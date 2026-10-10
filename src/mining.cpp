#include <Arduino.h>
#include <ArduinoJson.h>
#include <WiFi.h>
#include <esp_task_wdt.h>
#include <nvs_flash.h>
#include <nvs.h>
#include "ShaTests/nerdSHA256plus.h"
#include "stratum.h"
#include "mining.h"
#include "utils.h"
#include "monitor.h"
#include "timeconst.h"
#include "drivers/displays/display.h"
#include "drivers/storage/storage.h"
#include <mutex>
#include <list>
#include <map>
#include "mbedtls/sha256.h"
#include "i2c_master.h"
#include <string.h>

#define NONCE_PER_JOB_SW 4096
#define NONCE_PER_JOB_HW 16*1024
#define RANDOM_NONCE_MASK 0xFFFFC000

#ifdef HARDWARE_SHA265
#include <sha/sha_dma.h>
#include <hal/sha_hal.h>
#include <hal/sha_ll.h>
#if defined(CONFIG_IDF_TARGET_ESP32)
#include <sha/sha_parallel_engine.h>
#endif
#endif

nvs_handle_t stat_handle;
uint32_t templates = 0;
uint32_t hashes = 0;
uint32_t Mhashes = 0;
uint32_t totalKHashes = 0;
uint32_t elapsedKHs = 0;
volatile bool offlineBenchmarkMode = false;
volatile uint32_t offlineKHs = 0;

static uint64_t offlineTotalHashes = 0;
static uint64_t offlineLastRateCount = 0;
static unsigned long offlineLastRateTime = 0;
static uint32_t offlineNonce = 0;

static void offlineBenchmarkStep() {
    uint8_t header[80] = {0};
    uint8_t firstHash[32];
    uint8_t finalHash[32];

    // Deterministic local test header; never submitted to a pool.
    header[0] = 2;

    for (int i = 0; i < 64; ++i) {
        uint32_t nonce = offlineNonce++;
        header[76] = nonce & 0xff;
        header[77] = (nonce >> 8) & 0xff;
        header[78] = (nonce >> 16) & 0xff;
        header[79] = (nonce >> 24) & 0xff;

        if (mbedtls_sha256_ret(header, sizeof(header), firstHash, 0) == 0 &&
            mbedtls_sha256_ret(firstHash, sizeof(firstHash), finalHash, 0) == 0) {
            ++offlineTotalHashes;
        }
    }

    unsigned long now = millis();
    if (offlineLastRateTime == 0) {
        offlineLastRateTime = now;
        offlineLastRateCount = offlineTotalHashes;
    } else if (now - offlineLastRateTime >= 1000) {
        uint64_t elapsed = now - offlineLastRateTime;
        uint64_t count = offlineTotalHashes - offlineLastRateCount;
        offlineKHs = elapsed ? (uint32_t)(count / elapsed) : 0;
        offlineLastRateTime = now;
        offlineLastRateCount = offlineTotalHashes;
    }
}

uint64_t upTime = 0;
volatile uint32_t shares; 
volatile uint32_t valids; 
double best_diff = 0.0;

extern TSettings Settings;
IPAddress serverIP(1, 1, 1, 1);
static WiFiClient client;
static miner_data mMiner; 
mining_subscribe mWorker;
mining_job mJob;
monitor_data mMonitor;
static bool volatile isMinerSuscribed = false;
unsigned long mLastTXtoPool = millis();

int saveIntervals[] = {5 * 60, 15 * 60, 30 * 60, 1 * 3600, 3 * 3600, 6 * 3600, 12 * 3600};
int saveIntervalsSize = sizeof(saveIntervals)/sizeof(saveIntervals[0]);
int currentIntervalIndex = 0;

// Tracker for the Python serial UI timeline injection
unsigned long lastGuiStreamTime = 0;
// JankMiner FX1: avoid rewriting unchanged LCD text.
static char lastLcdLine0[17] = "";
static char lastLcdLine1[17] = "";

bool checkPoolConnection(void) {
  if (client.connected()) return true;
  isMinerSuscribed = false;
  Serial.println("Client not connected, trying to connect..."); 
  if(serverIP == IPAddress(1,1,1,1)) {
    WiFi.hostByName(Settings.PoolAddress.c_str(), serverIP);
    Serial.printf("Resolved DNS and save ip (first time) got: %s\n", serverIP.toString());
  }
  if (!client.connect(serverIP, Settings.PoolPort)) {
    Serial.println("Imposible to connect to : " + Settings.PoolAddress);
    WiFi.hostByName(Settings.PoolAddress.c_str(), serverIP);
    Serial.printf("Resolved DNS got: %s\n", serverIP.toString());
    return false;
  }
  return true;
}

unsigned long mStart0Hashrate = 0;
bool checkPoolInactivity(unsigned int keepAliveTime, unsigned long inactivityTime){ 
    unsigned long currentKHashes = (Mhashes*1000) + hashes/1000;
    unsigned long elapsedKHs = currentKHashes - totalKHashes;
    uint32_t time_now = millis();
    if (time_now < mLastTXtoPool) mLastTXtoPool = time_now;
    if (time_now > mLastTXtoPool + keepAliveTime) {
      mLastTXtoPool = time_now;
      Serial.println("  Sending  : KeepAlive suggest_difficulty");
      tx_suggest_difficulty(client, DEFAULT_DIFFICULTY);
    }
    if(elapsedKHs == 0){
      if(mStart0Hashrate == 0) mStart0Hashrate  = time_now; 
      if((time_now-mStart0Hashrate) > inactivityTime) { mStart0Hashrate=0; return true;}
      return false;
    }
  mStart0Hashrate = 0;
  return false;
}

struct JobRequest {
  uint32_t id;
  uint32_t nonce_start;
  uint32_t nonce_count;
  double difficulty;
  uint8_t sha_buffer[128];
  uint32_t midstate[8];
  uint32_t bake[16];
};

struct JobResult {
  uint32_t id;
  uint32_t nonce;
  uint32_t nonce_count;
  double difficulty;
  uint8_t hash[32];
};

static std::mutex s_job_mutex;
std::list<std::shared_ptr<JobRequest>> s_job_request_list_sw;
#ifdef HARDWARE_SHA265
std::list<std::shared_ptr<JobRequest>> s_job_request_list_hw;
#endif
std::list<std::shared_ptr<JobResult>> s_job_result_list;
static volatile uint8_t s_working_current_job_id = 0xFF;

static void JobPush(std::list<std::shared_ptr<JobRequest>> &job_list, uint32_t id, uint32_t nonce_start, uint32_t nonce_count, double difficulty,
                    const uint8_t* sha_buffer, const uint32_t* midstate, const uint32_t* bake) {
  std::shared_ptr<JobRequest> job = std::make_shared<JobRequest>();
  job->id = id;
  job->nonce_start = nonce_start;
  job->nonce_count = nonce_count;
  job->difficulty = difficulty;
  memcpy(job->sha_buffer, sha_buffer, sizeof(job->sha_buffer));
  memcpy(job->midstate, midstate, sizeof(job->midstate));
  memcpy(job->bake, bake, sizeof(job->bake));
  job_list.push_back(job);
}

struct Submition {
  double diff;
  bool is32bit;
  bool isValid;
};

static void MiningJobStop(uint32_t &job_pool, std::map<uint32_t, std::shared_ptr<Submition>> & submition_map) {
  {
    std::lock_guard<std::mutex> lock(s_job_mutex);
    s_job_result_list.clear();
    s_job_request_list_sw.clear();
    #ifdef HARDWARE_SHA265
    s_job_request_list_hw.clear();
    #endif
  }
  s_working_current_job_id = 0xFF;
  job_pool = 0xFFFFFFFF;
  submition_map.clear();
}

void runStratumWorker(void *name) {
  Serial.println("");
  Serial.printf("\n[WORKER] Started. Running %s on core %d\n", (char *)name, xPortGetCoreID());

  std::map<uint32_t, std::shared_ptr<Submition>> s_submition_map;

#ifdef I2C_SLAVE
  std::vector<uint8_t> i2c_slave_vector;
  if (i2c_master_start() == 0) i2c_slave_vector = i2c_master_scan(0x0, 0x80);
#endif

  double currentPoolDifficulty = DEFAULT_DIFFICULTY;
  uint32_t nonce_pool = 0;
  uint32_t job_pool = 0xFFFFFFFF;
  uint32_t last_job_time = millis();
  static unsigned long lastOfflineWifiRetry = 0;

  while(true) {

    if(WiFi.status() != WL_CONNECTED){
      mMonitor.NerdStatus = NM_Connecting;
      offlineBenchmarkMode = true;
      MiningJobStop(job_pool, s_submition_map);

      if (millis() - lastOfflineWifiRetry >= 5000) {
        WiFi.reconnect();
        lastOfflineWifiRetry = millis();
      }

      offlineBenchmarkStep();
      vTaskDelay(1 / portTICK_PERIOD_MS);
      continue;
    } 

    if(!checkPoolConnection()){
      offlineBenchmarkMode = true;
      MiningJobStop(job_pool, s_submition_map);
      offlineBenchmarkStep();
      vTaskDelay(10 / portTICK_PERIOD_MS);
      continue;
    }

    offlineBenchmarkMode = false;
    offlineKHs = 0;

    if(!isMinerSuscribed) {
      mWorker = init_mining_subscribe();
      if(!tx_mining_subscribe(client, mWorker)) { 
        client.stop();
        MiningJobStop(job_pool, s_submition_map);
        continue; 
      }
      strcpy(mWorker.wName, Settings.BtcWallet);
      strcpy(mWorker.wPass, Settings.PoolPassword);
      tx_mining_auth(client, mWorker.wName, mWorker.wPass);
      tx_suggest_difficulty(client, currentPoolDifficulty);
      isMinerSuscribed=true;
      uint32_t time_now = millis();
      mLastTXtoPool = time_now;
      last_job_time = time_now;
    }

    if(checkPoolInactivity(KEEPALIVE_TIME_ms, POOLINACTIVITY_TIME_ms)){
      client.stop();
      isMinerSuscribed=false;
      MiningJobStop(job_pool, s_submition_map);
      continue; 
    }

    {
      uint32_t time_now = millis();
      if (time_now < last_job_time) last_job_time = time_now;
      if (time_now >= last_job_time + 10*60*1000) {
        client.stop();
        isMinerSuscribed=false;
        MiningJobStop(job_pool, s_submition_map);
        continue;
      }
    }

    uint32_t hw_midstate[8];
    uint32_t diget_mid[8];
    uint32_t bake[16];
    #if defined(CONFIG_IDF_TARGET_ESP32)
    uint8_t sha_buffer_swap[128];
    #endif

    while(client.connected() && client.available()) {
      String line = client.readStringUntil('\n');
      stratum_method result = parse_mining_method(line);
      switch (result) {
          case MINING_NOTIFY: if(parse_mining_notify(line, mJob)) {
                                          {
                                            std::lock_guard<std::mutex> lock(s_job_mutex);
                                            s_job_request_list_sw.clear();
                                            #ifdef HARDWARE_SHA265
                                            s_job_request_list_hw.clear();
                                            #endif
                                          }
                                          templates++;
                                          job_pool++;
                                          s_working_current_job_id = job_pool & 0xFF;
                                          last_job_time = millis();
                                          mLastTXtoPool = last_job_time;

                                          uint32_t mh = hashes/1000000;
                                          Mhashes += mh;
                                          hashes -= mh*1000000;

                                          mMiner=calculateMiningData(mWorker, mJob);
                                          memset(mMiner.bytearray_blockheader+80, 0, 128-80);
                                          mMiner.bytearray_blockheader[80] = 0x80;
                                          mMiner.bytearray_blockheader[126] = 0x02;
                                          mMiner.bytearray_blockheader[127] = 0x80;

                                          nerd_mids(diget_mid, mMiner.bytearray_blockheader);
                                          nerd_sha256_bake(diget_mid, mMiner.bytearray_blockheader+64, bake);

                                          #ifdef HARDWARE_SHA265
                                          #if defined(CONFIG_IDF_TARGET_ESP32S2) || defined(CONFIG_IDF_TARGET_ESP32S3) || defined(CONFIG_IDF_TARGET_ESP32C3)
                                            esp_sha_acquire_hardware();
                                            sha_hal_hash_block(SHA2_256, mMiner.bytearray_blockheader, 64/4, true);
                                            sha_hal_read_digest(SHA2_256, hw_midstate);
                                            esp_sha_release_hardware();
                                          #endif
                                          #endif

                                          #if defined(CONFIG_IDF_TARGET_ESP32)
                                          for (int i = 0; i < 32; ++i)
                                            ((uint32_t*)sha_buffer_swap)[i] = __builtin_bswap32(((const uint32_t*)(mMiner.bytearray_blockheader))[i]);
                                          #endif

                                          nonce_pool = 0xDA54E700; 

                                          {
                                            std::lock_guard<std::mutex> lock(s_job_mutex);
                                            for (int i = 0; i < 4; ++ i) {
                                              JobPush(s_job_request_list_sw, job_pool, nonce_pool, NONCE_PER_JOB_SW, currentPoolDifficulty, mMiner.bytearray_blockheader, diget_mid, bake);
                                              nonce_pool += NONCE_PER_JOB_SW;
                                              #ifdef HARDWARE_SHA265
                                                #if defined(CONFIG_IDF_TARGET_ESP32)
                                                  JobPush(s_job_request_list_hw, job_pool, nonce_pool, NONCE_PER_JOB_HW, currentPoolDifficulty, sha_buffer_swap, hw_midstate, bake);
                                                #else
                                                  JobPush(s_job_request_list_hw, job_pool, nonce_pool, NONCE_PER_JOB_HW, currentPoolDifficulty, mMiner.bytearray_blockheader, hw_midstate, bake);
                                                #endif
                                                nonce_pool += NONCE_PER_JOB_HW;
                                              #endif
                                            }
                                          }
                                      } else {
                                        client.stop();
                                        isMinerSuscribed=false;
                                        MiningJobStop(job_pool, s_submition_map);
                                      }
                                      break;
          case MINING_SET_DIFFICULTY: parse_mining_set_difficulty(line, currentPoolDifficulty);
                                      break;
          case STRATUM_SUCCESS: {
                                        unsigned long id = parse_extract_id(line);
                                        auto itt = s_submition_map.find(id);
                                        if (itt != s_submition_map.end()) {
                                          if (itt->second->diff > best_diff) best_diff = itt->second->diff;
                                          if (itt->second->is32bit) shares++;
                                          if (itt->second->isValid) valids++;
                                          s_submition_map.erase(itt);
                                        }
                                      }
                                      break;
          case STRATUM_PARSE_ERROR: {
                                        unsigned long id = parse_extract_id(line);
                                        auto itt = s_submition_map.find(id);
                                        if (itt != s_submition_map.end()) s_submition_map.erase(itt);
                                      }
                                      break;
          default:                    break;
      }
    }

    std::list<std::shared_ptr<JobResult>> job_result_list;
    vTaskDelay(50 / portTICK_PERIOD_MS); 
    
    if (job_pool != 0xFFFFFFFF) {
      std::lock_guard<std::mutex> lock(s_job_mutex);
      job_result_list.insert(job_result_list.end(), s_job_result_list.begin(), s_job_result_list.end());
      s_job_result_list.clear();

      while (s_job_request_list_sw.size() < 4) {
        JobPush(s_job_request_list_sw, job_pool, nonce_pool, NONCE_PER_JOB_SW, currentPoolDifficulty, mMiner.bytearray_blockheader, diget_mid, bake);
        nonce_pool += NONCE_PER_JOB_SW;
      }

      #ifdef HARDWARE_SHA265
      while (s_job_request_list_hw.size() < 4) {
        #if defined(CONFIG_IDF_TARGET_ESP32)
          JobPush(s_job_request_list_hw, job_pool, nonce_pool, NONCE_PER_JOB_HW, currentPoolDifficulty, sha_buffer_swap, hw_midstate, bake);
        #else
          JobPush(s_job_request_list_hw, job_pool, nonce_pool, NONCE_PER_JOB_HW, currentPoolDifficulty, mMiner.bytearray_blockheader, hw_midstate, bake);
        #endif
        nonce_pool += NONCE_PER_JOB_HW;
      }
      #endif
    }

    while (!job_result_list.empty()) {
      std::shared_ptr<JobResult> res = job_result_list.front();
      job_result_list.pop_front();
      hashes += res->nonce_count;
      if (res->difficulty > currentPoolDifficulty && job_pool == res->id && res->nonce != 0xFFFFFFFF) {
        if (!client.connected()) break;
        unsigned long sumbit_id = 0;
        tx_mining_submit(client, mWorker, mJob, res->nonce, sumbit_id);
        mLastTXtoPool = millis();

        std::shared_ptr<Submition> submition = std::make_shared<Submition>();
        submition->diff = res->difficulty;
        submition->is32bit = (res->hash[29] == 0 && res->hash[28] == 0);
        submition->isValid = submition->is32bit ? checkValid(res->hash, mMiner.bytearray_target) : false;
        s_submition_map.insert(std::make_pair(sumbit_id, submition));
      }
    }
  }
}

void minerWorkerSw(void * task_id) {
  unsigned int miner_id = (uint32_t)task_id;
  std::shared_ptr<JobRequest> job;
  std::shared_ptr<JobResult> result;
  uint8_t hash[32];
  uint32_t wdt_counter = 0;
  while (1) {
    {
      std::lock_guard<std::mutex> lock(s_job_mutex);
      if (result) {
        if (s_job_result_list.size() < 16) s_job_result_list.push_back(result);
        result.reset();
      }
      if (!s_job_request_list_sw.empty()) {
        job = s_job_request_list_sw.front();
        s_job_request_list_sw.pop_front();
      } else job.reset();
    }
    if (job) {
      result = std::make_shared<JobResult>();
      result->difficulty = job->difficulty;
      result->nonce = 0xFFFFFFFF;
      result->id = job->id;
      result->nonce_count = job->nonce_count;
      uint8_t job_in_work = job->id & 0xFF;
      for (uint32_t n = 0; n < job->nonce_count; ++n) {
        ((uint32_t*)(job->sha_buffer+64+12))[0] = job->nonce_start+n;
        if (nerd_sha256d_baked(job->midstate, job->sha_buffer+64, job->bake, hash)) {
          double diff_hash = diff_from_target(hash);
          if (diff_hash > result->difficulty) {
            result->difficulty = diff_hash;
            result->nonce = job->nonce_start+n;
            memcpy(result->hash, hash, 32);
          }
        }
        if ((uint16_t)(n & 0xFF) == 0 && s_working_current_job_id != job_in_work) {
          result->nonce_count = n+1;
          break;
        }
      }
    } else vTaskDelay(2 / portTICK_PERIOD_MS);

    wdt_counter++;
    if (wdt_counter >= 8) { wdt_counter = 0; esp_task_wdt_reset(); }
  }
}

#ifdef HARDWARE_SHA265
#if defined(CONFIG_IDF_TARGET_ESP32)

static inline bool nerd_sha_ll_read_digest_swap_if(void* ptr) {
  DPORT_INTERRUPT_DISABLE();
  uint32_t fin = DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 7 * 4);
  if ((uint32_t)(fin & 0xFFFF) != 0) { DPORT_INTERRUPT_RESTORE(); return false; }
  ((uint32_t*)ptr)[7] = __builtin_bswap32(fin);
  ((uint32_t*)ptr)[0] = __builtin_bswap32(DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 0 * 4));
  ((uint32_t*)ptr)[1] = __builtin_bswap32(DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 1 * 4));
  ((uint32_t*)ptr)[2] = __builtin_bswap32(DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 2 * 4));
  ((uint32_t*)ptr)[3] = __builtin_bswap32(DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 3 * 4));
  ((uint32_t*)ptr)[4] = __builtin_bswap32(DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 4 * 4));
  ((uint32_t*)ptr)[5] = __builtin_bswap32(DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 5 * 4));
  ((uint32_t*)ptr)[6] = __builtin_bswap32(DPORT_SEQUENCE_REG_READ(SHA_TEXT_BASE + 6 * 4));
  DPORT_INTERRUPT_RESTORE();
  return true;
}

static inline void nerd_sha_hal_wait_idle() { while (DPORT_REG_READ(SHA_256_BUSY_REG)) {} }

static inline void nerd_sha_ll_fill_text_block_sha256(const void *input_text) {
    uint32_t *data_words = (uint32_t *)input_text;
    uint32_t *reg_addr_buf = (uint32_t *)(SHA_TEXT_BASE);
    for(int i=0; i<16; i++) reg_addr_buf[i] = data_words[i];
}

static inline void nerd_sha_ll_fill_text_block_sha256_upper(const void *input_text, uint32_t nonce) {
    uint32_t *data_words = (uint32_t *)input_text;
    uint32_t *reg_addr_buf = (uint32_t *)(SHA_TEXT_BASE);
    reg_addr_buf[0] = data_words[0];
    reg_addr_buf[1] = data_words[1];
    reg_addr_buf[2] = data_words[2];
    reg_addr_buf[3] = __builtin_bswap32(nonce);
    reg_addr_buf[4] = 0x80000000;
    for(int i=5; i<15; i++) reg_addr_buf[i] = 0x00000000;
    reg_addr_buf[15] = 0x00000280;
}

static inline void nerd_sha_ll_fill_text_block_sha256_double() {
    uint32_t *reg_addr_buf = (uint32_t *)(SHA_TEXT_BASE);
    reg_addr_buf[8] = 0x80000000;
    for(int i=9; i<15; i++) reg_addr_buf[i] = 0x00000000;
    reg_addr_buf[15] = 0x00000100;
}

void minerWorkerHw(void * task_id) {
  unsigned int miner_id = (uint32_t)task_id;
  std::shared_ptr<JobRequest> job;
  std::shared_ptr<JobResult> result;
  uint8_t hash[32];
  uint8_t sha_buffer[128];
  while (1) {
    {
      std::lock_guard<std::mutex> lock(s_job_mutex);
      if (result) {
        if (s_job_result_list.size() < 16) s_job_result_list.push_back(result);
        result.reset();
      }
      if (!s_job_request_list_hw.empty()) {
        job = s_job_request_list_hw.front();
        s_job_request_list_hw.pop_front();
      } else job.reset();
    }
    if (job) {
      result = std::make_shared<JobResult>();
      result->id = job->id; result->nonce = 0xFFFFFFFF;
      result->nonce_count = job->nonce_count; result->difficulty = job->difficulty;
      uint8_t job_in_work = job->id & 0xFF;
      memcpy(sha_buffer, job->sha_buffer, 80);

      esp_sha_lock_engine(SHA2_256);
      for (uint32_t n = 0; n < job->nonce_count; ++n) {
        nerd_sha_ll_fill_text_block_sha256(sha_buffer);
        sha_ll_start_block(SHA2_256);
        nerd_sha_hal_wait_idle();
        nerd_sha_ll_fill_text_block_sha256_upper(sha_buffer+64, job->nonce_start+n);
        sha_ll_continue_block(SHA2_256);
        nerd_sha_hal_wait_idle();
        sha_ll_load(SHA2_256);
        nerd_sha_hal_wait_idle();
		nerd_sha_ll_fill_text_block_sha256_double();
		sha_ll_start_block(SHA2_256);
		nerd_sha_hal_wait_idle();
		sha_ll_load(SHA2_256);
		nerd_sha_hal_wait_idle();  // Wait for the final digest to be ready.
		if (nerd_sha_ll_read_digest_swap_if(hash)) {
          double diff_hash = diff_from_target(hash);
          if (diff_hash > result->difficulty) {
            if (isSha256Valid(hash)) {
              result->difficulty = diff_hash;
              result->nonce = job->nonce_start+n;
              memcpy(result->hash, hash, sizeof(hash));
            }
          }
        }
        if ((uint8_t)(n & 0xFF) == 0 && s_working_current_job_id != job_in_work) {
          result->nonce_count = n+1;
          break;
        }
      }
      esp_sha_unlock_engine(SHA2_256);
    } else vTaskDelay(2 / portTICK_PERIOD_MS);
    esp_task_wdt_reset();
  }
}
#endif
#endif

void restoreStat() {
  if(!Settings.saveStats) return;
  esp_err_t ret = nvs_flash_init();
  ret = nvs_open("state", NVS_READWRITE, &stat_handle);
  size_t required_size = sizeof(double);
  nvs_get_blob(stat_handle, "best_diff", &best_diff, &required_size);
  nvs_get_u32(stat_handle, "Mhashes", &Mhashes);
  uint32_t nv_shares, nv_valids;
  nvs_get_u32(stat_handle, "shares", &nv_shares);
  nvs_get_u32(stat_handle, "valids", &nv_valids);
  shares = nv_shares; valids = nv_valids;
  nvs_get_u32(stat_handle, "templates", &templates);
  nvs_get_u64(stat_handle, "upTime", &upTime);
}

void saveStat() {
  if(!Settings.saveStats) return;
  nvs_set_blob(stat_handle, "best_diff", &best_diff, sizeof(best_diff));
  nvs_set_u32(stat_handle, "Mhashes", Mhashes);
  nvs_set_u32(stat_handle, "shares", shares);
  nvs_set_u32(stat_handle, "valids", valids);
  nvs_set_u32(stat_handle, "templates", templates);
  nvs_set_u64(stat_handle, "upTime", upTime);
}


void resetStat() {
  best_diff = 0.0;
  Mhashes = 0;
  hashes = 0;
  totalKHashes = 0;
  elapsedKHs = 0;
  shares = 0;
  valids = 0;
  templates = 0;
  upTime = 0;

  if (Settings.saveStats) {
    nvs_set_blob(stat_handle, "best_diff", &best_diff, sizeof(best_diff));
    nvs_set_u32(stat_handle, "Mhashes", Mhashes);
    nvs_set_u32(stat_handle, "shares", shares);
    nvs_set_u32(stat_handle, "valids", valids);
    nvs_set_u32(stat_handle, "templates", templates);
    nvs_set_u64(stat_handle, "upTime", upTime);
    nvs_commit(stat_handle);
  }
}

void runMonitor(void *name) {
  restoreStat();
  unsigned long mLastCheck = 0;
  resetToFirstScreen();
  unsigned long frame = 0;
  totalKHashes = (Mhashes * 1000) + hashes / 1000;
  uint32_t last_update_millis = millis();
  uint32_t uptime_frac = 0;
  while (1) {
    uint32_t now_millis = millis();
    if (now_millis < last_update_millis) now_millis = last_update_millis;
    uint32_t mElapsed = now_millis - mLastCheck;
    if (mElapsed >= 1000) { 
      mLastCheck = now_millis;
      last_update_millis = now_millis;
      unsigned long currentKHashes = (Mhashes * 1000) + hashes / 1000;
      elapsedKHs = currentKHashes - totalKHashes;
      totalKHashes = currentKHashes;
      uptime_frac += mElapsed;
      while (uptime_frac >= 1000) { uptime_frac -= 1000; upTime ++; }
      drawCurrentScreen(mElapsed);
    }
    animateCurrentScreen(frame);
    doLedStuff(frame);
    vTaskDelay(50 / portTICK_PERIOD_MS);
    frame++;
  }
}
