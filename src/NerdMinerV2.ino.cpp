#include <Wire.h>
#include <hd44780.h>
#include <hd44780ioClass/hd44780_I2Cexp.h>

#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <esp_task_wdt.h>
#include <OneButton.h>
#include <string.h>

#include "mbedtls/md.h"
#include "wManager.h"
#include "mining.h"
#include "monitor.h"
#include "drivers/displays/display.h"
#include "drivers/storage/SDCard.h"
#include "ShaTests/nerdSHA_HWTest.h"
#include "timeconst.h"

#ifdef TOUCH_ENABLE
#include "TouchHandler.h"
#endif

#include <soc/soc_caps.h>

// ⚡ PROXIMITY SCREEN CUSTOM DEFINITIONS
#define IR_PIN 27
#define LCD_SDA 21
#define LCD_SCL 22

hd44780_I2Cexp lcd;
extern uint32_t elapsedKHs;
const int DETECTED_LEVEL = LOW;
bool lcdIsOn = false;
bool lcdReady = false;
unsigned long lastScreenRefresh = 0;
static char lastLcdLine0[17] = "";
static char lastLcdLine1[17] = "";

//3 seconds WDT
#define WDT_TIMEOUT 3
//15 minutes WDT for miner task
#define WDT_MINER_TIMEOUT 900

#ifdef PIN_BUTTON_1
  OneButton button1(PIN_BUTTON_1);
#endif

#ifdef PIN_BUTTON_2
  OneButton button2(PIN_BUTTON_2);
#endif

#ifdef TOUCH_ENABLE
extern TouchHandler touchHandler;
#endif

extern monitor_data mMonitor;

#ifdef SD_ID
  SDCard SDCrd = SDCard(SD_ID);
#else  
  SDCard SDCrd = SDCard();
#endif

/**********************⚡ GLOBAL Vars *******************************/

unsigned long start = millis();
const char* ntpServer = "pool.ntp.org";

/********* INIT *****/
void setup()
{
Serial.begin(115200);
delay(500);
Serial.println("MY CUSTOM NERDMINER BUILD 123");
  // Start serial before LCD initialization so errors can be reported.
#ifdef MONITOR_SPEED
  Serial.begin(MONITOR_SPEED);
#else
  Serial.begin(115200);
#endif
  Serial.setTimeout(0);
  Serial.printf("FX1 CPU frequency: %u MHz\n",
              getCpuFrequencyMhz());

  // Initialize the proximity sensor here. Initialize the external LCD later,
  // after NerdMiner's own display setup has run.
  pinMode(IR_PIN, INPUT);

  //Init pin 15 to enable 5V external power (LilyGo bug)
  #ifdef PIN_ENABLE5V
      pinMode(PIN_ENABLE5V, OUTPUT);
      digitalWrite(PIN_ENABLE5V, HIGH);
  #endif

  delay(SECOND_MS/10);

  esp_task_wdt_init(WDT_MINER_TIMEOUT, true);
  disableCore0WDT();

#ifdef HW_SHA256_TEST
  while (1) HwShaTest();
#endif

  // Setup the buttons
  #if defined(PIN_BUTTON_1) && !defined(PIN_BUTTON_2)
    button1.setPressMs(5*SECOND_MS);
    button1.attachClick(switchToNextScreen);
    button1.attachDoubleClick(alternateScreenRotation);
    button1.attachLongPressStart(reset_configuration);
    button1.attachMultiClick(alternateScreenState);
  #endif

  #if defined(PIN_BUTTON_1) && defined(PIN_BUTTON_2)
    button1.setPressMs(5*SECOND_MS);
    button1.attachClick(alternateScreenState);
    button1.attachDoubleClick(alternateScreenRotation);
  #endif

  #if defined(PIN_BUTTON_2)
    button2.setPressMs(5*SECOND_MS);
    button2.attachClick(switchToNextScreen);
    button2.attachLongPressStart(reset_configuration);
  #endif

  Serial.println("NerdMiner v2 starting......");

  initDisplay();
  Serial.println("CHECKPOINT 1");
  drawLoadingScreen();
  delay(2*SECOND_MS);
  Serial.println("CHECKPOINT 2 - starting external LCD");

  
  // Initialize the external LCD after NerdMiner's native display.
  Serial.println("Starting external I2C LCD...");

  Wire.begin(LCD_SDA, LCD_SCL);
  Wire.setClock(100000);

  int lcdStatus = lcd.begin(16, 2);
  Serial.println("CHECKPOINT 3 - calling lcd.begin");

  Serial.print("LCD begin status: ");
  Serial.println(lcdStatus);


  if (lcdStatus == 0) {
    lcdReady = true;
    lcd.clear();
    lcd.noBacklight();
    lcdIsOn = false;

    Serial.println("External I2C LCD initialized.");
  } else {
    lcdReady = false;
    Serial.println("External LCD initialization failed.");
  }


  mMonitor.NerdStatus = NM_waitingConfig;
  doLedStuff(0);

#ifdef SDMMC_1BIT_FIX
  SDCrd.initSDcard();
#endif

  init_WifiManager();

  Serial.println("");
  Serial.println("Initiating tasks...");
  static const char monitor_name[] = "(Monitor)";
  #if defined(CONFIG_IDF_TARGET_ESP32)
  BaseType_t res1 = xTaskCreatePinnedToCore(runMonitor, "Monitor", 9500, (void*)monitor_name, 5, NULL,1);
  #else
  BaseType_t res1 = xTaskCreatePinnedToCore(runMonitor, "Monitor", 10000, (void*)monitor_name, 5, NULL,1);
  #endif

  static const char stratum_name[] = "(Stratum)";
 #if defined(CONFIG_IDF_TARGET_ESP32) && !defined(ESP32_2432S028R) && !defined(ESP32_2432S028_2USB)
  BaseType_t res2 = xTaskCreatePinnedToCore(runStratumWorker, "Stratum", 12000, (void*)stratum_name, 4, NULL,1);
 #elif defined(ESP32_2432S028R) || defined(ESP32_2432S028_2USB)
  BaseType_t res2 = xTaskCreatePinnedToCore(runStratumWorker, "Stratum", 13500, (void*)stratum_name, 4, NULL,1);
 #else
  BaseType_t res2 = xTaskCreatePinnedToCore(runStratumWorker, "Stratum", 15000, (void*)stratum_name, 4, NULL,1);
 #endif

  TaskHandle_t minerTask1, minerTask2 = NULL;
  #ifdef HARDWARE_SHA265
    #if defined(CONFIG_IDF_TARGET_ESP32)
    xTaskCreate(minerWorkerHw, "MinerHw-0", 3584, (void*)0, 3, &minerTask1);
    #else
    xTaskCreate(minerWorkerHw, "MinerHw-0", 4096, (void*)0, 3, &minerTask1);
    #endif
  #else
    #if defined(CONFIG_IDF_TARGET_ESP32)
    xTaskCreate(minerWorkerSw, "MinerSw-0", 5000, (void*)0, 1, &minerTask1);
    #else
    xTaskCreate(minerWorkerSw, "MinerSw-0", 6000, (void*)0, 1, &minerTask1);
    #endif
  #endif
  esp_task_wdt_add(minerTask1);

#if (SOC_CPU_CORES_NUM >= 2)
  #if defined(CONFIG_IDF_TARGET_ESP32)
  xTaskCreate(minerWorkerSw, "MinerSw-1", 5000, (void*)1, 1, &minerTask2);
  #else
  xTaskCreate(minerWorkerSw, "MinerSw-1", 6000, (void*)1, 1, &minerTask2);
  #endif
  esp_task_wdt_add(minerTask2);
#endif

  vTaskPrioritySet(NULL, 4);
  setup_monitor();
}

void app_error_fault_handler(void *arg) {
  char *stack = (char *)arg;
  esp_log_write(ESP_LOG_ERROR, "APP_ERROR", "Error Stack Code:\n%s", stack);
  esp_restart();
}

void loop() {
  #ifdef PIN_BUTTON_1
    button1.tick();
  #endif

  #ifdef PIN_BUTTON_2
    button2.tick();
  #endif

#ifdef TOUCH_ENABLE
  touchHandler.isTouched();
#endif
  wifiManagerProcess();

  // Proximity LCD runtime. Do not use the LCD if setup failed.
  bool detected = (digitalRead(IR_PIN) == DETECTED_LEVEL);

  if (lcdReady && detected) {
    if (!lcdIsOn) {
      lcd.backlight();
      lcd.clear();
      lcdIsOn = true;
    }

    if (millis() - lastScreenRefresh >= 1000) {
      lastScreenRefresh = millis();
	lcd.setCursor(0, 0);

	if (offlineBenchmarkMode) {
	  lcd.print("OFFLINE TEST    ");
	} else {
	  lcd.print("SOLO LOTTERY BTC");
	}

	uint32_t displayRate = offlineBenchmarkMode ? offlineKHs : elapsedKHs;

	lcd.setCursor(0, 1);
	char rateLine[17];
	snprintf(rateLine, sizeof(rateLine), "Speed: %lu KH/s",
	         (unsigned long)displayRate);
	lcd.print("                ");
	lcd.setCursor(0, 1);
	lcd.print(rateLine);
    }
  } else if (lcdReady) {
    if (lcdIsOn) {
      lcd.clear();
      lcd.noBacklight();
      lcdIsOn = false;
    }
  }

  vTaskDelay(50 / portTICK_PERIOD_MS);
}
