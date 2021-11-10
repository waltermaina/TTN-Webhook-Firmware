/**
   @file RAK1906_RAK4630_LoRaWAN.ino
   @author waltermaina76@gmail.com
   @brief LoRaWan node with:
      1. OTAA/ABP registration
      2. Reading of RAK1906 environment sensor data
      3. Sending the temperature, humidity, air pressure and air quality data to TTN
      4. Data is stored in a queue for sending later if the device is offline (gateway is off)
      5. It is meant for use with the webook: https://environmentsensors.herokuapp.com/api/v1
   @version 1.0.0
   @date 2021-11-10

   @copyright Copyright (c) 2021

   @note RAK4631 GPIO mapping to nRF52840 GPIO ports
   RAK4631    <->  nRF52840
   WB_IO1     <->  P0.17 (GPIO 17)
   WB_IO2     <->  P1.02 (GPIO 34)
   WB_IO3     <->  P0.21 (GPIO 21)
   WB_IO4     <->  P0.04 (GPIO 4)
   WB_IO5     <->  P0.09 (GPIO 9)
   WB_IO6     <->  P0.10 (GPIO 10)
   WB_SW1     <->  P0.01 (GPIO 1)
   WB_A0      <->  P0.04/AIN2 (AnalogIn A2)
   WB_A1      <->  P0.31/AIN7 (AnalogIn A7)
*/

#include <Arduino.h>
#include <LoRaWan-RAK4630.h> //http://librarymanager/All#SX126x
#include <SPI.h>
#include <Wire.h>
#include <Adafruit_Sensor.h>
#include <Adafruit_BME680.h> // Click to install library: http://librarymanager/All#Adafruit_BME680
#include <PString.h>
#include <MD_CirQueue.h>

// RAK4630 supply two LED
#ifndef LED_BUILTIN
#define LED_BUILTIN 35
#endif

#ifndef LED_BUILTIN2
#define LED_BUILTIN2 36
#endif

bool doOTAA = true;   // OTAA is used by default.
#define SCHED_MAX_EVENT_DATA_SIZE APP_TIMER_SCHED_EVENT_DATA_SIZE /**< Maximum size of scheduler events. */
#define SCHED_QUEUE_SIZE 60										  /**< Maximum number of events in the scheduler queue. */
#define LORAWAN_DATERATE DR_0									  /*LoRaMac datarates definition, from DR_0 to DR_5*/
#define LORAWAN_TX_POWER TX_POWER_5							/*LoRaMac tx power definition, from TX_POWER_0 to TX_POWER_15*/
#define JOINREQ_NBTRIALS 3										  /**< Number of trials for the join request. */
DeviceClass_t g_CurrentClass = CLASS_A;					/* class definition*/
LoRaMacRegion_t g_CurrentRegion = LORAMAC_REGION_EU868;    /* Region:EU868*/
lmh_confirm g_CurrentConfirm = LMH_CONFIRMED_MSG;				  /* confirm/unconfirm packet definition*/
uint8_t gAppPort = LORAWAN_APP_PORT;							        /* data port*/

/**@brief Structure containing LoRaWan parameters, needed for lmh_init()
*/
static lmh_param_t g_lora_param_init = {LORAWAN_ADR_ON, LORAWAN_DATERATE, LORAWAN_PUBLIC_NETWORK, JOINREQ_NBTRIALS, LORAWAN_TX_POWER, LORAWAN_DUTYCYCLE_OFF};

// Foward declaration
static void lorawan_has_joined_handler(void);
static void lorawan_join_failed_handler(void);
static void lorawan_rx_handler(lmh_app_data_t *app_data);
static void lorawan_confirm_class_handler(DeviceClass_t Class);
static void send_lora_frame(void);
static void sensor_read_periodic_handler(void);

/**@brief Structure containing LoRaWan callback functions, needed for lmh_init()
*/
static lmh_callback_t g_lora_callbacks = {BoardGetBatteryLevel, BoardGetUniqueId, BoardGetRandomSeed,
                                          lorawan_rx_handler, lorawan_has_joined_handler, lorawan_confirm_class_handler, lorawan_join_failed_handler
                                         };
//OTAA keys !!!! KEYS ARE MSB !!!!
uint8_t nodeDeviceEUI[8] = {0x70, 0xB3, 0xD5, 0x7E, 0xD0, 0x04, 0x66, 0xE5};
uint8_t nodeAppEUI[8] = {0xB8, 0x27, 0xEB, 0xFF, 0xFE, 0x39, 0x00, 0x00};
uint8_t nodeAppKey[16] = {0xD0, 0xE5, 0x8C, 0x2E, 0xD5, 0x37, 0xE8, 0xFD, 0x7B, 0x1F, 0x21, 0x2C, 0xDE, 0xA5, 0xC3, 0x48};

// ABP keys
uint32_t nodeDevAddr = 0x260116F8;
uint8_t nodeNwsKey[16] = {0x7E, 0xAC, 0xE2, 0x55, 0xB8, 0xA5, 0xE2, 0x69, 0x91, 0x51, 0x96, 0x06, 0x47, 0x56, 0x9D, 0x23};
uint8_t nodeAppsKey[16] = {0xFB, 0xAC, 0xB6, 0x47, 0xF3, 0x58, 0x45, 0xC7, 0x50, 0x7D, 0xBF, 0x16, 0x8B, 0xA8, 0xC1, 0x7C};

// Private defination
#define LORAWAN_APP_DATA_BUFF_SIZE 64                     /**< buffer size of the data to be transmitted. */
#define LORAWAN_APP_INTERVAL 20000                        /**< Defines for user timer, the application data transmission interval. 20s, value in [ms]. */
static uint8_t m_lora_app_data_buffer[LORAWAN_APP_DATA_BUFF_SIZE];            //< Lora user application data buffer.
static lmh_app_data_t m_lora_app_data = {m_lora_app_data_buffer, 0, 0, 0, 0}; //< Lora user application data structure.

TimerEvent_t appTimer;
TimerEvent_t sensorReadTimer;
static uint32_t timers_init(void);
static uint32_t count = 0;
static uint32_t count_fail = 0;

// Join retry variables
bool retJoinRetry = true; /* For checking if a join retry should be made */
unsigned long joinRetryTimepoint = 0;
#define JOIN_RETRY_INTERVAL 300000 // 5 Minutes
#define SEND_FAIL_COUNT 1 // 1 failure should trigger a join retry, as a way of checking if the gateway is still up
static uint32_t count_fail_copy = 0; /** Used to count the number of send fails */
bool mightBeOffline = false; /** Used to check if gateway is off */

// BME680 variables
Adafruit_BME680 bme;
// Might need adjustments
#define SEALEVELPRESSURE_HPA (1010.0)
#define SENSORS_BUFFER_SIZE 52                              /** Maximum size of sensors data buffer in bytes. */
static char pstring_buffer[SENSORS_BUFFER_SIZE];            /** Buffer to be used with PString. */
static PString str(pstring_buffer, sizeof(pstring_buffer)); /** PString string to hold DS18B20 data. */

// RAK1906 data queue variables
const uint8_t QUEUE_SIZE = 255; /** (255/24)= 10.625 days, 24 records per day */
struct
{
  unsigned long record_id = 0;
  unsigned long milliSec = 0;
  double temperature = 0.0;
  double pressure = 0.0;
  double humidity = 0.0;
  double gas_resistance = 0.0;
} pushdata, popdata, peekdata;   /** Data type of data stored every hour (40 bytes each) */

/** Define a queue that has 255 data items each with 320 bits and total is 10,200 bytes. */
MD_CirQueue Q(QUEUE_SIZE, sizeof(pushdata));
unsigned long recordId = 0; /** The record id */

// Sensor read and queue peek variables
unsigned long sensorReadTimepoint = 0;
//#define SENSOR_READ_INTERVAL LORAWAN_APP_INTERVAL * 2
#define SENSOR_READ_INTERVAL 3600000 // Every hour
#define PEEK_DATA_INTERVAL LORAWAN_APP_INTERVAL - 10000 /** Put data in buffer a few seconds befor sending */
unsigned long peekDataTimepoint = 0;

bool appDebugOn = true;    /** Used to decide if debug information can be printed */
//bool appDebugOn = false;

/**@brief Function for initializing BME680 sensor in RAK1906.
*/
void bme680_init()
{
  Wire.begin();

  if (!bme.begin(0x76)) {
    Serial.println("Could not find a valid BME680 sensor, check wiring!");
    return;
  }

  // Set up oversampling and filter initialization
  bme.setTemperatureOversampling(BME680_OS_8X);
  bme.setHumidityOversampling(BME680_OS_2X);
  bme.setPressureOversampling(BME680_OS_4X);
  bme.setIIRFilterSize(BME680_FILTER_SIZE_3);
  bme.setGasHeater(320, 150); // 320*C for 150 ms
}

/**@brief Function for reading the BME680 sensor and putting the
   data in a queue.
*/
void bme680_get(void)
{
  str.begin(); // reuse the PString, blocks sending of data during queue push

  // Calculate sensor values
  double temperature = bme.temperature;
  double pressure = bme.pressure / 100.0;
  double humidity = bme.humidity;
  double gas_resistance = bme.gas_resistance / 1000.0;

  if (appDebugOn == true) {
    Serial.print("Temperature = ");
    Serial.print(temperature);
    Serial.println(" *C");

    Serial.print("Pressure = ");
    Serial.print(pressure);
    Serial.println(" hPa");

    Serial.print("Humidity = ");
    Serial.print(humidity);
    Serial.println(" %");

    Serial.print("Gas = ");
    Serial.print(gas_resistance);
    Serial.println(" KOhms");

    Serial.println();
  }

  recordId = recordId + 1;
  pushdata.record_id = recordId;
  pushdata.milliSec = millis();
  pushdata.temperature = temperature;
  pushdata.pressure = pressure;
  pushdata.humidity = humidity;
  pushdata.gas_resistance = gas_resistance;
  bool b;
  b = Q.push((uint8_t *)&pushdata);

  if (appDebugOn == true) {
    Serial.print("\nPush ");
    Serial.print("Record ID = ");
    Serial.print(pushdata.record_id);
    Serial.print(" Temperature = ");
    Serial.print(pushdata.temperature);
    Serial.print(" Pressure = ");
    Serial.print(pushdata.pressure);
    Serial.print(" Humidity = ");
    Serial.print(pushdata.humidity);
    Serial.print(" Gas Resistance = ");
    Serial.print(pushdata.gas_resistance);
    Serial.print(" Uptime = ");
    Serial.print(pushdata.milliSec);
    Serial.println(b ? " ok" : " fail");
  }
}

/**@brief Function for putting data into the pstring_buffer
   so that it can be sent by the send_lora_frame() function.
*/
void peekData(void) {
  str.begin(); // reuse the PString, clear it incase the queue is empty too

  if (!Q.isEmpty()) {
    bool b = Q.peek((uint8_t *)&peekdata);

    // How long ago this data was recorded
    unsigned long milliSecAgo = millis() - peekdata.milliSec;

    if (appDebugOn == true) {
      Serial.print("\nPeek ");
      Serial.print("Record ID = ");
      Serial.print(peekdata.record_id);
      Serial.print(" Temperature = ");
      Serial.print(peekdata.temperature);
      Serial.print(" Pressure = ");
      Serial.print(peekdata.pressure);
      Serial.print(" Humidity = ");
      Serial.print(peekdata.humidity);
      Serial.print(" Gas Resistance = ");
      Serial.print(peekdata.gas_resistance);
      Serial.print(" Uptime = ");
      Serial.print(milliSecAgo);
      Serial.println(b ? " ok" : " fail");
    }

    // Put the data in a pstring

    // Add Record ID to pstring
    str.print(peekdata.record_id);
    str.print(",");

    // Add Time recorded to pstring
    str.print(milliSecAgo);
    str.print(",");

    // Add temperature to pstring
    str.print(peekdata.temperature);
    str.print(",");

    // Add pressure to pstring
    str.print(peekdata.pressure);
    str.print(",");

    // Add humidity to pstring
    str.print(peekdata.humidity);
    str.print(",");

    // Add gas to pstring
    str.print(peekdata.gas_resistance);

    // Print pstring data
    Serial.print("Peek Data Pstring = ");
    Serial.println(str);
  }
}

/**@brief Function for removing sent data from queue.
*/
void popData(void) {
  if (!Q.isEmpty()) {
    bool b = Q.pop((uint8_t *)&popdata);

    if (appDebugOn == true) {
      Serial.print("\nPop ");
      Serial.print("Record ID = ");
      Serial.print(popdata.record_id);
      Serial.print(" Temperature = ");
      Serial.print(popdata.temperature);
      Serial.print(" Pressure = ");
      Serial.print(popdata.pressure);
      Serial.print(" Humidity = ");
      Serial.print(popdata.humidity);
      Serial.print(" Gas Resistance = ");
      Serial.print(popdata.gas_resistance);
      Serial.print(" Uptime = ");
      Serial.print(popdata.milliSec);
      Serial.println(b ? " ok" : " fail");
    }
  }
}

void setup()
{
  pinMode(LED_BUILTIN, OUTPUT);
  digitalWrite(LED_BUILTIN, LOW);

  // Initialize LoRa chip.
  lora_rak4630_init();

  // Initialize Serial for debug output
  time_t serial_timeout = millis();
  // On nRF52840 the USB serial is not available immediately
  while (!Serial)
  {
    if ((millis() - serial_timeout) < 5000)
    {
      delay(100);
      // Blink green LED while we wait
      digitalWrite(LED_BUILTIN, !digitalRead(LED_BUILTIN));
    }
    else
    {
      break;
    }
  }

  Serial.println("=====================================");
  Serial.println("Welcome to RAK4630 LoRaWan!!!");
  if (doOTAA)
  {
    Serial.println("Type: OTAA");
  }
  else
  {
    Serial.println("Type: ABP");
  }

  switch (g_CurrentRegion)
  {
    case LORAMAC_REGION_AS923:
      Serial.println("Region: AS923");
      break;
    case LORAMAC_REGION_AU915:
      Serial.println("Region: AU915");
      break;
    case LORAMAC_REGION_CN470:
      Serial.println("Region: CN470");
      break;
    case LORAMAC_REGION_EU433:
      Serial.println("Region: EU433");
      break;
    case LORAMAC_REGION_IN865:
      Serial.println("Region: IN865");
      break;
    case LORAMAC_REGION_EU868:
      Serial.println("Region: EU868");
      break;
    case LORAMAC_REGION_KR920:
      Serial.println("Region: KR920");
      break;
    case LORAMAC_REGION_US915:
      Serial.println("Region: US915");
      break;
  }
  Serial.println("=====================================");

  //creat a user timer to send data to server period
  uint32_t err_code;
  err_code = timers_init();
  if (err_code != 0)
  {
    Serial.printf("timers_init failed - %d\n", err_code);
    return;
  }

  // Setup the EUIs and Keys
  if (doOTAA)
  {
    lmh_setDevEui(nodeDeviceEUI);
    lmh_setAppEui(nodeAppEUI);
    lmh_setAppKey(nodeAppKey);
  }
  else
  {
    lmh_setNwkSKey(nodeNwsKey);
    lmh_setAppSKey(nodeAppsKey);
    lmh_setDevAddr(nodeDevAddr);
  }

  // Initialize LoRaWan
  err_code = lmh_init(&g_lora_callbacks, g_lora_param_init, doOTAA, g_CurrentClass, g_CurrentRegion);
  if (err_code != 0)
  {
    Serial.printf("lmh_init failed - %d\n", err_code);
    return;
  }

  // Initialize BME680.
  bme680_init();
  // Initialize the queue.
  Q.begin();

  // Start Join procedure
  lmh_join();
}

void loop()
{
  // Check if a join retry should be made
  if (millis() - joinRetryTimepoint > JOIN_RETRY_INTERVAL)
  {
    joinRetryTimepoint = millis();
    if (retJoinRetry == true) {
      Serial.println("Starting Join procedure again...");
      lmh_join();
    }
  }

  // Read the sensors.
  if (millis() - sensorReadTimepoint > SENSOR_READ_INTERVAL) {
    sensorReadTimepoint = millis();

    if (! bme.performReading()) {
      Serial.println("Failed to perform reading :(");
      return;
    }
    Serial.print("SENSOR_READ_INTERVAL: ");
    Serial.println(SENSOR_READ_INTERVAL);

    // Toggle LED to show device is not frozen
    digitalWrite(LED_BUILTIN, !digitalRead(LED_BUILTIN));

    // Read bme680 and put data in queue
    bme680_get();
  }

  // Put data in buffer a few seconds before send event
  if (millis() - peekDataTimepoint > PEEK_DATA_INTERVAL)
  {
    peekDataTimepoint = millis();
    peekData();
  }
}

/**@brief LoRa function for handling HasJoined event.
*/
void lorawan_has_joined_handler(void)
{
  Serial.println("OTAA Mode, Network Joined!");

  lmh_error_status ret = lmh_class_request(g_CurrentClass);
  retJoinRetry = false;
  if (ret == LMH_SUCCESS)
  {
    delay(1000);
    TimerSetValue(&appTimer, LORAWAN_APP_INTERVAL);
    TimerStart(&appTimer);
    mightBeOffline = false; // Gateway is on now
  }
}
/**@brief LoRa function for handling OTAA join failed
*/
static void lorawan_join_failed_handler(void)
{
  Serial.println("OTAA join failed!");
  Serial.println("Check your EUI's and Keys's!");
  Serial.println("Check if a Gateway is in range!");
  retJoinRetry = true;
}
/**@brief Function for handling LoRaWan received data from Gateway

   @param[in] app_data  Pointer to rx data
*/
void lorawan_rx_handler(lmh_app_data_t *app_data)
{
  popData(); // pop the sent data record
  count_fail_copy = 0;

  Serial.printf("LoRa Packet received on port %d, size:%d, rssi:%d, snr:%d, data:%s\n",
                app_data->port, app_data->buffsize, app_data->rssi, app_data->snr, app_data->buffer);
}

void lorawan_confirm_class_handler(DeviceClass_t Class)
{
  Serial.printf("switch to class %c done\n", "ABC"[Class]);
  // Informs the server that switch has occurred ASAP
  m_lora_app_data.buffsize = 0;
  m_lora_app_data.port = gAppPort;
  lmh_send(&m_lora_app_data, g_CurrentConfirm);
}

void send_lora_frame(void)
{
  if (lmh_join_status_get() != LMH_SET)
  {
    //Not joined, try again later
    return;
  }

  // Send only if the queue is not empty, there are no past send failures
  // and the peekData() function has put data in the pstring_buffer
  if ((!Q.isEmpty()) && (mightBeOffline == false) && (strlen(pstring_buffer) > 0)) {
    uint32_t i = 0;
    memset(m_lora_app_data.buffer, 0, LORAWAN_APP_DATA_BUFF_SIZE);
    m_lora_app_data.port = gAppPort;

    /* Put RAK1906 sensors data in lorawan app buffer
       and avoid coppying excess data
    */
    int dataLength = strlen(pstring_buffer);
    if (dataLength > SENSORS_BUFFER_SIZE) {
      memcpy(m_lora_app_data.buffer, pstring_buffer, SENSORS_BUFFER_SIZE);
      i = SENSORS_BUFFER_SIZE - 1;
    } else {
      memcpy(m_lora_app_data.buffer, pstring_buffer, strlen(pstring_buffer) + 1);
      i = dataLength;
    }

    m_lora_app_data.buffsize = i;

    lmh_error_status error = lmh_send(&m_lora_app_data, g_CurrentConfirm);
    if (error == LMH_SUCCESS)
    {
      count++;
      Serial.printf("lmh_send ok count %d\n", count);
    }
    else
    {
      count_fail++;
      count_fail_copy++;
      if (count_fail_copy >= SEND_FAIL_COUNT) {
        retJoinRetry = true;
        count_fail_copy = 0;
        mightBeOffline = true; // Failures indicate gateway might be off
        Serial.println("Join Retry: count_fail_copy > SEND_FAIL_COUNT...");
      }
      Serial.printf("lmh_send fail count %d\n", count_fail);
    }
  } else {
    Serial.println("There is no data to send or the gateway might be off.");
  }
}

/**@brief Function for handling user timerout event.
*/
void tx_lora_periodic_handler(void)
{
  TimerSetValue(&appTimer, LORAWAN_APP_INTERVAL);
  TimerStart(&appTimer);
  Serial.println("Sending frame now...");
  send_lora_frame();
}

/**@brief Function for the Timer initialization.

   @details Initializes the timer module. This creates and starts application timers.
*/
uint32_t timers_init(void)
{
  TimerInit(&appTimer, tx_lora_periodic_handler);
  return 0;
}
