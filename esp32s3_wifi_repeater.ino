/*
 * ESP32-S3 Wi-Fi Repeater (routed NAT range extender)
 * ----------------------------------------------------------------------------
 * Target  : ESP32-S3, Arduino IDE, ESP32 Arduino core 3.x (3.0.0 or newer)
 * Libraries: ONLY libraries bundled with the ESP32 Arduino core
 *            (WiFi, WebServer, DNSServer, Preferences). Nothing to install.
 *
 * HOW IT WORKS
 *   - The ESP32-S3 runs in WIFI_AP_STA mode: one radio, two virtual interfaces.
 *   - STA joins your existing router (upstream).
 *   - AP creates the repeater network with its own DHCP server and its own
 *     subnet (default 192.168.50.0/24).
 *   - lwIP NAPT (Network Address and Port Translation) is enabled on the AP
 *     interface with WiFi.AP.enableNAPT(true). Packets from AP clients are
 *     routed out through STA with the source address rewritten to the ESP32's
 *     STA address. This is a ROUTED repeater (double NAT), not a transparent
 *     Layer-2 bridge. See the limitations in the README/answer.
 *   - The AP's DHCP server hands out the upstream router's DNS server, so
 *     clients resolve names directly through the upstream network.
 *
 * MODES
 *   SETUP    : no valid saved configuration -> setup AP + captive portal.
 *   REPEATER : valid configuration -> repeater AP + NAT + dashboard (login).
 *
 * Serial log tags: [BOOT] [WIFI] [AP] [NAT] [WEB] [CLIENT] [ERROR]
 */

#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <DNSServer.h>
#include <Preferences.h>
#include <esp_system.h>
#include <esp_timer.h>

#if !defined(ESP_ARDUINO_VERSION_MAJOR) || (ESP_ARDUINO_VERSION_MAJOR < 3)
#error "ESP32 Arduino core 3.0.0 or newer is required (WiFi.AP.enableNAPT)."
#endif
#if !defined(CONFIG_IDF_TARGET_ESP32S3)
#warning "This sketch is written for ESP32-S3. Select an ESP32S3 board in Tools > Board."
#endif

// ============================================================================
// Settings (single place for every constant / default)
// ============================================================================
#define FW_VERSION          "1.0.0"
#define HOSTNAME            "esp32s3-repeater"

#define SETUP_AP_SSID       "ESP32-S3-Repeater-Setup"
#define SETUP_AP_PASS       "repeater-setup"   // WPA2, >= 8 chars. Only used during first-time setup.
#define ADMIN_USER          "admin"            // dashboard login user (password is set during setup)

#define RESET_BUTTON_PIN    0                  // BOOT button on most ESP32-S3 boards
#define RESET_HOLD_MS       10000UL            // hold this long (while running) = factory reset

#define MAX_AP_CLIENTS      8                  // ESP32 hard limit is 10
#define CONNECT_TIMEOUT_MS  25000UL
#define BACKOFF_MIN_MS      5000UL             // reconnect backoff: 5s,10s,20s,40s,60s,60s...
#define BACKOFF_MAX_MS      60000UL
#define AP_RETRY_MS         5000UL
#define STATUS_INTERVAL_MS  1000UL
#define LOG_INTERVAL_MS     30000UL
#define LOW_HEAP_WARN       20000UL            // bytes: show warning
#define LOW_HEAP_CRIT       8000UL             // bytes: controlled restart if sustained
#define MAX_SCAN_RESULTS    20

static const IPAddress SETUP_AP_IP(192, 168, 4, 1);          // setup AP address
static const IPAddress FALLBACK_DNS(1, 1, 1, 1);             // only until upstream DNS is known
// Repeater AP subnet candidates. The first one that does not collide with the
// upstream router's subnet is used (a NAT router needs two different subnets).
static const IPAddress AP_CANDIDATES[] = {
  IPAddress(192, 168, 50, 1), IPAddress(192, 168, 77, 1),
  IPAddress(10, 77, 77, 1),   IPAddress(172, 20, 77, 1)
};
static const size_t AP_CANDIDATE_COUNT = sizeof(AP_CANDIDATES) / sizeof(AP_CANDIDATES[0]);

// ============================================================================
// Logging
// ============================================================================
#define LOG(tag, fmt, ...)  Serial.printf("[" tag "] " fmt "\n", ##__VA_ARGS__)
#define LOGE(fmt, ...)      Serial.printf("[ERROR] " fmt "\n", ##__VA_ARGS__)

// ============================================================================
// Types and global state
// ============================================================================
struct Config {
  char    staSsid[33];     // upstream SSID
  char    staPass[64];     // upstream password ("" = open network)
  char    apSsid[33];      // repeater SSID
  char    apPass[64];      // repeater password (WPA2, 8..63)
  char    adminPass[33];   // dashboard password (8..32)
  uint8_t apChannel;       // 0 = automatic (follow upstream), 1..11
};

enum StaState : uint8_t { STA_IDLE, STA_CONNECTING, STA_CONNECTED, STA_BACKOFF };

struct ScanEntry { char ssid[33]; int8_t rssi; uint8_t ch; uint8_t sec; };

struct Status {
  bool     staUp;
  int      rssi;
  uint8_t  channel;
  uint8_t  clients;
  uint32_t uptime;
  uint32_t heap;
  uint32_t minHeap;
  bool     memLow;
  char     staIp[16];
  char     apIp[16];
};

static Config      cfg;
static bool        cfgValid  = false;
static bool        setupMode = true;
static Preferences prefs;
static const char* NVS_NS = "repeater";

static WebServer   server(80);
static DNSServer   dnsServer;

static Status      status;
static IPAddress   apIp;
static IPAddress   apDns;
static bool        apOk        = false;
static uint32_t    apRetryAt   = 0;
static bool        natActive   = false;
static bool        natPending  = false;
static uint32_t    natRetryAt  = 0;

// Written from the Wi-Fi event task, read from loop(): keep them volatile.
static volatile StaState staState      = STA_IDLE;
static volatile bool     gotIpFlag     = false;
static volatile uint32_t nextAttemptAt = 0;
static const char* volatile lastError  = "";
static uint32_t staAttemptStart = 0;
static uint32_t backoffMs       = BACKOFF_MIN_MS;
static uint32_t reconnectCount  = 0;
static bool     attemptedOnce   = false;

static ScanEntry scanCache[MAX_SCAN_RESULTS];
static uint8_t   scanCount     = 0;
static bool      scanRunning   = false;
static uint32_t  scanStartedAt = 0;

static bool      restartPending = false;
static uint32_t  restartAt      = 0;
static uint32_t  lastStatusMs   = 0;
static uint32_t  lastLogMs      = 0;
static uint32_t  btnDownAt      = 0;
static uint32_t  critHeapSince  = 0;

static uint8_t   authFails = 0;
static uint32_t  authWindowStart = 0;
static uint32_t  authBlockUntil  = 0;

extern const char INDEX_HTML[];

// ============================================================================
// Small helpers
// ============================================================================
static void scheduleRestart(uint32_t inMs) {
  restartAt = millis() + inMs;
  restartPending = true;
}

static const char* resetReasonText() {
  switch (esp_reset_reason()) {
    case ESP_RST_POWERON:   return "power-on";
    case ESP_RST_SW:        return "software restart";
    case ESP_RST_PANIC:     return "panic/crash";
    case ESP_RST_INT_WDT:   return "interrupt watchdog";
    case ESP_RST_TASK_WDT:  return "task watchdog";
    case ESP_RST_WDT:       return "watchdog";
    case ESP_RST_BROWNOUT:  return "BROWNOUT (check power supply)";
    case ESP_RST_DEEPSLEEP: return "deep sleep wake";
    default:                return "other";
  }
}

static const char* currentApSsid() { return setupMode ? SETUP_AP_SSID : cfg.apSsid; }

static void fmtMac(const uint8_t* m, char* out) {
  snprintf(out, 18, "%02X:%02X:%02X:%02X:%02X:%02X", m[0], m[1], m[2], m[3], m[4], m[5]);
}

// Escape a string for safe embedding in a JSON string literal.
static void jsonEscape(const char* in, char* out, size_t outSize) {
  size_t o = 0;
  for (; *in && o + 7 < outSize; ++in) {
    uint8_t c = (uint8_t)*in;
    if (c == '"' || c == '\\')      { out[o++] = '\\'; out[o++] = (char)c; }
    else if (c < 0x20 || c == 0x7F) { o += snprintf(out + o, outSize - o, "\\u%04x", c); }
    else                            { out[o++] = (char)c; }
  }
  out[o] = 0;
}

static bool sameSubnet(const IPAddress& a, const IPAddress& b, const IPAddress& m) {
  for (int i = 0; i < 4; i++) if ((a[i] & m[i]) != (b[i] & m[i])) return false;
  return true;
}

// Map a Wi-Fi disconnect reason code to a human message.
// Numeric values come from esp_wifi_types.h (wifi_err_reason_t).
static const char* describeDisconnect(uint8_t r) {
  switch (r) {
    case 201:                 return "Router unavailable (SSID not found)";      // NO_AP_FOUND
    case 202: case 15: case 204:
                              return "Authentication failed (wrong password?)";  // AUTH_FAIL, 4WAY/HANDSHAKE timeout
    case 200:                 return "Upstream signal lost (beacon timeout)";    // BEACON_TIMEOUT
    case 203: case 205:       return "Association with router failed";           // ASSOC_FAIL, CONNECTION_FAIL
    case 2:                   return "Authentication expired";                   // AUTH_EXPIRE
    case 3: case 4: case 6: case 7:
                              return "Router disconnected the repeater";         // AUTH_LEAVE, ASSOC_EXPIRE...
    default:                  return "Upstream connection failed or lost";
  }
}

// ============================================================================
// Input validation
// ============================================================================
static bool validSsid(const String& s) {
  size_t n = s.length();
  if (n < 1 || n > 32) return false;
  for (size_t i = 0; i < n; i++) { uint8_t c = (uint8_t)s[i]; if (c < 0x20 || c == 0x7F) return false; }
  return true;
}
static bool validPrintable(const String& s, size_t minLen, size_t maxLen) {
  size_t n = s.length();
  if (n < minLen || n > maxLen) return false;
  for (size_t i = 0; i < n; i++) { uint8_t c = (uint8_t)s[i]; if (c < 0x20 || c > 0x7E) return false; }
  return true;
}
static bool validWpaPass(const String& s) { return validPrintable(s, 8, 63); }
static bool validAdminPass(const String& s) { return validPrintable(s, 8, 32); }

// Returns nullptr when the configuration is complete and valid.
static const char* configError(const Config& c) {
  size_t a = strlen(c.staSsid), b = strlen(c.apSsid), sp = strlen(c.staPass), ap = strlen(c.apPass), ad = strlen(c.adminPass);
  if (a < 1 || a > 32)                     return "Invalid upstream SSID";
  if (sp != 0 && (sp < 8 || sp > 63))      return "Invalid upstream password";
  if (b < 1 || b > 32)                     return "Invalid repeater SSID";
  if (ap < 8 || ap > 63)                   return "Invalid repeater password";
  if (ad < 8 || ad > 32)                   return "Invalid admin password";
  if (c.apChannel > 11)                    return "Invalid channel";
  if (strcmp(c.staSsid, c.apSsid) == 0)    return "Repeater SSID must differ from the upstream SSID";
  return nullptr;
}

// ============================================================================
// Configuration storage (Preferences / NVS)
// ============================================================================
void loadConfig() {
  memset(&cfg, 0, sizeof(cfg));
  if (!prefs.begin(NVS_NS, false)) {
    LOGE("NVS open failed, starting in setup mode");
    lastError = "Storage error (NVS)";
    cfgValid = false; setupMode = true;
    return;
  }
  prefs.getString("sta_ssid", cfg.staSsid,  sizeof(cfg.staSsid));
  prefs.getString("sta_pass", cfg.staPass,  sizeof(cfg.staPass));
  prefs.getString("ap_ssid",  cfg.apSsid,   sizeof(cfg.apSsid));
  prefs.getString("ap_pass",  cfg.apPass,   sizeof(cfg.apPass));
  prefs.getString("adm_pass", cfg.adminPass, sizeof(cfg.adminPass));
  cfg.apChannel = prefs.getUChar("ap_ch", 0);
  prefs.end();

  bool blank = !cfg.staSsid[0] && !cfg.apSsid[0] && !cfg.adminPass[0];
  const char* err = configError(cfg);
  cfgValid  = (err == nullptr);
  setupMode = !cfgValid;
  if (!cfgValid && !blank) {
    lastError = "Invalid stored configuration - please run setup again";
    LOGE("Stored configuration invalid: %s", err);
  }
  LOG("BOOT", "Configuration %s", cfgValid ? "loaded" : (blank ? "not found (first boot)" : "invalid"));
}

bool saveConfig(const Config& c) {
  if (!prefs.begin(NVS_NS, false)) { LOGE("NVS open failed while saving"); return false; }
  bool ok = true;
  ok &= prefs.putString("sta_ssid", c.staSsid)   > 0;
  prefs.putString("sta_pass", c.staPass);                 // may legitimately be empty (open network)
  ok &= prefs.putString("ap_ssid",  c.apSsid)    > 0;
  ok &= prefs.putString("ap_pass",  c.apPass)    > 0;
  ok &= prefs.putString("adm_pass", c.adminPass) > 0;
  ok &= prefs.putUChar("ap_ch",     c.apChannel) > 0;
  prefs.end();
  if (!ok) LOGE("Failed to write configuration to NVS");
  return ok;
}

static void factoryReset() {
  if (prefs.begin(NVS_NS, false)) { prefs.clear(); prefs.end(); }
  LOG("BOOT", "Configuration erased (factory reset)");
}

// ============================================================================
// Wi-Fi events (run in the system event task: keep them short, set flags only)
// ============================================================================
static void onStaDisconnected(uint8_t reason) {
  if (reason == 8 && staState != STA_CONNECTED) return;     // ASSOC_LEAVE caused by our own disconnect()
  StaState s = staState;
  if (s == STA_CONNECTED) {
    lastError = describeDisconnect(reason);
    LOG("WIFI", "Upstream connection LOST (reason %u: %s)", reason, lastError);
    backoffMs = BACKOFF_MIN_MS;
    nextAttemptAt = millis() + backoffMs;
    staState = STA_BACKOFF;
  } else if (s == STA_CONNECTING) {
    lastError = describeDisconnect(reason);
    LOGE("Upstream connect failed (reason %u: %s)", reason, lastError);
    nextAttemptAt = millis() + backoffMs;
    LOG("WIFI", "Next attempt in %lu s", (unsigned long)(backoffMs / 1000));
    backoffMs = min<uint32_t>(backoffMs * 2, BACKOFF_MAX_MS);
    staState = STA_BACKOFF;
  }
  // STA_IDLE / STA_BACKOFF: ignore (setup mode, or duplicate event)
}

void handleWiFiEvents(arduino_event_id_t event, arduino_event_info_t info) {
  char mac[18];
  switch (event) {
    case ARDUINO_EVENT_WIFI_STA_START:
      LOG("WIFI", "Station interface started");
      break;
    case ARDUINO_EVENT_WIFI_STA_CONNECTED:
      LOG("WIFI", "Associated with upstream router (channel %u)", info.wifi_sta_connected.channel);
      break;
    case ARDUINO_EVENT_WIFI_STA_GOT_IP:
      staState = STA_CONNECTED;
      backoffMs = BACKOFF_MIN_MS;
      lastError = "";
      gotIpFlag = true;                       // NAT is configured from loop()
      break;
    case ARDUINO_EVENT_WIFI_STA_LOST_IP:
      LOG("WIFI", "Lost upstream IP address");
      break;
    case ARDUINO_EVENT_WIFI_STA_DISCONNECTED:
      onStaDisconnected(info.wifi_sta_disconnected.reason);
      break;
    case ARDUINO_EVENT_WIFI_AP_START:
      LOG("AP", "Access point interface started");
      break;
    case ARDUINO_EVENT_WIFI_AP_STOP:
      LOG("AP", "Access point interface stopped");
      break;
    case ARDUINO_EVENT_WIFI_AP_STACONNECTED:
      fmtMac(info.wifi_ap_staconnected.mac, mac);
      LOG("CLIENT", "Connected    %s (clients now: %u)", mac, (unsigned)WiFi.softAPgetStationNum());
      break;
    case ARDUINO_EVENT_WIFI_AP_STADISCONNECTED:
      fmtMac(info.wifi_ap_stadisconnected.mac, mac);
      LOG("CLIENT", "Disconnected %s (clients now: %u)", mac, (unsigned)WiFi.softAPgetStationNum());
      break;
    case ARDUINO_EVENT_WIFI_AP_STAIPASSIGNED:
      LOG("CLIENT", "IP assigned  %s", IPAddress(info.wifi_ap_staipassigned.ip.addr).toString().c_str());
      break;
    default:
      break;
  }
}

// ============================================================================
// Access point
// ============================================================================
bool startAccessPoint() {
  const char* ssid = currentApSsid();
  const char* pass = setupMode ? SETUP_AP_PASS : cfg.apPass;
  // While STA is connected the radio is locked to the router's channel anyway,
  // so this value only matters while the upstream is not connected.
  int channel = setupMode ? 1 : (cfg.apChannel ? cfg.apChannel : 1);

  apIp  = setupMode ? SETUP_AP_IP : AP_CANDIDATES[0];
  apDns = setupMode ? apIp : FALLBACK_DNS;     // setup: DNS = ourselves (captive portal)
  IPAddress mask(255, 255, 255, 0);
  IPAddress leaseStart = apIp;
  leaseStart[3] = apIp[3] + 1;

  if (!WiFi.softAPConfig(apIp, apIp, mask, leaseStart, apDns)) {
    LOGE("AP network configuration failed");
    lastError = "Access point failed to start (network config)";
    apOk = false; apRetryAt = millis() + AP_RETRY_MS;
    return false;
  }
  if (!WiFi.softAP(ssid, pass, channel, 0, MAX_AP_CLIENTS)) {
    LOGE("softAP() failed for SSID \"%s\"", ssid);
    lastError = "Access point failed to start";
    apOk = false; apRetryAt = millis() + AP_RETRY_MS;
    return false;
  }
  apOk = true;
  LOG("AP", "%s AP \"%s\" up, IP %s, channel %d", setupMode ? "Setup" : "Repeater", ssid,
      WiFi.softAPIP().toString().c_str(), channel);

  if (setupMode) {
    // Captive portal DNS: answer every name with our own address.
    dnsServer.setErrorReplyCode(DNSReplyCode::NoError);
    dnsServer.start(53, "*", WiFi.softAPIP());
    LOG("AP", "Setup AP password: %s  |  open http://%s/", SETUP_AP_PASS, WiFi.softAPIP().toString().c_str());
  }
  return true;
}

// ============================================================================
// Upstream Wi-Fi (non-blocking state machine)
// ============================================================================
void connectToUpstreamWiFi() {
  if (setupMode || !cfg.staSsid[0]) return;
  if (attemptedOnce) reconnectCount++;
  attemptedOnce = true;
  LOG("WIFI", "Connecting to \"%s\" (attempt %lu)...", cfg.staSsid, (unsigned long)(reconnectCount + 1));
  staAttemptStart = millis();
  staState = STA_CONNECTING;
  WiFi.begin(cfg.staSsid, cfg.staPass[0] ? cfg.staPass : nullptr);
}

// Called every loop(): drives connect / timeout / backoff without delay().
void checkWiFiConnection() {
  if (setupMode) return;
  uint32_t now = millis();
  switch (staState) {
    case STA_IDLE:
      connectToUpstreamWiFi();
      break;
    case STA_CONNECTING:
      if (now - staAttemptStart >= CONNECT_TIMEOUT_MS) {
        lastError = "Connection timeout";
        LOGE("Upstream connection timeout");
        staState = STA_BACKOFF;                 // set first so the resulting disconnect event is ignored
        nextAttemptAt = now + backoffMs;
        backoffMs = min<uint32_t>(backoffMs * 2, BACKOFF_MAX_MS);
        WiFi.disconnect(false, false);          // abort the attempt, keep the radio on
      }
      break;
    case STA_BACKOFF:
      if ((int32_t)(now - nextAttemptAt) >= 0) connectToUpstreamWiFi();
      break;
    case STA_CONNECTED:
      break;
  }
}

// ============================================================================
// NAT / routing
// ============================================================================
// Re-applies the AP address + DHCP DNS (this restarts the AP's DHCP server).
static bool applyApNetwork() {
  WiFi.AP.enableNAPT(false);                    // detach NAT before changing addressing
  natActive = false;
  IPAddress mask(255, 255, 255, 0);
  IPAddress leaseStart = apIp;
  leaseStart[3] = apIp[3] + 1;
  return WiFi.softAPConfig(apIp, apIp, mask, leaseStart, apDns);
}

// Runs after the STA got an IP: pick a non-colliding AP subnet, hand the
// upstream DNS to AP clients, and switch lwIP NAPT on for the AP interface.
static bool configureNat() {
  if (!WiFi.AP.started()) return false;         // AP not ready yet: retry shortly

  IPAddress staIp   = WiFi.localIP();
  IPAddress staMask = WiFi.subnetMask();
  IPAddress upDns   = WiFi.dnsIP(0);
  if (upDns == IPAddress((uint32_t)0)) upDns = FALLBACK_DNS;
  const IPAddress m24(255, 255, 255, 0);

  bool changed = false;
  // 1) The two subnets of a NAT router must differ.
  if (sameSubnet(staIp, apIp, m24) || sameSubnet(staIp, apIp, staMask)) {
    for (size_t i = 0; i < AP_CANDIDATE_COUNT; i++) {
      const IPAddress& cand = AP_CANDIDATES[i];
      if (!sameSubnet(staIp, cand, m24) && !sameSubnet(staIp, cand, staMask)) { apIp = cand; changed = true; break; }
    }
    LOG("NAT", "Upstream subnet collides with AP subnet, AP moved to %s", apIp.toString().c_str());
  }
  // 2) Clients should use the upstream DNS server.
  if (apDns != upDns) { apDns = upDns; changed = true; }

  if (changed && !applyApNetwork()) {
    LOGE("Could not re-apply AP network settings");
    lastError = "NAT setup failed (AP network)";
    return false;
  }
  // 3) Enable NAPT on the AP interface (requires an upstream default route = STA).
  if (!WiFi.AP.enableNAPT(true)) {
    LOGE("WiFi.AP.enableNAPT(true) failed - NAPT not available in this core build?");
    lastError = "NAT could not be enabled";
    return false;
  }
  natActive = true;
  LOG("NAT", "NAPT enabled: AP %s/24  ->  STA %s via gateway %s, client DNS %s",
      apIp.toString().c_str(), staIp.toString().c_str(),
      WiFi.gatewayIP().toString().c_str(), apDns.toString().c_str());
  return true;
}

static void serviceNat() {
  if (setupMode) return;
  if (gotIpFlag) {
    gotIpFlag = false;
    LOG("WIFI", "Connected to \"%s\"  IP %s  RSSI %d dBm  channel %u", cfg.staSsid,
        WiFi.localIP().toString().c_str(), WiFi.RSSI(), (unsigned)WiFi.channel());
    natPending = true;
    natRetryAt = millis();
  }
  if (natPending && (int32_t)(millis() - natRetryAt) >= 0) {
    if (configureNat()) natPending = false;
    else natRetryAt = millis() + 2000;
  }
}

// ============================================================================
// Scan (asynchronous, results cached in a fixed array: no heap churn)
// ============================================================================
static void startScan() {
  if (scanRunning) return;
  if (scanStartedAt && millis() - scanStartedAt < 4000) return;     // rate limit
  int r = WiFi.scanNetworks(true);
  scanStartedAt = millis();
  if (r == WIFI_SCAN_FAILED) { LOGE("Wi-Fi scan could not be started"); return; }
  scanRunning = true;
  LOG("WIFI", "Scan started");
}

static void pollScan() {
  if (!scanRunning) return;
  int n = WiFi.scanComplete();
  if (n == WIFI_SCAN_RUNNING) {
    if (millis() - scanStartedAt > 15000) { scanRunning = false; WiFi.scanDelete(); LOGE("Wi-Fi scan timed out"); }
    return;
  }
  scanRunning = false;
  scanCount = 0;
  if (n < 0) { LOGE("Wi-Fi scan failed"); return; }
  for (int i = 0; i < n && scanCount < MAX_SCAN_RESULTS; i++) {
    String s = WiFi.SSID(i);
    if (s.length() == 0 || s.length() > 32) continue;               // skip hidden / odd entries
    bool dup = false;                                               // list is RSSI-sorted: keep strongest
    for (uint8_t k = 0; k < scanCount; k++) if (strcmp(scanCache[k].ssid, s.c_str()) == 0) { dup = true; break; }
    if (dup) continue;
    ScanEntry& e = scanCache[scanCount++];
    strlcpy(e.ssid, s.c_str(), sizeof(e.ssid));
    e.rssi = (int8_t)WiFi.RSSI(i);
    e.ch   = (uint8_t)WiFi.channel(i);
    e.sec  = (WiFi.encryptionType(i) != WIFI_AUTH_OPEN) ? 1 : 0;
  }
  WiFi.scanDelete();
  LOG("WIFI", "Scan finished: %u networks", (unsigned)scanCount);
}

// ============================================================================
// Status snapshot
// ============================================================================
void updateStatus() {
  status.uptime  = (uint32_t)(esp_timer_get_time() / 1000000LL);
  status.heap    = ESP.getFreeHeap();
  status.minHeap = ESP.getMinFreeHeap();
  status.clients = WiFi.softAPgetStationNum();
  status.channel = (uint8_t)WiFi.channel();
  status.staUp   = (staState == STA_CONNECTED);
  status.rssi    = status.staUp ? WiFi.RSSI() : 0;
  strlcpy(status.staIp, status.staUp ? WiFi.localIP().toString().c_str() : "-", sizeof(status.staIp));
  strlcpy(status.apIp, WiFi.softAPIP().toString().c_str(), sizeof(status.apIp));

  status.memLow = status.heap < LOW_HEAP_WARN;
  uint32_t now = millis();
  if (status.heap < LOW_HEAP_CRIT) {
    if (!critHeapSince) critHeapSince = now ? now : 1;
    else if (now - critHeapSince > 10000UL && status.uptime > 60 && !restartPending) {
      LOGE("Free heap critically low (%lu bytes) - restarting", (unsigned long)status.heap);
      scheduleRestart(500);
    }
  } else critHeapSince = 0;
}

static const char* describeState(const char** level) {
  if (setupMode)                                  { *level = "warn"; return "Setup mode - waiting for configuration"; }
  if (!apOk)                                      { *level = "err";  return "Access point failed to start"; }
  switch (staState) {
    case STA_CONNECTED:  if (natActive) { *level = "ok"; return "Repeater active (NAT on)"; }
                         *level = "warn"; return "Connected - enabling NAT";
    case STA_CONNECTING: *level = "warn"; return "Connecting to upstream...";
    case STA_BACKOFF:    *level = "err";  return "Upstream unavailable - reconnecting";
    default:             *level = "warn"; return "Starting...";
  }
}

// ============================================================================
// Web server helpers
// ============================================================================
static void sendSecurityHeaders() {
  server.sendHeader("Cache-Control", "no-store");
  server.sendHeader("X-Content-Type-Options", "nosniff");
  server.sendHeader("X-Frame-Options", "DENY");
  server.sendHeader("Content-Security-Policy",
    "default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; connect-src 'self'; img-src data:");
}
static void sendJson(int code, const char* body) {
  sendSecurityHeaders();
  server.send(code, "application/json", body);
}
static void sendJsonError(int code, const char* msg) {   // msg must not contain quotes
  char b[200];
  snprintf(b, sizeof(b), "{\"ok\":false,\"error\":\"%s\"}", msg);
  sendJson(code, b);
}

// HTTP Basic auth (user "admin") in repeater mode, with simple brute-force throttling.
static bool requireAuth() {
  if (setupMode) return true;                                   // setup AP is WPA2-protected
  uint32_t now = millis();
  if (authBlockUntil && (int32_t)(now - authBlockUntil) < 0) {
    sendJsonError(429, "Too many attempts. Try again in a minute.");
    return false;
  }
  if (server.authenticate(ADMIN_USER, cfg.adminPass)) { authFails = 0; return true; }
  if (now - authWindowStart > 30000UL) { authWindowStart = now; authFails = 0; }
  if (++authFails > 12) {
    authBlockUntil = now + 60000UL; if (!authBlockUntil) authBlockUntil = 1;
    LOGE("Too many failed logins - web login blocked for 60 s");
  }
  server.requestAuthentication(BASIC_AUTH, "ESP32-S3 Repeater");
  return false;
}

// State-changing requests must carry a custom header. A cross-site HTML form
// cannot set it, which blocks CSRF against a browser that is already logged in.
static bool requireXhr() {
  if (server.header("X-Requested-With") != "repeater-ui") {
    sendJsonError(403, "Forbidden");
    return false;
  }
  return true;
}

// ============================================================================
// Web handlers
// ============================================================================
void handleDashboard() {
  if (!requireAuth()) return;
  sendSecurityHeaders();
  server.send_P(200, "text/html", INDEX_HTML);
}

void handleStatus() {
  if (!requireAuth()) return;
  const char* level = "warn";
  const char* state = describeState(&level);
  char s1[200], s2[200], er[120];
  jsonEscape(setupMode ? "" : cfg.staSsid, s1, sizeof(s1));
  jsonEscape(currentApSsid(), s2, sizeof(s2));
  jsonEscape(lastError, er, sizeof(er));
  char buf[1024];
  snprintf(buf, sizeof(buf),
    "{\"mode\":\"%s\",\"state\":\"%s\",\"level\":\"%s\",\"nat\":%s,\"staUp\":%s,"
    "\"staSsid\":\"%s\",\"staIp\":\"%s\",\"apSsid\":\"%s\",\"apIp\":\"%s\","
    "\"rssi\":%d,\"ch\":%u,\"cfgCh\":%u,\"clients\":%u,\"uptime\":%lu,"
    "\"heap\":%lu,\"minHeap\":%lu,\"reconn\":%lu,\"err\":\"%s\",\"memLow\":%s}",
    setupMode ? "setup" : "repeater", state, level, natActive ? "true" : "false", status.staUp ? "true" : "false",
    s1, status.staIp, s2, status.apIp,
    status.rssi, (unsigned)status.channel, (unsigned)cfg.apChannel, (unsigned)status.clients, (unsigned long)status.uptime,
    (unsigned long)status.heap, (unsigned long)status.minHeap, (unsigned long)reconnectCount, er,
    status.memLow ? "true" : "false");
  sendJson(200, buf);
}

void handleSystemInfo() {
  if (!requireAuth()) return;
  char buf[640];
  snprintf(buf, sizeof(buf),
    "{\"fw\":\"%s\",\"chip\":\"%s rev %u\",\"cores\":%u,\"mhz\":%u,\"flashKB\":%lu,\"psramKB\":%lu,"
    "\"sketchKB\":%lu,\"sdk\":\"%s\",\"core\":\"%d.%d.%d\",\"staMac\":\"%s\",\"apMac\":\"%s\","
    "\"reset\":\"%s\",\"minHeap\":%lu}",
    FW_VERSION, ESP.getChipModel(), (unsigned)ESP.getChipRevision(), (unsigned)ESP.getChipCores(),
    (unsigned)ESP.getCpuFreqMHz(), (unsigned long)(ESP.getFlashChipSize() / 1024),
    (unsigned long)(ESP.getPsramSize() / 1024), (unsigned long)(ESP.getSketchSize() / 1024),
    ESP.getSdkVersion(), ESP_ARDUINO_VERSION_MAJOR, ESP_ARDUINO_VERSION_MINOR, ESP_ARDUINO_VERSION_PATCH,
    WiFi.macAddress().c_str(), WiFi.softAPmacAddress().c_str(), resetReasonText(),
    (unsigned long)ESP.getMinFreeHeap());
  sendJson(200, buf);
}

// GET /api/scan[?start=1]  -> {"scanning":bool,"networks":[{ssid,rssi,ch,sec}...]}
void handleScan() {
  if (!requireAuth()) return;
  if (server.hasArg("start")) startScan();
  sendSecurityHeaders();
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);               // chunked: no big String needed
  server.send(200, "application/json", "");
  server.sendContent(scanRunning ? "{\"scanning\":true,\"networks\":[" : "{\"scanning\":false,\"networks\":[");
  char esc[200], line[300];
  for (uint8_t i = 0; i < scanCount; i++) {
    jsonEscape(scanCache[i].ssid, esc, sizeof(esc));
    snprintf(line, sizeof(line), "%s{\"ssid\":\"%s\",\"rssi\":%d,\"ch\":%u,\"sec\":%u}",
             i ? "," : "", esc, (int)scanCache[i].rssi, (unsigned)scanCache[i].ch, (unsigned)scanCache[i].sec);
    server.sendContent(line);
  }
  server.sendContent("]}");
  server.sendContent("");                                        // end of chunked body
}

// ---- form field parsers: return nullptr on success, else an error message ----
static const char* readUpstream(Config& c, bool keepIfBlank) {
  String ssid = server.arg("ssid");
  String pass = server.arg("pass");
  bool open   = (server.arg("open") == "1");
  if (!validSsid(ssid)) return "Invalid upstream SSID (1-32 characters)";
  if (open) {
    c.staPass[0] = 0;
  } else if (pass.length() == 0 && keepIfBlank && strcmp(ssid.c_str(), c.staSsid) == 0 && c.staPass[0]) {
    // unchanged SSID + blank password = keep the stored password
  } else if (!validWpaPass(pass)) {
    return "Upstream password must be 8-63 printable characters";
  } else {
    strlcpy(c.staPass, pass.c_str(), sizeof(c.staPass));
  }
  strlcpy(c.staSsid, ssid.c_str(), sizeof(c.staSsid));
  return nullptr;
}

static const char* readRepeater(Config& c, bool keepIfBlank) {
  String ssid = server.arg("apssid");
  String pass = server.arg("appass");
  String adm  = server.arg("adminpass");
  String ch   = server.arg("channel");
  if (!validSsid(ssid)) return "Invalid repeater SSID (1-32 characters)";
  if (!(pass.length() == 0 && keepIfBlank)) {
    if (!validWpaPass(pass)) return "Repeater password must be 8-63 printable characters";
    strlcpy(c.apPass, pass.c_str(), sizeof(c.apPass));
  }
  if (!(adm.length() == 0 && keepIfBlank)) {
    if (!validAdminPass(adm)) return "Admin password must be 8-32 printable characters";
    strlcpy(c.adminPass, adm.c_str(), sizeof(c.adminPass));
  }
  if (ch.length()) {
    if (ch.length() > 2) return "Invalid channel";
    for (size_t i = 0; i < ch.length(); i++) if (ch[i] < '0' || ch[i] > '9') return "Invalid channel";
    int v = ch.toInt();
    if (v < 0 || v > 11) return "Channel must be Auto or 1-11";
    c.apChannel = (uint8_t)v;
  }
  strlcpy(c.apSsid, ssid.c_str(), sizeof(c.apSsid));
  return nullptr;
}

static void commitConfig(const Config& c) {
  const char* err = configError(c);
  if (err) { sendJsonError(400, err); return; }
  if (!saveConfig(c)) { sendJsonError(500, "Could not save configuration (storage error)"); return; }
  LOG("WEB", "Configuration saved, restarting");
  sendJson(200, "{\"ok\":true,\"msg\":\"Saved. The ESP32 is restarting...\"}");
  scheduleRestart(1500);
}

// POST /api/wifi : change upstream network (dashboard, repeater mode)
void handleWiFiSettings() {
  if (!requireAuth() || !requireXhr()) return;
  Config c = cfg;
  const char* err = readUpstream(c, true);
  if (err) { sendJsonError(400, err); return; }
  commitConfig(c);
}

// POST /api/ap : change repeater SSID/password/channel/admin password
void handleApSettings() {
  if (!requireAuth() || !requireXhr()) return;
  Config c = cfg;
  const char* err = readRepeater(c, true);
  if (err) { sendJsonError(400, err); return; }
  commitConfig(c);
}

// POST /api/setup : first-time configuration (setup mode only)
void handleSetup() {
  if (!setupMode) { sendJsonError(403, "Setup is already complete"); return; }
  if (!requireXhr()) return;
  Config c;
  memset(&c, 0, sizeof(c));
  const char* err = readUpstream(c, false);
  if (!err) err = readRepeater(c, false);
  if (err) { sendJsonError(400, err); return; }
  commitConfig(c);
}

void handleRestart() {
  if (!requireAuth() || !requireXhr()) return;
  LOG("WEB", "Restart requested");
  sendJson(200, "{\"ok\":true,\"msg\":\"Restarting...\"}");
  scheduleRestart(1000);
}

void handleFactoryReset() {
  if (!requireAuth() || !requireXhr()) return;
  LOG("WEB", "Factory reset requested");
  factoryReset();
  sendJson(200, "{\"ok\":true,\"msg\":\"Configuration erased. The ESP32 is restarting into setup mode...\"}");
  scheduleRestart(1000);
}

// Captive-portal probes (Android, iOS/macOS, Windows, Kindle...) and unknown URLs.
static void redirectToPortal() {
  char url[40];
  snprintf(url, sizeof(url), "http://%s/", WiFi.softAPIP().toString().c_str());
  server.sendHeader("Location", url, true);
  server.sendHeader("Cache-Control", "no-store");
  server.send(302, "text/plain", "");
}
void handleCaptive() {
  if (setupMode) redirectToPortal();
  else server.send(404, "text/plain", "Not found");
}
void handleNotFound() {
  if (setupMode) redirectToPortal();
  else server.send(404, "text/plain", "Not found");
}

void startWebServer() {
  static const char* hdrs[] = { "X-Requested-With" };
  server.collectHeaders(hdrs, 1);
  server.on("/",           HTTP_GET,  handleDashboard);
  server.on("/api/status", HTTP_GET,  handleStatus);
  server.on("/api/system", HTTP_GET,  handleSystemInfo);
  server.on("/api/scan",   HTTP_GET,  handleScan);
  server.on("/api/wifi",   HTTP_POST, handleWiFiSettings);
  server.on("/api/ap",     HTTP_POST, handleApSettings);
  server.on("/api/setup",  HTTP_POST, handleSetup);
  server.on("/api/restart", HTTP_POST, handleRestart);
  server.on("/api/factory", HTTP_POST, handleFactoryReset);
  static const char* probes[] = {
    "/generate_204", "/gen_204", "/hotspot-detect.html", "/library/test/success.html",
    "/connecttest.txt", "/ncsi.txt", "/redirect", "/canonical.html", "/success.txt",
    "/fwlink", "/kindle-wifi/wifiredirect.html"
  };
  for (size_t i = 0; i < sizeof(probes) / sizeof(probes[0]); i++) server.on(probes[i], HTTP_ANY, handleCaptive);
  server.onNotFound(handleNotFound);
  server.begin();
  LOG("WEB", "HTTP server listening on port 80 (%s)", setupMode ? "setup, no login" : "login required");
}

// ============================================================================
// Periodic services called from loop()
// ============================================================================
static void serviceButton(uint32_t now) {
  if (restartPending) return;
  if (digitalRead(RESET_BUTTON_PIN) == LOW) {
    if (!btnDownAt) btnDownAt = now ? now : 1;
    else if (now - btnDownAt >= RESET_HOLD_MS) {
      LOG("BOOT", "Reset button held for %lu s - factory reset", (unsigned long)(RESET_HOLD_MS / 1000));
      factoryReset();
      scheduleRestart(300);
    }
  } else btnDownAt = 0;
}

static void serviceLog() {
  if (setupMode) {
    LOG("AP", "Setup mode | clients %u | heap %lu", (unsigned)status.clients, (unsigned long)status.heap);
  } else if (status.staUp) {
    LOG("WIFI", "Upstream \"%s\" OK | IP %s | RSSI %d dBm | ch %u | AP clients %u | heap %lu (min %lu) | reconnects %lu",
        cfg.staSsid, status.staIp, status.rssi, (unsigned)status.channel, (unsigned)status.clients,
        (unsigned long)status.heap, (unsigned long)status.minHeap, (unsigned long)reconnectCount);
  } else {
    LOG("WIFI", "Upstream \"%s\" DOWN (%s) | AP clients %u | heap %lu | reconnects %lu",
        cfg.staSsid, (const char*)lastError, (unsigned)status.clients, (unsigned long)status.heap,
        (unsigned long)reconnectCount);
  }
}

// ============================================================================
// Arduino entry points
// ============================================================================
void setup() {
  Serial.begin(115200);
  uint32_t t0 = millis();
  while (!Serial && millis() - t0 < 1500) { yield(); }          // bounded wait for USB-CDC
  LOG("BOOT", "ESP32-S3 Wi-Fi Repeater v%s", FW_VERSION);
  LOG("BOOT", "Chip %s rev %u, %u cores @ %u MHz, free heap %lu, reset reason: %s",
      ESP.getChipModel(), (unsigned)ESP.getChipRevision(), (unsigned)ESP.getChipCores(),
      (unsigned)ESP.getCpuFreqMHz(), (unsigned long)ESP.getFreeHeap(), resetReasonText());

  pinMode(RESET_BUTTON_PIN, INPUT_PULLUP);
  loadConfig();

  WiFi.persistent(false);                 // credentials live only in our own NVS namespace
  WiFi.setAutoReconnect(false);           // reconnect is handled by checkWiFiConnection()
  WiFi.onEvent(handleWiFiEvents);
  WiFi.setHostname(HOSTNAME);
  WiFi.mode(WIFI_AP_STA);                 // STA + AP on the single radio (STA also does scans in setup mode)
  WiFi.setSleep(false);                   // no modem sleep: lower latency / better AP throughput
  WiFi.setScanMethod(WIFI_ALL_CHANNEL_SCAN);
  WiFi.setSortMethod(WIFI_CONNECT_AP_BY_SIGNAL);   // pick the strongest AP when several share the SSID

  startAccessPoint();
  startWebServer();
  updateStatus();
  LOG("BOOT", "Mode: %s", setupMode ? "SETUP" : "REPEATER");
  // The first upstream connection attempt is started by checkWiFiConnection() in loop().
}

void loop() {
  const uint32_t now = millis();

  server.handleClient();
  if (setupMode) dnsServer.processNextRequest();

  pollScan();
  checkWiFiConnection();
  serviceNat();
  if (!apOk && (int32_t)(now - apRetryAt) >= 0) startAccessPoint();
  serviceButton(now);

  if (now - lastStatusMs >= STATUS_INTERVAL_MS) { lastStatusMs = now; updateStatus(); }
  if (now - lastLogMs    >= LOG_INTERVAL_MS)    { lastLogMs = now;    serviceLog();  }

  if (restartPending && (int32_t)(now - restartAt) >= 0) {
    LOG("BOOT", "Restarting...");
    Serial.flush();
    ESP.restart();
  }

  // Cooperative 2 ms yield (not a blocking wait): lets the IDLE task run so the
  // task watchdog is fed, and keeps CPU use sane while Wi-Fi/lwIP tasks work.
  vTaskDelay(pdMS_TO_TICKS(2));
}

// ============================================================================
// Web UI (single page, served from flash; all dynamic text uses textContent)
// ============================================================================
const char INDEX_HTML[] PROGMEM = R"HTML(<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>ESP32-S3 Repeater</title>
<style>
:root{--bg:#0e141b;--card:#17202a;--bd:#263241;--tx:#e8eef5;--mu:#8b99a9;--ac:#3b9cff;--ok:#2ecc71;--wa:#f5a623;--er:#ff5c5c}
@media(prefers-color-scheme:light){:root{--bg:#f2f5f9;--card:#fff;--bd:#dce3ec;--tx:#14202b;--mu:#5a6a7b}}
*{box-sizing:border-box}[hidden]{display:none!important}
body{margin:0;font:15px/1.5 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;background:var(--bg);color:var(--tx)}
header{display:flex;justify-content:space-between;align-items:center;gap:12px;padding:14px 20px;background:var(--card);border-bottom:1px solid var(--bd);position:sticky;top:0;z-index:2}
h1{font-size:18px;margin:0}h2{font-size:16px;margin:22px 0 4px}
.badge{padding:4px 12px;border-radius:99px;font-size:13px;font-weight:600;background:var(--bd);color:var(--mu);white-space:nowrap}
.badge.ok{background:rgba(46,204,113,.16);color:var(--ok)}.badge.warn{background:rgba(245,166,35,.16);color:var(--wa)}.badge.err{background:rgba(255,92,92,.16);color:var(--er)}
nav{display:flex;gap:6px;padding:12px 20px;overflow-x:auto;max-width:1000px;margin:0 auto}
nav button{background:none;border:1px solid var(--bd);color:var(--mu);padding:8px 14px;border-radius:8px;cursor:pointer;font:inherit;white-space:nowrap}
nav button.on{background:var(--ac);border-color:var(--ac);color:#fff}
main{max-width:1000px;margin:0 auto;padding:0 20px 40px}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:12px}
.card{background:var(--card);border:1px solid var(--bd);border-radius:12px;padding:14px 16px}
.card small{display:block;color:var(--mu);font-size:12px;text-transform:uppercase;letter-spacing:.05em}
.card b{display:block;font-size:17px;font-weight:600;word-break:break-word;margin-top:2px}
.panel{background:var(--card);border:1px solid var(--bd);border-radius:12px;padding:6px 18px 18px;max-width:560px}
label{display:block;margin:14px 0 4px;color:var(--mu);font-size:13px}
.chk{display:flex;gap:8px;align-items:center}.chk input{width:auto}
input,select{width:100%;padding:10px 12px;border-radius:8px;border:1px solid var(--bd);background:var(--bg);color:var(--tx);font:inherit}
.btn{margin-top:16px;padding:10px 18px;border:0;border-radius:8px;background:var(--ac);color:#fff;font:inherit;font-weight:600;cursor:pointer}
.btn.sec{background:var(--bd);color:var(--tx);margin-top:10px}.btn.dng{background:var(--er)}
.net{display:flex;justify-content:space-between;gap:10px;width:100%;margin-top:6px;padding:10px 12px;border:1px solid var(--bd);border-radius:8px;background:var(--bg);color:var(--tx);font:inherit;text-align:left;cursor:pointer}
.mu{color:var(--mu);font-size:13px}.note{color:var(--mu);font-size:13px;margin:8px 0 0}
.msg{margin:12px 0 0;font-size:14px}.msg.ok{color:var(--ok)}.msg.err{color:var(--er)}
.banner{margin:0 0 14px;padding:10px 14px;border-radius:10px;background:rgba(245,166,35,.14);border:1px solid var(--wa);color:var(--wa)}
table{border-collapse:collapse;width:100%}td{padding:8px 4px;border-bottom:1px solid var(--bd);vertical-align:top}td:first-child{color:var(--mu);width:42%}
</style></head><body>
<header><h1 id="title">ESP32-S3 Repeater</h1><span id="badge" class="badge">Connecting...</span></header>
<nav id="nav">
<button data-p="dash" class="on">Dashboard</button><button data-p="wifi">Wi-Fi Settings</button>
<button data-p="ap">AP Settings</button><button data-p="sys">System</button>
</nav>
<main>
<div id="banner" class="banner" hidden></div>

<section id="dash" class="pg"><div class="grid" id="cards"></div></section>

<section id="wifi" class="pg" hidden>
<div class="panel">
<h2>Upstream Wi-Fi (your router)</h2>
<p class="note">The ESP32-S3 is 2.4 GHz only. Choose a 2.4 GHz network.</p>
<button class="btn sec" id="rescan" type="button">Scan networks</button>
<div id="nets"></div>
<label for="ssid">Network name (SSID)</label><input id="ssid" maxlength="32" autocomplete="off" autocapitalize="off">
<label for="pass">Password</label><input id="pass" type="password" maxlength="63" autocomplete="new-password">
<label class="chk"><input type="checkbox" id="open">Open network (no password)</label>
<p class="note" id="keepnote">Leave the password blank to keep the saved one (same SSID).</p>
<button class="btn sv" id="saveWifi" type="button">Save and restart</button>
<p class="msg" id="m_wifi"></p>
</div></section>

<section id="ap" class="pg" hidden>
<div class="panel">
<h2>Repeater network</h2>
<label for="ap_ssid">Repeater SSID</label><input id="ap_ssid" maxlength="32" value="ESP32-S3-Repeater" autocomplete="off">
<label for="ap_pass">Repeater password (8-63 characters)</label><input id="ap_pass" type="password" maxlength="63" autocomplete="new-password">
<label for="ap_adm">Dashboard admin password (8-32 characters, user: admin)</label><input id="ap_adm" type="password" maxlength="32" autocomplete="new-password">
<label for="ap_ch">Preferred AP channel</label>
<select id="ap_ch"><option value="0">Auto (follow upstream)</option></select>
<p class="note">With one radio, the repeater must use the router's channel while connected. This setting only applies while the upstream is not connected.</p>
<p class="note" id="keepnote2">Leave passwords blank to keep the saved ones.</p>
<button class="btn sv" id="saveAp" type="button">Save and restart</button>
<p class="msg" id="m_ap"></p>
</div></section>

<section id="sys" class="pg" hidden>
<div class="panel"><h2>System information</h2><table id="systbl"></table>
<h2>Maintenance</h2>
<button class="btn sec" id="btnRestart" type="button">Restart ESP32</button>
<button class="btn dng" id="btnFactory" type="button">Factory reset</button>
<p class="note">Factory reset erases all saved Wi-Fi settings and returns to setup mode. Holding the BOOT button for 10 s does the same.</p>
<p class="msg" id="m_sys"></p>
</div></section>

<div id="setupBar" hidden style="max-width:560px"><button class="btn" id="saveSetup" type="button">Save and start repeater</button><p class="msg" id="m_setup"></p></div>
</main>
<script>
const $=i=>document.getElementById(i);
let mode='';
async function api(u,o){const r=await fetch(u,o);let d={};try{d=await r.json()}catch(e){}
 if(!r.ok||d.ok===false)throw new Error(d.error||('HTTP '+r.status));return d}
const post=(u,d)=>api(u,{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded','X-Requested-With':'repeater-ui'},body:new URLSearchParams(d)});
const note=(id,t,ok)=>{const e=$(id);e.textContent=t;e.className='msg '+(ok?'ok':'err')};
const fmtUp=s=>{const d=Math.floor(s/86400),h=Math.floor(s%86400/3600),m=Math.floor(s%3600/60);return(d?d+'d ':'')+h+'h '+m+'m '+(s%60)+'s'};
const qual=r=>r>=-55?'Excellent':r>=-67?'Good':r>=-75?'Fair':'Weak';
const CARDS=[['Repeater status','state'],['Upstream SSID','staSsid'],['Upstream connection','conn'],['STA IP address','staIp'],
 ['AP IP address','apIp'],['Repeater SSID','apSsid'],['Signal strength (RSSI)','rssi'],['Channel','ch'],['Connected clients','clients'],
 ['Uptime','up'],['Free heap','heap'],['Reconnection attempts','reconn']];
CARDS.forEach(c=>{const d=document.createElement('div');d.className='card';d.innerHTML='<small></small><b id="v_'+c[1]+'">-</b>';d.firstChild.textContent=c[0];$('cards').append(d)});
const sel=$('ap_ch');for(let i=1;i<=11;i++){const o=document.createElement('option');o.value=i;o.textContent='Channel '+i;sel.append(o)}

function show(p){document.querySelectorAll('.pg').forEach(e=>e.hidden=e.id!==p);
 document.querySelectorAll('nav button').forEach(b=>b.classList.toggle('on',b.dataset.p===p));
 if(p==='wifi')scan(1);if(p==='sys')sysinfo()}
document.querySelectorAll('nav button').forEach(b=>b.onclick=()=>show(b.dataset.p));

async function scan(start){const n=$('nets');if(start)n.textContent='Scanning...';
 try{const d=await api('/api/scan'+(start?'?start=1':''));
  if(d.scanning){setTimeout(()=>scan(0),1500);return}
  n.textContent='';if(!d.networks.length){n.textContent='No networks found. Try scanning again.';return}
  d.networks.forEach(x=>{const b=document.createElement('button');b.type='button';b.className='net';
   const a=document.createElement('span');a.textContent=x.ssid;const r=document.createElement('span');r.className='mu';
   r.textContent=(x.sec?'\u{1F512} ':'')+x.rssi+' dBm ('+qual(x.rssi)+') \u00B7 ch '+x.ch;b.append(a,r);
   b.onclick=()=>{$('ssid').value=x.ssid;$('open').checked=!x.sec;$('pass').focus()};n.append(b)})
 }catch(e){n.textContent='Scan failed: '+e.message}}
$('rescan').onclick=()=>scan(1);

async function sysinfo(){try{const d=await api('/api/system');const t=$('systbl');t.textContent='';
 [['Firmware',d.fw],['Chip',d.chip+', '+d.cores+' cores @ '+d.mhz+' MHz'],['Flash',(d.flashKB/1024).toFixed(0)+' MB'],
  ['PSRAM',d.psramKB?(d.psramKB/1024).toFixed(0)+' MB':'none'],['Sketch size',d.sketchKB+' KB'],['Arduino core',d.core],['ESP-IDF',d.sdk],
  ['STA MAC',d.staMac],['AP MAC',d.apMac],['Last reset',d.reset],['Min free heap ever',(d.minHeap/1024).toFixed(0)+' KB']]
 .forEach(r=>{const tr=document.createElement('tr');r.forEach(v=>{const td=document.createElement('td');td.textContent=v;tr.append(td)});t.append(tr)})
 }catch(e){note('m_sys',e.message,0)}}

function set(id,v){$('v_'+id).textContent=v}
async function refresh(){
 try{const s=await api('/api/status');
  if(s.mode==='setup'&&mode!=='setup')initSetup();
  const b=$('badge');b.textContent=s.state;b.className='badge '+s.level;
  set('state',s.state);set('staSsid',s.staSsid||'-');set('conn',s.staUp?'Connected':'Disconnected');
  set('staIp',s.staIp);set('apIp',s.apIp);set('apSsid',s.apSsid);
  set('rssi',s.staUp?s.rssi+' dBm ('+qual(s.rssi)+')':'-');set('ch',s.ch);set('clients',s.clients);
  set('up',fmtUp(s.uptime));set('heap',Math.round(s.heap/1024)+' KB (min '+Math.round(s.minHeap/1024)+' KB)');set('reconn',s.reconn);
  const bn=$('banner');const msgs=[];if(s.err)msgs.push(s.err);if(s.memLow)msgs.push('Low memory: '+Math.round(s.heap/1024)+' KB free');
  bn.hidden=!msgs.length;bn.textContent=msgs.join(' | ');
  if(mode!=='setup'&&!window.__ch){window.__ch=1;$('ap_ch').value=s.cfgCh;$('ap_ssid').value=s.apSsid;$('ssid').value=s.staSsid}
 }catch(e){const b=$('badge');b.textContent='Offline';b.className='badge err'}}

function initSetup(){mode='setup';$('nav').hidden=true;$('dash').hidden=true;$('sys').hidden=true;$('wifi').hidden=false;$('ap').hidden=false;
 document.querySelectorAll('.sv').forEach(e=>e.hidden=true);$('keepnote').hidden=true;$('keepnote2').hidden=true;
 $('setupBar').hidden=false;$('title').textContent='ESP32-S3';scan(1)}

$('saveWifi').onclick=async()=>{try{const d=await post('/api/wifi',{ssid:$('ssid').value,pass:$('pass').value,open:$('open').checked?'1':'0'});note('m_wifi',d.msg,1)}catch(e){note('m_wifi',e.message,0)}};
$('saveAp').onclick=async()=>{try{const d=await post('/api/ap',{apssid:$('ap_ssid').value,appass:$('ap_pass').value,adminpass:$('ap_adm').value,channel:$('ap_ch').value});
 note('m_ap',d.msg+' Reconnect to "'+$('ap_ssid').value+'" afterwards.',1)}catch(e){note('m_ap',e.message,0)}};
$('saveSetup').onclick=async()=>{try{await post('/api/setup',{ssid:$('ssid').value,pass:$('pass').value,open:$('open').checked?'1':'0',
 apssid:$('ap_ssid').value,appass:$('ap_pass').value,adminpass:$('ap_adm').value,channel:$('ap_ch').value});
 note('m_setup','Saved. The ESP32 is restarting. Connect your phone or laptop to "'+$('ap_ssid').value+'", then open http://192.168.50.1/ (user: admin).',1)}catch(e){note('m_setup',e.message,0)}};
$('btnRestart').onclick=async()=>{if(confirm('Restart the ESP32 now?')){try{const d=await post('/api/restart',{});note('m_sys',d.msg,1)}catch(e){note('m_sys',e.message,0)}}};
$('btnFactory').onclick=async()=>{if(confirm('Erase ALL settings and return to setup mode?')){try{const d=await post('/api/factory',{});note('m_sys',d.msg,1)}catch(e){note('m_sys',e.message,0)}}};

refresh();setInterval(refresh,2000);
</script></body></html>)HTML";
