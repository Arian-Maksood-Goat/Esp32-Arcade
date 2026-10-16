/*
  GHOST ARCADE — GAR1 MERGED FINAL
  BASE: Claude / v3 runtime (authoritative UI, input, SD-task and boot behavior).
  EXTRA: selected VM/package validation and rendering-safety features merged in.

  MERGE CHANGELOG
  KEPT FROM BASE (authoritative; not weakened):
  - Latched PRESSED/RELEASED edges, giEndFrame(), and frame-stable MODE.
  - giSuppress launch/resume masking; reserved B+Y pause combo and pauseArmed.
  - Joystick centre auto-calibration and ADC smoothing; DEBUG_RAW_SERIAL gate.
  - CONTINUE / RESTART / MODE / LEAVE pause menu and restart-safe path handling.
  - Atomic sdEvent, syncGamesWithSd(), scanGamesKeep(), timed SD mutex waits.
  - 9-scene boot intro/Bayer dissolve, SD popup animation + frameBackup restore.
  - NVS Preferences for invert/contrast, checked canvas allocation, five-button layout.
  - Existing GAR1 opcode meanings, physics-in-.gar architecture, 16 KB package ceiling.

  MERGED FROM EXTRA (backward-compatible additions):
  - Full GAR1 package/AST1 validation at launch; lightweight structural validation
    during game scan so browsing does not malloc every package at full size.
  - Instruction-boundary bitmap and guarded JMP/JZ/CALL targets.
  - Optional ENTER/LOADL/STOREL per-call locals; legacy games need no ENTER.
  - Per-frame rendering-work budget, clipped pixel/rectangle/line/sprite drawing,
    and deterministic fixed-point/shift helpers.
  - 96-byte game paths, path-too-long and 48-game overflow reporting.
  - ESP32 DevKit V1 / passive ESP32-CAM SD-adapter wiring notes and GPIO5 warning.

  CONFLICT RESOLUTION:
  - BASE runtime/input/SD synchronization/pause/boot/UI logic wins over EXTRA.
  - No GAR2 format, no changed opcode meanings, no game mechanics in firmware.
  - Game-specific movement, collision rules, AI, scoring and level logic remain in .gar.

  Libraries (Arduino Library Manager): Adafruit GFX Library, Adafruit SH110X.

  HOST BOARD: classic ESP32 DevKit V1. Passive adapter pad labels are NOT host GPIOs.
  OLED I2C: SDA 21, SCL 22
  Joystick: VRx 34, VRy 35, SW 33 (switch to GND)
  Buttons : A 25, B 26, X 13, Y 27 (switch to GND)
  SD SPI  : SCK 18, MISO 19, MOSI 23, CS 5
  Adapter pads: host GPIO18 -> adapter GPIO14 (CLK), GPIO19 -> GPIO2 (DAT0/MISO),
                host GPIO23 -> GPIO15 (CMD/MOSI), GPIO5 -> GPIO13 (DAT3/CS).
  GPIO5 is a classic ESP32 strapping pin: verify CS is not forced LOW during reset.
  This is a DevKit-host pin map, not a pin map for using ESP32-CAM as the host.
*/

#include <Arduino.h>
#include <Wire.h>
#include <SPI.h>
#include <SD.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SH110X.h>
#include <math.h>
#include <string.h>
#include <atomic>
#include <new>
#include <Preferences.h>
#include <esp_log.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <freertos/semphr.h>

// ---------- Pin map ----------
static constexpr int PIN_OLED_SDA = 21;
static constexpr int PIN_OLED_SCL = 22;

static constexpr int PIN_JOY_X = 34;
static constexpr int PIN_JOY_Y = 35;
static constexpr int PIN_JOY_SW = 33;

static constexpr int PIN_BUTTON_A = 25;
static constexpr int PIN_BUTTON_B = 26;
static constexpr int PIN_BUTTON_X = 13;
static constexpr int PIN_BUTTON_Y = 27;

static constexpr int PIN_SD_SCK  = 18;
static constexpr int PIN_SD_MISO = 19;
static constexpr int PIN_SD_MOSI = 23;
static constexpr int PIN_SD_CS   = 5;

static constexpr uint8_t  OLED_ADDRESS = 0x3C;
static constexpr uint32_t FRAME_INTERVAL_MS = 33;
static constexpr uint32_t DEBOUNCE_MS = 25;
static constexpr uint32_t LONG_PRESS_MS = 700;
static constexpr uint32_t PAUSE_HOLD_MS = 600;   // hold B+Y this long to pause

static constexpr uint16_t C_ON  = 1;   // SH110X_WHITE
static constexpr uint16_t C_OFF = 0;   // SH110X_BLACK
static constexpr float PI_F = 3.14159265f;

Adafruit_SH1106G display(128, 64, &Wire, -1);
SPIClass sdSPI(VSPI);

// Off-screen buffers used only for boot dissolve transitions.
GFXcanvas1 *cvA = nullptr;
GFXcanvas1 *cvB = nullptr;

// ---------- Input manager ----------
enum ButtonId : uint8_t { BTN_A, BTN_B, BTN_X, BTN_Y, BTN_JOY, BTN_COUNT };

struct ButtonState {
  uint8_t pin;
  ButtonState(uint8_t p = 0) : pin(p) {}
  bool down = false;
  bool pressed = false;
  bool released = false;
  bool rawLast = false;
  bool stableLast = false;
  uint32_t rawChangedAt = 0;
  uint32_t pressedAt = 0;
};

ButtonState buttons[BTN_COUNT] = {
  {PIN_BUTTON_A}, {PIN_BUTTON_B}, {PIN_BUTTON_X},
  {PIN_BUTTON_Y}, {PIN_JOY_SW}
};

int joyX = 2048, joyY = 2048;
int joyCenX = 2048, joyCenY = 2048;   // calibrated in setup()

bool displayReady = false;
bool invertDisplay = false;
uint8_t contrastValue = 180;
Preferences prefs;                  // NVS: display settings survive reboot
bool prefsReady = false;
#define DEBUG_RAW_SERIAL 0          // 1 = print raw inputs to Serial every 250 ms

void saveDisplayPrefs() {
  if (!prefsReady) return;
  prefs.putBool("inv", invertDisplay);
  prefs.putUChar("ctr", contrastValue);
}
const bool audioPresent = false;   // set true when audio hardware is added

// ---------- SD state (written by the SD task, read by the UI) ----------
volatile bool sdReady = false;
std::atomic<int8_t> sdEvent{0};            // +1 connected, -1 removed (consumed by UI)
SemaphoreHandle_t sdMutex = nullptr;    // take this around ANY future SD file access

static constexpr uint8_t SD_MOUNT_TRIES = 3;   // mount attempts inside one check
static constexpr uint8_t SD_FAIL_LIMIT  = 2;   // consecutive failed checks = removed

static constexpr uint32_t SD_SPI_HZ          = 1000000;  // slow = reliable on jumper wires
static constexpr uint32_t SD_LOCK_TIMEOUT_MS = 1500;     // UI never waits longer than this

int8_t sdListChange = 0;      // +1 / -1 set by pollSdEvents, handled by syncGamesWithSd
bool showSdPopup = false;
int8_t sdPopupKind = 0;
uint32_t sdPopupStartedAt = 0;
static constexpr uint32_t POPUP_MS = 3200;
static constexpr uint32_t POPUP_IN_MS = 450;
static constexpr uint32_t POPUP_OUT_MS = 450;

void updateInputs() {
  uint32_t now = millis();
  for (int i = 0; i < BTN_COUNT; ++i) {
    ButtonState &b = buttons[i];
    b.pressed = false;
    b.released = false;
    bool rawDown = (digitalRead(b.pin) == LOW);
    if (rawDown != b.rawLast) {
      b.rawLast = rawDown;
      b.rawChangedAt = now;
    }
    if ((now - b.rawChangedAt) >= DEBOUNCE_MS && b.stableLast != rawDown) {
      b.stableLast = rawDown;
      b.down = rawDown;
      if (rawDown) {
        b.pressed = true;
        b.pressedAt = now;
      } else {
        b.released = true;
      }
    } else {
      b.down = b.stableLast;
    }
  }
  joyX = (joyX + analogRead(PIN_JOY_X)) / 2;   // light smoothing (ESP32 ADC is noisy)
  joyY = (joyY + analogRead(PIN_JOY_Y)) / 2;
}

bool down(ButtonId id) { return buttons[id].down; }
bool pressed(ButtonId id) { return buttons[id].pressed; }
bool released(ButtonId id) { return buttons[id].released; }
bool anyPressed() {
  for (int i = 0; i < BTN_COUNT; ++i) if (buttons[i].pressed) return true;
  return false;
}
bool longPressed(ButtonId id) {
  return down(id) && (millis() - buttons[id].pressedAt >= LONG_PRESS_MS);
}

// ---------- SD background task ----------
static bool sdMountOnce() {
  if (!SD.begin(PIN_SD_CS, sdSPI, SD_SPI_HZ)) return false;
  if (SD.cardType() == CARD_NONE) return false;
  return true;
}

// Several mount attempts so one noisy init does not count as a failure.
static bool sdMountRetry() {
  for (uint8_t i = 0; i < SD_MOUNT_TRIES; ++i) {
    if (sdMountOnce()) return true;
    SD.end();
    vTaskDelay(pdMS_TO_TICKS(60));
  }
  return false;
}

void sdTask(void *) {
  uint8_t failCount = 0;

  // First probe at boot: silent (no popup).
  xSemaphoreTake(sdMutex, portMAX_DELAY);
  bool ok = sdMountRetry();
  if (!ok) SD.end();
  sdReady = ok;
  xSemaphoreGive(sdMutex);

  for (;;) {
    vTaskDelay(pdMS_TO_TICKS(sdReady ? 2000 : 1000));

    xSemaphoreTake(sdMutex, portMAX_DELAY);
    if (sdReady) {
      // Re-mount = real hardware check. Only N consecutive failures = removed.
      SD.end();
      if (sdMountRetry()) {
        failCount = 0;
      } else {
        SD.end();
        if (++failCount >= SD_FAIL_LIMIT) {
          sdReady = false;
          sdEvent = -1;
          failCount = 0;
          Serial.println(F("SD card removed."));
        } else {
          Serial.println(F("SD check failed once (ignored)."));
        }
      }
    } else {
      if (sdMountRetry()) {
        sdReady = true;
        sdEvent = 1;
        failCount = 0;
        Serial.println(F("SD card connected."));
      } else {
        SD.end();
      }
    }
    xSemaphoreGive(sdMutex);
  }
}

void pollSdEvents() {
  const int8_t ev = sdEvent.exchange(0);       // atomic read-and-clear (no lost events)
  if (ev != 0) {
    sdPopupKind = ev;
    sdPopupStartedAt = millis();
    showSdPopup = true;
    sdListChange = ev;
  }
}

// Forward declarations (defined further down)
void garStop();
bool garLoad(const char *path);
void renderScreen();
void drawSdPopup();
void giEndFrame();

// ---------- Game discovery + Pause state (must be before scanGames) ----------
static constexpr uint8_t MAX_GAMES = 48;       // soft cap; list is paginated in UI
static constexpr uint8_t GAME_NAME_LEN = 18;    // fits 128px with "> "
static constexpr size_t GAME_PATH_LEN = 96;
struct GameEntry {
  char name[GAME_NAME_LEN];
  char path[GAME_PATH_LEN];
};

// Use only primitive/pointer parameters here: Arduino's .ino preprocessor may
// emit this function's prototype before the GameEntry definition.
static bool garMakeGameEntry(const char *reportedName,
                             char *outName, size_t outNameSize,
                             char *outPath, size_t outPathSize) {
  if (!reportedName || !outName || !outPath || outNameSize == 0 || outPathSize == 0) return false;
  const char *fileName = strrchr(reportedName, '/');
  fileName = fileName ? fileName + 1 : reportedName;
  const size_t fileNameLen = strlen(fileName);
  if (fileNameLen < 5u) return false;
  const char *ext = fileName + fileNameLen - 4u;
  if (ext[0] != '.' || (ext[1] | 32) != 'g' || (ext[2] | 32) != 'a' || (ext[3] | 32) != 'r') return false;
  const int pathLen = snprintf(outPath, outPathSize, "/GAMES/%s", fileName);
  if (pathLen <= 0 || (size_t)pathLen >= outPathSize) return false;
  size_t displayLen = fileNameLen - 4u;
  if (displayLen >= outNameSize) displayLen = outNameSize - 1u;
  memcpy(outName, fileName, displayLen);
  outName[displayLen] = '\0';
  return true;
}
bool gameListTruncated = false;   // true if more .gar files exist than MAX_GAMES
bool gameScanPathSkipped = false; // true if a valid .gar has a filename too long for our path buffer
GameEntry gameList[MAX_GAMES];
uint8_t gameCount = 0;
uint8_t gameSelection = 0;
uint8_t gameScroll = 0;
char currentGameTitle[GAME_NAME_LEN] = "GAME";
char currentGamePath[GAME_PATH_LEN] = "";
uint8_t pauseSelection = 0;   // 0 CONTINUE 1 RESTART 2 MODE 3 LEAVE
bool    garPaused = false;
volatile bool garModeRequested = false;
bool    garSwallowInput = false;  // clear one frame of edges after pause menu

static constexpr size_t GAME_FILE_MAX = 16384;
static constexpr uint8_t GAR_MAX_SPRITES = 32;

// Fast, allocation-free scan validation: header/codeLen and the optional AST1
// framing must match the exact file size. Full bytecode validation happens on load.
static bool garValidateFileStructure(File &f, size_t sz) {
  if (sz < 7 || sz > GAME_FILE_MAX || !f.seek(0)) return false;
  uint8_t hdr[6];
  if (f.read(hdr, sizeof(hdr)) != (int)sizeof(hdr)) return false;
  if (memcmp(hdr, "GAR1", 4) != 0) return false;
  const uint16_t codeLen = (uint16_t)(hdr[4] | ((uint16_t)hdr[5] << 8));
  if (codeLen == 0 || (size_t)codeLen > sz - 6u) return false;
  const size_t assetOff = 6u + (size_t)codeLen;
  if (assetOff == sz) return true;  // legacy GAR1 package, no assets
  if (sz - assetOff < 5u || !f.seek((uint32_t)assetOff)) return false;
  uint8_t ah[5];
  if (f.read(ah, sizeof(ah)) != (int)sizeof(ah) || memcmp(ah, "AST1", 4) != 0) return false;
  const uint8_t count = ah[4];
  if (count > GAR_MAX_SPRITES) return false;
  bool used[GAR_MAX_SPRITES] = {false};
  size_t pos = assetOff + 5u;
  for (uint8_t i = 0; i < count; ++i) {
    if (pos > sz || sz - pos < 3u || !f.seek((uint32_t)pos)) return false;
    uint8_t rec[3];
    if (f.read(rec, sizeof(rec)) != (int)sizeof(rec)) return false;
    const uint8_t id = rec[0], w = rec[1], h = rec[2];
    if (id >= GAR_MAX_SPRITES || used[id] || w == 0 || h == 0 || w > 128 || h > 64) return false;
    used[id] = true;
    const size_t nbytes = (((size_t)w + 7u) / 8u) * (size_t)h;
    pos += 3u;
    if (pos > sz || nbytes > sz - pos) return false;
    pos += nbytes;
  }
  return pos == sz;
}

// Scan /GAMES/ for valid .gar packages. Takes sdMutex itself (with a timeout).
// keepSelection = true re-highlights the previously selected game if it still exists.
static void scanGamesImpl(bool keepSelection) {
  char keepPath[GAME_PATH_LEN] = {0};
  if (keepSelection && gameSelection < gameCount) {
    snprintf(keepPath, sizeof(keepPath), "%s", gameList[gameSelection].path);
  }

  gameCount = 0;
  gameSelection = 0;
  gameScroll = 0;
  gameListTruncated = false;
  gameScanPathSkipped = false;
  if (!sdReady || !sdMutex) return;

  if (xSemaphoreTake(sdMutex, pdMS_TO_TICKS(SD_LOCK_TIMEOUT_MS)) != pdTRUE) return;
  if (!sdReady) { xSemaphoreGive(sdMutex); return; }

  File dir = SD.open("/GAMES");
  if (!dir || !dir.isDirectory()) {
    if (dir) dir.close();
    xSemaphoreGive(sdMutex);
    return;
  }

  for (File f = dir.openNextFile(); f; f = dir.openNextFile()) {
    if (f.isDirectory()) { f.close(); continue; }
    // File::name() can point into File-owned storage: use it only before close.
    const char *nm = f.name();
    const char *slash = nm ? strrchr(nm, '/') : nullptr;
    const char *fileName = slash ? slash + 1 : (nm ? nm : "");
    const size_t nameLen = strlen(fileName);
    if (nameLen < 5u || fileName[0] == '.') { f.close(); continue; }
    const char *ext = fileName + nameLen - 4u;
    if (ext[0] != '.' || (ext[1] | 32) != 'g' || (ext[2] | 32) != 'a' || (ext[3] | 32) != 'r') {
      f.close(); continue;
    }
    if (nameLen + 8u > GAME_PATH_LEN) {
      gameScanPathSkipped = true;
      Serial.printf("Skipping .gar with path too long: %s\n", fileName);
      f.close();
      continue;
    }

    const size_t sz = f.size();
    if (!garValidateFileStructure(f, sz)) { f.close(); continue; }

    GameEntry entry;
    if (!garMakeGameEntry(fileName, entry.name, sizeof(entry.name), entry.path, sizeof(entry.path))) {
      gameScanPathSkipped = true;
      Serial.printf("Skipping .gar with path too long/invalid: %s\n", fileName);
      f.close();
      continue;
    }
    f.close();

    if (gameCount >= MAX_GAMES) {
      gameListTruncated = true;
      continue;
    }
    gameList[gameCount++] = entry;
  }
  dir.close();
  xSemaphoreGive(sdMutex);

  // Alphabetical sort (case-insensitive).
  for (uint8_t i = 0; i + 1 < gameCount; ++i) {
    for (uint8_t j = i + 1; j < gameCount; ++j) {
      if (strcasecmp(gameList[i].name, gameList[j].name) > 0) {
        GameEntry tmp = gameList[i];
        gameList[i] = gameList[j];
        gameList[j] = tmp;
      }
    }
  }

  // Preserve selected full path across rescans and SD reinsertion.
  if (keepPath[0]) {
    for (uint8_t i = 0; i < gameCount; ++i) {
      if (strcmp(gameList[i].path, keepPath) == 0) { gameSelection = i; break; }
    }
  }
}
void scanGames()     { scanGamesImpl(false); }
void scanGamesKeep() { scanGamesImpl(true);  }

// ---------- UI state ----------
enum Screen : uint8_t {
  SCREEN_BOOT, SCREEN_HOME, SCREEN_GAMES, SCREEN_SETTINGS, SCREEN_RAW,
  SCREEN_DIAGNOSTICS, SCREEN_ABOUT, SCREEN_DISPLAY, SCREEN_GAME, SCREEN_PAUSE
};
Screen screen = SCREEN_BOOT;
Screen previousScreen = SCREEN_SETTINGS;
uint32_t bootStartedAt = 0;
uint32_t lastFrameAt = 0;
uint32_t lastRawAt = 0;
uint8_t homeSelection = 0;
uint8_t settingsSelection = 0;
uint8_t displaySelection = 0;
uint8_t aboutScroll = 0;
bool longPressHandled = false;
int8_t latchedNavDir = 0;
uint32_t navRepeatAt = 0;
const int JOY_NAV_ENTER = 900;
const int JOY_NAV_EXIT = 550;
const uint32_t JOY_NAV_REPEAT_MS = 260;

const char *homeItems[] = {"Games", "Settings", "About"};
const uint8_t HOME_COUNT = sizeof(homeItems) / sizeof(homeItems[0]);
const char *settingsItems[] = {"Raw Value", "Diagnostics", "Display", "About"};
const uint8_t SETTINGS_COUNT = sizeof(settingsItems) / sizeof(settingsItems[0]);

// About text: every line must be <= 19 characters (6 px per char, scrollbar at x=123).
static const char *const aboutLines[] = {
  "GHOST ARCADE",
  "ESP32 retro console",
  "GAR1 + sprites",
  "OLED: SH1106 128x64",
  "Stick + A/B",
  "Pause: hold B+Y",
  "Games from /GAMES",
  "No reflash needed"
};
static constexpr uint8_t ABOUT_LINE_COUNT = sizeof(aboutLines) / sizeof(aboutLines[0]);
static constexpr uint8_t ABOUT_VISIBLE    = 4;
static constexpr uint8_t ABOUT_MAX_SCROLL = ABOUT_LINE_COUNT - ABOUT_VISIBLE;

// Keep the Games list honest when the card disappears / comes back.
void syncGamesWithSd() {
  if (sdListChange == 0) return;
  const int8_t ev = sdListChange;
  sdListChange = 0;
  if (ev < 0) {
    gameCount = 0; gameSelection = 0; gameScroll = 0; gameListTruncated = false; gameScanPathSkipped = false;
  } else if (screen == SCREEN_GAMES) {
    scanGamesKeep();
  }
}

// ---------- Generic drawing helpers (work on display or canvas) ----------
void gText(Adafruit_GFX &g, int x, int y, const char *s, uint8_t size = 1) {
  g.setTextSize(size);
  g.setTextColor(C_ON);
  g.setCursor(x, y);
  g.print(s);
}

void drawHeader(const char *title) {
  display.setTextSize(1);
  display.setTextColor(C_ON);
  display.setCursor(2, 1);
  display.print(title);
  display.drawLine(0, 11, 127, 11, C_ON);
}

void drawFooterG(Adafruit_GFX &g, const char *hint) {
  g.drawLine(0, 55, 127, 55, C_ON);
  g.setTextSize(1);
  g.setTextColor(C_ON);
  g.setCursor(2, 57);
  g.print(hint);
}
void drawFooter(const char *hint) { drawFooterG(display, hint); }

// One-off message for slow (blocking) operations such as scanning the SD card.
void showBusy(const char *msg) {
  if (!displayReady) return;
  display.clearDisplay();
  display.setTextSize(1);
  display.setTextColor(C_ON);
  display.setCursor((128 - (int)strlen(msg) * 6) / 2, 28);
  display.print(msg);
  display.display();
}

// Small ghost used on the Home screen.
void drawHomeGhost(Adafruit_GFX &g, int cx, int cy, int frame) {
  int w = 14, h = 14;
  int x = cx - w / 2;
  int y = cy - h / 2;
  g.fillRoundRect(x, y, w, h - 3, 4, C_ON);
  g.fillRect(x, y + h / 2, w, h / 2 - 2, C_ON);
  int scallopW = 4;
  for (int sx = x; sx < x + w; sx += scallopW) {
    int offset = ((sx / scallopW + frame) % 2) ? 2 : 0;
    g.fillCircle(sx + scallopW / 2, y + h - 3 + offset, scallopW / 2, C_ON);
  }
  g.fillCircle(cx - 3, y + 5, 1, C_OFF);
  g.fillCircle(cx + 3, y + 5, 1, C_OFF);
}

// =====================================================================
//  BOOT ANIMATION  (9 panels from the reference image)
// =====================================================================

// 16x16 outline ghost (X = outline, E = eye)
const char *const GHOST_BODY[14] = {
  "....XXXXXXXX....",
  "..XXX......XXX..",
  ".XX..........XX.",
  ".X............X.",
  "XX............XX",
  "X..............X",
  "X...EE....EE...X",
  "X...EE....EE...X",
  "X...EE....EE...X",
  "X..............X",
  "X..............X",
  "X..............X",
  "X..............X",
  "X..............X"
};
const char *const GHOST_FEET[2][2] = {
  {"XX..XX....XX..XX", ".XXX..XXXX..XXX."},
  {"X.XX..XX..XX..XX", ".X..XX..XX..XX.."}
};

void drawGhost16(Adafruit_GFX &g, int x, int y, uint8_t frame, bool filled) {
  const char *rows[16];
  for (int i = 0; i < 14; ++i) rows[i] = GHOST_BODY[i];
  rows[14] = GHOST_FEET[frame & 1][0];
  rows[15] = GHOST_FEET[frame & 1][1];

  if (filled) {
    for (int c = 0; c < 16; ++c) {
      int top = -1, bot = -1;
      for (int r = 0; r < 16; ++r) {
        if (rows[r][c] != '.') { if (top < 0) top = r; bot = r; }
      }
      if (top >= 0) g.drawFastVLine(x + c, y + top, bot - top + 1, C_ON);
    }
  }
  for (int r = 0; r < 16; ++r) {
    for (int c = 0; c < 16; ++c) {
      char ch = rows[r][c];
      if (ch == 'X') g.drawPixel(x + c, y + r, C_ON);
      else if (ch == 'E') g.drawPixel(x + c, y + r, filled ? C_OFF : C_ON);
    }
  }
}

void sceneFrame(Adafruit_GFX &g) {
  g.fillScreen(C_OFF);
  g.drawRoundRect(1, 1, 126, 62, 4, C_ON);
}

void bootStars(Adafruit_GFX &g, uint32_t t, int ax, int ay, int aw, int ah) {
  for (int i = 0; i < 18; ++i) {
    int x = 7 + ((i * 43) % 113);
    int y = 6 + ((i * 29) % 48);
    if (x >= ax && x < ax + aw && y >= ay && y < ay + ah) continue;
    if (((t / 180) + i) % 4 == 0) continue;
    g.drawPixel(x, y, C_ON);
    if (i % 6 == 0) {
      g.drawPixel(x - 1, y, C_ON); g.drawPixel(x + 1, y, C_ON);
      g.drawPixel(x, y - 1, C_ON); g.drawPixel(x, y + 1, C_ON);
    }
  }
}

float smooth01(float p) {
  if (p < 0) p = 0;
  if (p > 1) p = 1;
  return p * p * (3.0f - 2.0f * p);
}

// 1: ghost idle with twinkling stars
void sceneIdle(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  bootStars(g, t, 50, 18, 28, 28);
  int bob = (int)(1.5f * sinf(t * 0.009f));
  drawGhost16(g, 56, 24 + bob, (t / 160) & 1, false);
}

// 2: ghost dashes right with speed lines
void sceneDash(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  bootStars(g, t, 0, 0, 0, 0);
  float p = (t > 500) ? 1.0f : t / 500.0f;
  float e = smooth01(p);
  int gx = 10 + (int)(86.0f * e);
  const int gy = 24;
  float v = sinf(p * PI_F);                 // 0 -> 1 -> 0 speed profile
  static const uint8_t L[6] = {40, 22, 34, 16, 44, 28};
  static const uint8_t O[6] = {0, 4, 1, 6, 2, 5};
  for (int k = 0; k < 6; ++k) {
    int y = gy + 2 + k * 2;
    int len = (int)(L[k] * (0.2f + 0.8f * v));
    int x1 = gx - 3 - O[k];
    int x0 = x1 - len;
    if (x0 < 6) x0 = 6;
    if (x1 > x0) g.drawFastHLine(x0, y, x1 - x0, C_ON);
  }
  drawGhost16(g, gx, gy, (t / 90) & 1, false);
}

// 3: filled ghost with radiating rays
void sceneBurst(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  float grow = smooth01(t / 220.0f);
  float pulse = 0.5f + 0.5f * sinf(t * 0.02f);
  const int rays = 20;
  for (int i = 0; i < rays; ++i) {
    float a = i * (2.0f * PI_F / rays);
    float ca = cosf(a), sa = sinf(a);
    int r0 = 14 + ((i & 1) ? 3 : 0);
    int len = (int)((10 + (i % 4) * 9 + 8 * pulse) * grow);
    for (int r = r0; r < r0 + len; ++r) {
      if (((r + i) % 6) >= 4) continue;
      int px = 64 + (int)(ca * r * 1.8f);
      int py = 32 + (int)(sa * r);
      if (px < 4 || px > 123 || py < 4 || py > 59) break;
      g.drawPixel(px, py, C_ON);
    }
  }
  g.fillRect(52, 20, 24, 24, C_OFF);                // clear halo behind ghost
  drawGhost16(g, 56, 24, (t / 110) & 1, true);
}

// Title helpers
void drawTitle(Adafruit_GFX &g, int gy, int ay, int nG, int nA) {
  static const char TG[] = "GHOST";
  static const char TA[] = "ARCADE";
  g.setTextSize(2);
  g.setTextColor(C_ON);
  for (int i = 0; i < nG && i < 5; ++i) {
    g.setCursor(35 + i * 12, gy);     g.print(TG[i]);
    g.setCursor(36 + i * 12, gy);     g.print(TG[i]);     // faux-bold
  }
  if (nG > 0) g.drawFastHLine(35, gy + 8, nG * 12 + 1, C_OFF);  // scanline cut
  g.setTextSize(1);
  for (int i = 0; i < nA && i < 6; ++i) {
    g.setCursor(41 + i * 8, ay);
    g.print(TA[i]);
  }
}

void sideDashes(Adafruit_GFX &g, int y, int w) {
  if (w < 1) return;
  g.drawFastHLine(29 - w, y, w, C_ON);
  g.drawFastHLine(99, y, w, C_ON);
  int w2 = w / 2;
  if (w2 > 0) {
    g.drawFastHLine(29 - w2, y - 3, w2, C_ON);
    g.drawFastHLine(99, y - 3, w2, C_ON);
    g.drawFastHLine(29 - w2, y + 3, w2, C_ON);
    g.drawFastHLine(99, y + 3, w2, C_ON);
  }
}

// 4: GHOST title types in, ARCADE follows
void sceneTitle1(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  int nG = 1 + (int)(t / 60);
  int nA = (t > 260) ? (int)((t - 260) / 45) : 0;
  drawTitle(g, 18, 38, nG, nA);
  sideDashes(g, 26, (int)(20.0f * smooth01(t / 300.0f)));
}

// 5: title + lines under/around ARCADE
void sceneTitle2(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  drawTitle(g, 18, 38, 5, 6);
  sideDashes(g, 26, 20);
  int w = (int)(18.0f * smooth01(t / 300.0f));
  if (w > 0) {
    g.drawFastHLine(38 - w, 41, w, C_ON);
    g.drawFastHLine(90, 41, w, C_ON);
  }
}

// 6: title rises, mountains + moon + water
void sceneTitle3(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  float slide = smooth01(t / 260.0f);
  int gy = 18 - (int)(10.0f * slide);
  int ay = 38 - (int)(13.0f * slide);
  bootStars(g, t, 0, 0, 0, 0);
  g.fillRect(30, gy - 2, 70, 34, C_OFF);          // keep title area clean of stars
  drawTitle(g, gy, ay, 5, 6);

  // Moon
  g.drawCircle(110, 14, 5, C_ON);
  g.fillCircle(110, 14, 3, C_ON);

  // Mountains rise from the horizon
  float rise = smooth01((t > 150 ? t - 150 : 0) / 400.0f);
  auto my = [&](int y) { return 50 - (int)((50 - y) * rise); };
  g.drawLine(3, 50, 15, my(36), C_ON);   g.drawLine(15, my(36), 26, 50, C_ON);
  g.drawLine(22, 50, 31, my(42), C_ON);  g.drawLine(31, my(42), 40, 50, C_ON);
  g.drawLine(88, 50, 97, my(42), C_ON);  g.drawLine(97, my(42), 106, 50, C_ON);
  g.drawLine(100, 50, 112, my(35), C_ON);g.drawLine(112, my(35), 124, 50, C_ON);
  g.drawFastHLine(4, 50, 120, C_ON);

  // Shimmering water
  for (int k = 0; k < 4; ++k) {
    int y = 52 + k * 2;
    for (int x = 8; x < 118; x += 7) {
      if ((((x / 7) + (int)(t / 110) + k) % 3) == 0) continue;
      g.drawFastHLine(x, y, 5, C_ON);
    }
  }
}

void drawIsland(Adafruit_GFX &g, uint32_t t) {
  float p = smooth01(t / 700.0f);
  int sx = 108;
  int sy = 47 + (int)(11.0f * (1.0f - p));
  g.fillCircle(sx, sy, 9, C_ON);
  g.fillRect(sx - 10, 49, 22, 12, C_OFF);
  for (int k = 0; k < 4; ++k) {
    int y = 50 + k * 3;
    int off = (int)(2.0f * sinf(t * 0.01f + k));
    g.drawFastHLine(84 + ((k & 1) ? 3 : 0) + off, y, 34 - k * 4, C_ON);
  }
  g.fillTriangle(82, 50, 98, 50, 89, 45, C_ON);
  g.drawLine(89, 45, 91, 36, C_ON);
  g.drawLine(91, 36, 84, 37, C_ON);
  g.drawLine(91, 36, 86, 33, C_ON);
  g.drawLine(91, 36, 97, 37, C_ON);
  g.drawLine(91, 36, 96, 33, C_ON);
  g.drawLine(91, 36, 91, 32, C_ON);
  // birds
  g.drawLine(98, 22, 100, 24, C_ON); g.drawLine(100, 24, 102, 22, C_ON);
  g.drawLine(106, 27, 108, 29, C_ON); g.drawLine(108, 29, 110, 27, C_ON);
}

// 7: SYSTEM INIT
void sceneInit(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  g.setTextSize(1);
  g.setTextColor(C_ON);
  g.setCursor(8, 6);
  g.print("SYSTEM INIT");
  int d = (t / 140) % 4;
  for (int i = 0; i < d; ++i) g.print('.');

  const char *names[5] = {"DISPLAY", "SD CARD", "INPUT", "AUDIO", "READY"};
  bool ok[5] = {displayReady, (bool)sdReady, true, audioPresent, true};
  for (int k = 0; k < 5; ++k) {
    uint32_t at = 120 + k * 120;
    if (t < at) break;
    int y = 18 + k * 8;
    g.setCursor(8, y);  g.print("> ");
    g.setCursor(20, y); g.print(names[k]);
    if (t >= at + 70) {
      g.setCursor(68, y);
      g.print(ok[k] ? "OK" : "--");
    }
  }
  drawIsland(g, t);
}

// 8: LOADING GAMES
void sceneLoading(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  gText(g, 16, 18, "LOADING GAMES...");
  g.drawRoundRect(20, 31, 88, 12, 3, C_ON);
  int filled = (int)((t * 11UL) / 700UL);
  if (filled > 10) filled = 10;
  for (int i = 0; i < filled; ++i) g.fillRect(23 + i * 8, 34, 7, 6, C_ON);
}

// 9: SYSTEM READY
void sceneReady(Adafruit_GFX &g, uint32_t t) {
  sceneFrame(g);
  int slide = (int)(6.0f * (1.0f - smooth01(t / 250.0f)));
  g.fillTriangle(16 - slide, 14, 16 - slide, 22, 22 - slide, 18, C_ON);
  g.fillTriangle(112 + slide, 14, 112 + slide, 22, 106 + slide, 18, C_ON);
  gText(g, 28, 14, "SYSTEM READY");

  int w = (int)(30.0f * smooth01(t / 350.0f));
  g.drawFastHLine(50 - w, 36, w, C_ON);  g.drawFastHLine(78, 36, w, C_ON);
  g.drawFastHLine(50 - w / 2, 39, w / 2, C_ON); g.drawFastHLine(78, 39, w / 2, C_ON);
  g.drawFastHLine(50 - w, 42, w, C_ON);  g.drawFastHLine(78, 42, w, C_ON);

  // Gamepad icon
  g.drawRoundRect(52, 31, 24, 14, 6, C_ON);
  g.drawFastHLine(56, 38, 7, C_ON);
  g.drawFastVLine(59, 35, 7, C_ON);
  bool blink = ((t / 180) & 1);
  g.fillCircle(68, 36, 1, C_ON);
  g.fillCircle(71, 39, 1, C_ON);
  if (blink) g.drawPixel(68, 36, C_OFF);
  else g.drawPixel(71, 39, C_OFF);
  g.drawLine(54, 44, 52, 48, C_ON);  g.drawLine(74, 44, 76, 48, C_ON);
}

void drawHome(Adafruit_GFX &g);

static constexpr int BOOT_SCENES = 9;
static constexpr uint16_t SCENE_MS[BOOT_SCENES] = {500, 500, 550, 500, 500, 650, 900, 800, 800};
static constexpr uint32_t TRANS_MS = 220;

void drawScene(Adafruit_GFX &g, int idx, uint32_t t) {
  switch (idx) {
    case 0: sceneIdle(g, t); break;
    case 1: sceneDash(g, t); break;
    case 2: sceneBurst(g, t); break;
    case 3: sceneTitle1(g, t); break;
    case 4: sceneTitle2(g, t); break;
    case 5: sceneTitle3(g, t); break;
    case 6: sceneInit(g, t); break;
    case 7: sceneLoading(g, t); break;
    case 8: sceneReady(g, t); break;
    default: drawHome(g); break;     // 9 = Home (final dissolve target)
  }
}

static const uint8_t BAYER4[4][4] = {
  {0, 8, 2, 10}, {12, 4, 14, 6}, {3, 11, 1, 9}, {15, 7, 13, 5}
};

void drawBoot() {
  const uint32_t el = millis() - bootStartedAt;

  uint32_t total = 0;
  for (int i = 0; i < BOOT_SCENES; ++i) total += SCENE_MS[i];
  if (el >= total) { screen = SCREEN_HOME; drawHome(display); return; }   // key-skip handled in loop()

  // Find current scene i; 'end' is the time its slot finishes.
  uint32_t end = 0;
  int i = 0;
  for (; i < BOOT_SCENES; ++i) {
    end += SCENE_MS[i];
    if (el < end) break;
  }
  const int32_t startI = (i == 0) ? 0 : (int32_t)(end - SCENE_MS[i]) - (int32_t)TRANS_MS;
  const int32_t startNext = (int32_t)end - (int32_t)TRANS_MS;

  if ((int32_t)el >= startNext && cvA && cvB) {
    // Dither dissolve from scene i to scene i+1 (or Home after the last one).
    float p = smooth01((float)((int32_t)el - startNext) / (float)TRANS_MS);
    int thr = (int)(p * 16.99f);
    drawScene(*cvA, i, (uint32_t)((int32_t)el - startI));
    drawScene(*cvB, i + 1, (uint32_t)((int32_t)el - startNext));
    display.clearDisplay();
    for (int y = 0; y < 64; ++y) {
      for (int x = 0; x < 128; ++x) {
        bool useB = BAYER4[y & 3][x & 3] < thr;
        if ((useB ? cvB : cvA)->getPixel(x, y)) display.drawPixel(x, y, C_ON);
      }
    }
  } else {
    drawScene(display, i, (uint32_t)((int32_t)el - startI));
  }
}

// =====================================================================
//  Screens
// =====================================================================
void drawHome(Adafruit_GFX &g) {
  g.fillScreen(C_OFF);
  drawHomeGhost(g, 14, 7, (millis() / 250) % 4);
  gText(g, 25, 3, "GHOST ARCADE");
  g.drawLine(0, 16, 127, 16, C_ON);

  for (uint8_t i = 0; i < HOME_COUNT; ++i) {
    int y = 22 + i * 10;
    g.setCursor(i == homeSelection ? 17 : 25, y);
    g.print(i == homeSelection ? ">" : " ");
    g.print(" ");
    g.print(homeItems[i]);
  }
  drawFooterG(g, "STICK:MOVE A:SELECT");
}

void drawGames() {
  display.clearDisplay();
  drawHeader("GAMES");
  display.setTextSize(1);

  if (!sdReady) {
    display.setCursor(8, 28); display.print("NO SD CARD");
    drawFooter("B:BACK");
    return;
  }
  if (gameCount == 0) {
    if (gameScanPathSkipped) {
      display.setCursor(8, 24); display.print("PATH TOO LONG");
      display.setCursor(8, 36); display.print("Rename .gar file");
    } else {
      display.setCursor(8, 24); display.print("No games found");
      display.setCursor(8, 36); display.print("Put .gar in /GAMES");
    }
    drawFooter("A:RESCAN  B:BACK");
    return;
  }

  // Visible rows: 4 (y = 16,25,34,43)
  const uint8_t visible = 4;
  if (gameSelection < gameScroll) gameScroll = gameSelection;
  if (gameSelection >= gameScroll + visible) gameScroll = gameSelection - visible + 1;

  for (uint8_t row = 0; row < visible; ++row) {
    uint8_t idx = gameScroll + row;
    if (idx >= gameCount) break;
    int y = 16 + row * 9;
    display.setCursor(idx == gameSelection ? 2 : 10, y);
    display.print(idx == gameSelection ? ">" : " ");
    display.print(" ");
    display.print(gameList[idx].name);
  }

  // Scrollbar when needed
  if (gameCount > visible) {
    display.drawFastVLine(125, 16, 36, C_ON);
    int thumbY = 16 + ((int)gameScroll * 28) / (gameCount - visible);
    display.fillRect(123, thumbY, 3, 8, C_ON);
  }
  // "n/total" (+ when the list was truncated) in the header, clear of the rows.
  char pos[12];
  snprintf(pos, sizeof(pos), "%u/%u%s%s", (unsigned)(gameSelection + 1), (unsigned)gameCount,
           gameListTruncated ? "+" : "", gameScanPathSkipped ? "!" : "");
  display.setCursor(126 - (int)strlen(pos) * 6, 1);
  display.print(pos);
  if (gameListTruncated && gameScanPathSkipped) drawFooter("48+ PATH! X:SCAN");
  else if (gameListTruncated) drawFooter("48+ GAMES X:SCAN");
  else if (gameScanPathSkipped) drawFooter("PATH TOO LONG! X:SCAN");
  else drawFooter("A:PLAY X:SCAN B:BACK");
}

// Universal pause menu (firmware-owned)
// CONTINUE / RESTART / MODE / LEAVE
void drawPause() {
  display.clearDisplay();
  // Decorative frame
  display.drawRoundRect(4, 4, 120, 56, 3, C_ON);
  display.drawRoundRect(6, 6, 116, 52, 2, C_ON);

  // Title (current game name, truncated)
  display.setTextSize(1);
  display.setTextColor(C_ON);
  int tw = strlen(currentGameTitle) * 6;
  display.setCursor((128 - tw) / 2, 9);
  display.print(currentGameTitle);

  // Divider
  display.drawFastHLine(20, 19, 88, C_ON);

  const char *items[] = {"CONTINUE", "RESTART", "MODE", "LEAVE"};
  for (uint8_t i = 0; i < 4; ++i) {
    int y = 22 + i * 8;
    if (i == pauseSelection) {
      display.fillRoundRect(22, y - 1, 84, 9, 2, C_ON);
      display.setTextColor(C_OFF);
      display.setCursor(28, y);
      display.print("> ");
      display.print(items[i]);
      display.setTextColor(C_ON);
    } else {
      display.setCursor(34, y);
      display.print(items[i]);
    }
  }
}

void drawSettings() {
  display.clearDisplay();
  drawHeader("SETTINGS");
  for (uint8_t i = 0; i < SETTINGS_COUNT; ++i) {
    int y = 16 + i * 9;
    display.setCursor(i == settingsSelection ? 3 : 11, y);
    display.print(i == settingsSelection ? ">" : " ");
    display.print(" ");
    display.print(settingsItems[i]);
  }
  drawFooter("A:SEL  B:BACK");
}

void drawRawValue() {
  display.clearDisplay();
  drawHeader("RAW VALUE");
  display.setTextSize(1);
  display.setCursor(2, 14);
  display.print("X UD: "); display.print(joyX);
  display.setCursor(2, 24);
  display.print("Y LR: "); display.print(joyY);
  display.setCursor(2, 34);
  display.print("JOY SW: "); display.print(down(BTN_JOY) ? "0 DOWN" : "1 UP");
  display.setCursor(2, 44);
  display.print("A:"); display.print(down(BTN_A) ? '0' : '1');
  display.print(" B:"); display.print(down(BTN_B) ? '0' : '1');
  display.print(" X:"); display.print(down(BTN_X) ? '0' : '1');
  display.print(" Y:"); display.print(down(BTN_Y) ? '0' : '1');
  drawFooter("JOY: BACK  0=DOWN");
}

void drawDiagnostics() {
  display.clearDisplay();
  drawHeader("DIAGNOSTICS");
  display.setTextSize(1);
  display.setCursor(2, 15); display.print("OLED: "); display.print(displayReady ? "OK" : "FAIL");
  display.setCursor(2, 25); display.print("SD:   "); display.print(sdReady ? "OK" : "MISSING");
  display.setCursor(2, 35); display.print("ADC X/Y: "); display.print(joyX); display.print("/"); display.print(joyY);
  display.setCursor(2, 45); display.print("FREE HEAP: "); display.print(ESP.getFreeHeap());
  drawFooter("B: BACK");
}

void drawAbout() {
  display.clearDisplay();
  drawHeader("ABOUT");
  const uint8_t visible = ABOUT_VISIBLE;
  const uint8_t maxScroll = ABOUT_MAX_SCROLL;

  if (aboutScroll > maxScroll) aboutScroll = maxScroll;

  for (uint8_t row = 0; row < visible; ++row) {
    display.setCursor(3, 16 + row * 9);
    display.print(aboutLines[aboutScroll + row]);
  }

  // Scrollbar in the right margin.
  display.drawFastVLine(125, 16, 36, C_ON);
  const int thumbY = 16 + ((int)aboutScroll * 28) / (maxScroll ? maxScroll : 1);
  display.fillRect(123, thumbY, 3, 8, C_ON);

  drawFooter("STICK:SCROLL B:BACK");
}

void drawDisplaySettings() {
  display.clearDisplay();
  drawHeader("DISPLAY");
  display.setTextSize(1);
  display.setCursor(4, 20);
  display.print(displaySelection == 0 ? "> " : "  ");
  display.print("Invert: "); display.print(invertDisplay ? "ON" : "OFF");
  display.setCursor(4, 32);
  display.print(displaySelection == 1 ? "> " : "  ");
  display.print("Contrast: "); display.print(contrastValue);
  display.setCursor(4, 44);
  display.print("A: change / B: back");
  drawFooter("JOY: MOVE");
}

void renderScreen() {
  switch (screen) {
    case SCREEN_BOOT: drawBoot(); break;
    case SCREEN_HOME: drawHome(display); break;
    case SCREEN_GAMES: drawGames(); break;
    case SCREEN_SETTINGS: drawSettings(); break;
    case SCREEN_RAW: drawRawValue(); break;
    case SCREEN_DIAGNOSTICS: drawDiagnostics(); break;
    case SCREEN_ABOUT: drawAbout(); break;
    case SCREEN_DISPLAY: drawDisplaySettings(); break;
    case SCREEN_PAUSE: drawPause(); break;
    default: break;
  }
}

// ---------- SD popup ----------
void drawSdPopup() {
  const uint32_t el = millis() - sdPopupStartedAt;
  if (el >= POPUP_MS) { showSdPopup = false; return; }

  float y;
  if (el < POPUP_IN_MS) {
    y = -44.0f + 57.0f * smooth01(el / (float)POPUP_IN_MS);
  } else if (el > POPUP_MS - POPUP_OUT_MS) {
    y = 13.0f - 57.0f * smooth01((el - (POPUP_MS - POPUP_OUT_MS)) / (float)POPUP_OUT_MS);
  } else {
    y = 13.0f;
  }
  const int iy = (int)y;

  display.fillRoundRect(8, iy, 112, 39, 4, C_OFF);
  display.drawRoundRect(8, iy, 112, 39, 4, C_ON);

  // 8-bit SD card icon
  display.fillRect(18, iy + 8, 17, 22, C_ON);
  display.fillRect(22, iy + 5, 9, 4, C_ON);
  display.fillRect(22, iy + 10, 3, 6, C_OFF);
  display.fillRect(28, iy + 10, 3, 6, C_OFF);
  if (sdPopupKind < 0) {
    for (int d = -1; d <= 1; ++d) display.drawLine(15 + d, iy + 32, 38 + d, iy + 6, C_OFF);
    display.drawLine(15, iy + 32, 38, iy + 6, C_ON);
  }

  display.setTextSize(1);
  display.setTextColor(C_ON);
  display.setCursor(46, iy + 10);
  display.print("SD CARD");
  display.setCursor(46, iy + 22);
  display.print(sdPopupKind > 0 ? "CONNECTED" : "REMOVED");
}

// ---------- Navigation ----------
void goBack() {
  switch (screen) {
    case SCREEN_HOME: break;
    case SCREEN_SETTINGS:
    case SCREEN_GAMES: screen = SCREEN_HOME; break;
    case SCREEN_RAW:
    case SCREEN_DIAGNOSTICS:
    case SCREEN_DISPLAY: screen = SCREEN_SETTINGS; break;
    case SCREEN_ABOUT: screen = previousScreen; break;
    case SCREEN_BOOT: screen = SCREEN_HOME; break;
    default: break;
  }
}

void selectHome() {
  switch (homeSelection) {
    case 0:
      showBusy("SCANNING...");
      scanGames();
      screen = SCREEN_GAMES;
      break;
    case 1: screen = SCREEN_SETTINGS; break;
    case 2: previousScreen = SCREEN_HOME; aboutScroll = 0; screen = SCREEN_ABOUT; break;
  }
}

void selectSetting() {
  switch (settingsSelection) {
    case 0: screen = SCREEN_RAW; break;
    case 1: screen = SCREEN_DIAGNOSTICS; break;
    case 2: screen = SCREEN_DISPLAY; break;
    case 3: previousScreen = SCREEN_SETTINGS; aboutScroll = 0; screen = SCREEN_ABOUT; break;
  }
}

void moveSelection(int8_t direction);
void launchGame(const char *path);

// One joystick step (-1 = up, +1 = down) with hysteresis + auto-repeat; 0 = no step.
int8_t joyNavStep() {
  const int d = joyX - joyCenX;
  int8_t req = 0;
  if (d > JOY_NAV_ENTER) req = -1;
  else if (d < -JOY_NAV_ENTER) req = 1;

  const uint32_t now = millis();
  if (req == 0) {
    if (abs(d) < JOY_NAV_EXIT) latchedNavDir = 0;
    return 0;
  }
  if (req != latchedNavDir) {
    latchedNavDir = req;
    navRepeatAt = now;
    return req;
  }
  if (now - navRepeatAt >= JOY_NAV_REPEAT_MS) {
    navRepeatAt = now;
    return req;
  }
  return 0;
}

void resumeGame() {
  garPaused = false;
  garSwallowInput = true;     // buttons still held stay masked until released
  screen = SCREEN_GAME;
}

void leaveGameToList() {
  garStop();
  garPaused = false;
  garSwallowInput = true;
  latchedNavDir = 0;
  scanGamesKeep();            // keeps the highlighted game selected
  screen = SCREEN_GAMES;
}

void handlePauseNavigation() {
  const int8_t step = joyNavStep();
  if (step < 0 && pauseSelection > 0) --pauseSelection;
  if (step > 0 && pauseSelection < 3) ++pauseSelection;

  if (pressed(BTN_A) || pressed(BTN_JOY)) {
    switch (pauseSelection) {
      case 0: resumeGame(); break;                                  // CONTINUE
      case 1:                                                       // RESTART
        garPaused = false;
        garSwallowInput = true;
        if (currentGamePath[0]) launchGame(currentGamePath);
        else leaveGameToList();
        break;
      case 2: garModeRequested = true; resumeGame(); break;         // MODE
      default: leaveGameToList(); break;                            // LEAVE
    }
    latchedNavDir = 0;
  } else if (pressed(BTN_B)) {
    resumeGame();             // B is part of the B+Y pause combo, so B = back to the game
    latchedNavDir = 0;
  }
}

void handleNavigation() {
  // Reset the long-press latch no matter which screen we are on.
  if (released(BTN_JOY)) longPressHandled = false;

  if (screen == SCREEN_PAUSE) {
    handlePauseNavigation();
    return;
  }

  // Raw Value: joystick click is Back.
  if (screen == SCREEN_RAW) {
    if (pressed(BTN_JOY)) screen = SCREEN_SETTINGS;
    return;
  }

  if (pressed(BTN_B)) {
    goBack();
    latchedNavDir = 0;
    return;
  }

  // Long joystick click returns Home.
  if (longPressed(BTN_JOY) && !longPressHandled) {
    longPressHandled = true;
    screen = SCREEN_HOME;
    latchedNavDir = 0;
    return;
  }

  const int8_t step = joyNavStep();   // X+ = up (-1), X- = down (+1)

  // About: joystick up/down scrolls
  if (screen == SCREEN_ABOUT) {
    if (step < 0 && aboutScroll > 0) --aboutScroll;
    if (step > 0 && aboutScroll < ABOUT_MAX_SCROLL) ++aboutScroll;
    if (pressed(BTN_A)) goBack();
    return;
  }

  if (step != 0) moveSelection(step);

  if (screen == SCREEN_GAMES && pressed(BTN_X)) {
    showBusy("SCANNING...");
    scanGamesKeep();
  }

  if (pressed(BTN_A)) {
    if (screen == SCREEN_HOME) selectHome();
    else if (screen == SCREEN_SETTINGS) selectSetting();
    else if (screen == SCREEN_DISPLAY) {
      if (displaySelection == 0) {
        invertDisplay = !invertDisplay;
        display.invertDisplay(invertDisplay);
      } else {
        int c = (int)contrastValue + 32;            // never overflows uint8_t
        contrastValue = (uint8_t)(c > 255 ? 32 : c);
        display.setContrast(contrastValue);
      }
      saveDisplayPrefs();
    } else if (screen == SCREEN_GAMES) {
      if (gameCount == 0) {
        showBusy("SCANNING...");
        scanGames();                    // A = rescan when empty
      } else if (gameSelection < gameCount) {
        launchGame(gameList[gameSelection].path);
      }
    } else if (screen == SCREEN_DIAGNOSTICS) {
      goBack();
    }
  }
}

void moveSelection(int8_t direction) {
  if (screen == SCREEN_HOME) {
    if (direction < 0 && homeSelection > 0) --homeSelection;
    if (direction > 0 && homeSelection + 1 < HOME_COUNT) ++homeSelection;
  } else if (screen == SCREEN_SETTINGS) {
    if (direction < 0 && settingsSelection > 0) --settingsSelection;
    if (direction > 0 && settingsSelection + 1 < SETTINGS_COUNT) ++settingsSelection;
  } else if (screen == SCREEN_DISPLAY) {
    if (direction < 0) displaySelection = 0;
    if (direction > 0) displaySelection = 1;
  } else if (screen == SCREEN_GAMES) {
    if (direction < 0 && gameSelection > 0) --gameSelection;
    if (direction > 0 && gameSelection + 1 < gameCount) ++gameSelection;
  }
}

// =====================================================================
//  GAME INPUT API  (the VM reads only this)
// =====================================================================
enum : uint16_t {
  GI_UP = 1 << 0, GI_DOWN = 1 << 1, GI_LEFT = 1 << 2, GI_RIGHT = 1 << 3,
  GI_A = 1 << 4, GI_B = 1 << 5, GI_X = 1 << 6, GI_Y = 1 << 7, GI_STICK = 1 << 8,
  GI_MODE = 1 << 9          // set for one frame when player chose MODE in pause
};

struct GameInput {
  uint16_t held, pressed, released;  // bitmasks of GI_*
  int8_t ax, ay;                     // -100..100, ax: right+, ay: down+
};
GameInput gi = {0, 0, 0, 0, 0};

static constexpr int GI_CENTER = 2048;
static constexpr int GI_DEAD = 250;
static constexpr int GI_DIR_ON = 900;
static constexpr int GI_DIR_OFF = 550;
static constexpr int GI_X_SIGN = 1;    // flip to -1 if left/right is reversed
static constexpr int GI_Y_SIGN = -1;   // matches the menu (joyX high = up)
uint16_t giPrev = 0;

static int8_t giNorm(int d) {
  int a = abs(d);
  if (a < GI_DEAD) return 0;
  int v = ((a - GI_DEAD) * 100) / (2047 - GI_DEAD);
  if (v > 100) v = 100;
  return (int8_t)(d < 0 ? -v : v);
}

static bool giHys(int d, bool wasOn) {
  return d > GI_DIR_ON || (wasOn && d > GI_DIR_OFF);
}

static constexpr uint16_t GI_BUTTON_MASK = GI_A | GI_B | GI_X | GI_Y | GI_STICK;
uint16_t giSuppress = 0;       // buttons masked until physically released
bool     giModeHold = false;   // MODE stays visible until the VM has run a frame

// Called every loop() pass. Edges (pressed/released) LATCH until the VM consumes
// them in giEndFrame(); loop() runs far faster than the 30 fps VM frame.
void giUpdate() {
  const int dx = (joyY - joyCenY) * GI_X_SIGN;   // left/right axis
  const int dy = (joyX - joyCenX) * GI_Y_SIGN;   // up/down axis, down positive
  gi.ax = giNorm(dx);
  gi.ay = giNorm(dy);

  uint16_t h = 0;
  if (giHys(dx,  giPrev & GI_RIGHT)) h |= GI_RIGHT;
  if (giHys(-dx, giPrev & GI_LEFT))  h |= GI_LEFT;
  if (giHys(dy,  giPrev & GI_DOWN))  h |= GI_DOWN;
  if (giHys(-dy, giPrev & GI_UP))    h |= GI_UP;
  if (down(BTN_A))   h |= GI_A;
  if (down(BTN_B))   h |= GI_B;
  if (down(BTN_X))   h |= GI_X;
  if (down(BTN_Y))   h |= GI_Y;
  if (down(BTN_JOY)) h |= GI_STICK;

  // The B+Y pause combo is reserved: neither button reaches the game until both
  // are released. Same for buttons still held when a game starts / resumes.
  if (down(BTN_B) && down(BTN_Y)) giSuppress |= GI_B | GI_Y;
  if (garSwallowInput) { giSuppress |= (h & GI_BUTTON_MASK); garSwallowInput = false; }
  giSuppress &= h;                 // un-mask once physically released
  h &= ~giSuppress;

  gi.pressed  |= (uint16_t)(h & ~giPrev);
  gi.released |= (uint16_t)(~h & giPrev);
  giPrev  = h;
  gi.held = h;

  // MODE comes from the pause menu: one "pressed" edge, held for one VM frame.
  if (garModeRequested) {
    gi.pressed |= GI_MODE;
    giModeHold = true;
    garModeRequested = false;
  }
  if (giModeHold) gi.held |= GI_MODE;

  // Never queue edges while no game is consuming them.
  if (screen != SCREEN_GAME) {
    gi.pressed = 0;
    gi.released = 0;
    giModeHold = false;
  }
}

// Called by the firmware after each VM frame.
void giEndFrame() {
  gi.pressed = 0;
  gi.released = 0;
  giModeHold = false;
}

// =====================================================================
//  GAR1 VIRTUAL MACHINE  (Milestone 1 + extensions)
// =====================================================================
/*
  PACKAGE FORMAT (GAR1 + optional AST1 only; old packages remain valid)
    "GAR1" (4) | u16 codeLen LE | code bytes | optional "AST1" asset block
    Max package size is 16384 bytes. Scan validates framing; launch validates
    all instructions, branch/call boundaries and the entire AST1 section.
    Execution starts at byte 0.  FRAME ends the frame; firmware presents
    the display and re-enters the VM next frame (~30 FPS).

  SAFETY (BASE plus selected EXTRA hardening)
    - Stack underflow / overflow and call-stack depth limit
    - Full instruction/operand and branch/call-boundary validation
    - Strict AST1 structure, unique sprite IDs, bounded dimensions
    - Per-frame instruction and rendering-work budgets
    - Variable, local and memory-pool bounds
    - Jump / call target validation
    - Division by zero
    - Instruction budget per frame
    - Malformed bytecode → clean stop + launcher recovery

  LIMITS
    Stack          : 48 × int32
    Globals        : 64 × int32
    Memory pool    : 256 × int32   (arrays / entity tables)
    Call depth     : 8
    Budget         : 30000 instructions / frame
    Package        : ≤ 16384 bytes

  ── EXISTING OPCODES (unchanged meaning) ──────────────────────────────
  CONTROL / DATA
    0x00 END
    0x01 PUSH8  i8
    0x02 PUSH16 i16
    0x03 LOAD   v        (0..63)
    0x04 STORE  v
    0x10 JMP    u16
    0x11 JZ     u16
    0x40 FRAME
    0x50 RND             pop n → 0..n-1  (now uses seeded LCG)

  MATH / LOGIC
    0x05 ADD  0x06 SUB  0x07 MUL  0x08 DIV  0x09 MOD
    0x0A LT   0x0B GT   0x0C EQ   0x0D NEQ  0x0E LE   0x0F GE
    0x12 NEG  0x13 NOT  (logical)
    0x14 AND  0x15 OR   (logical → 0/1)

  GRAPHICS
    0x20 CLS
    0x21 PIXEL x y
    0x22 RECT  x y w h
    0x23 FILL  x y w h
    0x24 TEXT  x y  + zero-terminated string (≤23 chars)
    0x25 NUM   x y value
    0x26 LINE  x0 y0 x1 y1

  INPUT
    0x30 HELD    mask
    0x31 PRESSED mask
    0x32 AXISX
    0x33 AXISY
    Masks: UP=1 DOWN=2 LEFT=4 RIGHT=8 A=16 B=32 X=64 Y=128 STICK=256 MODE=512

  ── NEW OPCODES (backward-compatible extensions) ──────────────────────
  BITWISE / EXTRA MATH
    0x16 BAND   a & b
    0x17 BOR    a | b
    0x18 BXOR   a ^ b
    0x19 BNOT   ~a
    0x1A SHL    a << b   (b clamped 0..31)
    0x1B SHR    a >> b   (arithmetic for signed)
    0x1C ABS    |a|
    0x1D POP             discard top of stack

  FUNCTIONS (call stack, backward-compatible)
    0x60 CALL u16        push return PC, jump
    0x61 RET             return
    0x62 ENTER argc,n    OPTIONAL per-call local allocation + argument transfer
    0x63 LOADL local     push local slot
    0x64 STOREL local    store local slot; existing packages need no ENTER

  MEMORY POOL / ARRAYS  (256 slots, index 0..255)
    0x70 LOADM           pop idx → push mem[idx]
    0x71 STOREM          pop val, pop idx → mem[idx] = val
    0x72 CLEARM          zero entire memory pool

  FIXED-POINT 16.16  (values still int32; high 16 bits = integer)
    0x80 FP_MUL          (a * b) >> 16
    0x81 FP_DIV          (a << 16) / b     (guard /0)
    0x82 TO_FP           a << 16
    0x83 FROM_FP         a >> 16           (truncate toward −∞)
    0x84 FP_ROUND        (a + 0x8000) >> 16

  RNG
    0x51 SEED            pop seed → set LCG state
    (0x50 RND uses the LCG; default seed if never set)

  EXTRA GRAPHICS
    0x27 CIRCLE  x y r
    0x28 FCIRCLE x y r

  EXTRA INPUT
    0x34 RELEASED mask   push 1 if any bit released this frame

  CAMERA / SPRITES (Phase 7)
    0x90 SETCAM  x y           set camera origin
    0x91 SPRITE  id x y        draw sprite (screen coords, 0-bits transparent)
    0x92 SPRITEW id x y        draw sprite in world coords (minus camera)

  Assets (optional, after code):
    "AST1" | u8 count | { u8 id, u8 w, u8 h, data[((w+7)/8)*h] }...

  Firmware exit: hold B+Y for ~0.6 s to open pause menu.
*/

static constexpr size_t   GAR_MAX_FILE   = GAME_FILE_MAX;
static constexpr uint8_t  GAR_STACK      = 48;
static constexpr uint8_t  GAR_VARS       = 64;
static constexpr uint16_t GAR_MEM        = 256;
static constexpr uint8_t  GAR_CALL_DEPTH = 8;
static constexpr uint8_t  GAR_LOCALS = 64;
static constexpr uint32_t GAR_BUDGET = 30000;
static constexpr uint32_t GAR_RENDER_BUDGET = 20000;

uint8_t *garBase = nullptr;
uint8_t *garCode = nullptr;
uint8_t *garBoundaryBits = nullptr; // one bit per valid instruction boundary
uint16_t garLen = 0, garPc = 0;
int32_t  garStack[GAR_STACK];
int32_t  garVar[GAR_VARS];
int32_t  garMem[GAR_MEM];
struct GarCallFrame {
  uint16_t returnPc;
  uint8_t localCount;
  bool localsReady;
  int32_t locals[GAR_LOCALS];
};
GarCallFrame garCallFrames[GAR_CALL_DEPTH];
GarCallFrame garRootFrame; // optional locals in top-level game code
uint8_t  garSp = 0;
uint8_t  garCallSp = 0;
static uint32_t garRenderWork = 0;
bool     garRunning = false;
const char *garError = nullptr;
uint32_t garRngState = 0xA5A5F00Du;   // default seed

// ---- Phase 7: assets / camera / sprites ----
struct GarSprite {
  uint8_t w, h;
  const uint8_t *data;   // 1 bpp, row-major, MSB left, bytes = ((w+7)/8)*h
};
GarSprite garSprites[GAR_MAX_SPRITES];
uint8_t   garSpriteCount = 0;
int32_t   garCamX = 0, garCamY = 0;

// Simple deterministic LCG (Numerical Recipes style)
static inline uint32_t garNextRnd() {
  garRngState = garRngState * 1664525u + 1013904223u;
  return garRngState;
}

// Explicit two's-complement wrapping helpers avoid signed-overflow UB and
// implementation-defined unsigned-to-signed conversions in the VM.
static int32_t garI32FromU32(uint32_t u) {
  int32_t out;
  memcpy(&out, &u, sizeof(out));
  return out;
}
static uint32_t garU32FromI32(int32_t v) {
  uint32_t out;
  memcpy(&out, &v, sizeof(out));
  return out;
}
static int32_t garWrap64(int64_t v) { return garI32FromU32((uint32_t)(uint64_t)v); }
static int32_t garWrapAdd(int32_t a, int32_t b) {
  return garI32FromU32(garU32FromI32(a) + garU32FromI32(b));
}
static int32_t garWrapSub(int32_t a, int32_t b) {
  return garI32FromU32(garU32FromI32(a) - garU32FromI32(b));
}
static int32_t garWrapMul(int32_t a, int32_t b) {
  return garI32FromU32(garU32FromI32(a) * garU32FromI32(b));
}
static int32_t garArithmeticShiftRight(int32_t a, uint8_t n) {
  if (n == 0) return a;
  const uint32_t u = garU32FromI32(a);
  uint32_t shifted = u >> n;
  if (a < 0) shifted |= (~(uint32_t)0) << (32 - n);
  return garI32FromU32(shifted);
}
static int64_t garFloorDiv65536(int64_t v) {
  int64_t q = v / 65536;
  if (v < 0 && (v % 65536) != 0) --q;
  return q;
}
static bool garBoundaryAt(const uint8_t *bits, uint16_t pc, uint16_t len) {
  return bits && pc < len && (bits[pc >> 3] & (uint8_t)(1u << (pc & 7u))) != 0;
}
static void garMarkBoundary(uint8_t *bits, uint16_t pc) {
  bits[pc >> 3] |= (uint8_t)(1u << (pc & 7u));
}

// Full package validator. It does not change VM state. Successful validation
// returns an allocated instruction-boundary bitmap to the caller if requested.
static bool garValidateBuffer(const uint8_t *buf, size_t sz, uint16_t *codeLenOut,
                              const char **errorOut, uint8_t **boundaryOut) {
  if (errorOut) *errorOut = "INVALID PACKAGE";
  if (boundaryOut) *boundaryOut = nullptr;
  if (!buf || sz < 7u || sz > GAR_MAX_FILE) {
    if (errorOut) *errorOut = "BAD FILE SIZE";
    return false;
  }
  if (memcmp(buf, "GAR1", 4) != 0) {
    if (errorOut) *errorOut = "NOT A GAR1 FILE";
    return false;
  }
  const uint16_t codeLen = (uint16_t)(buf[4] | ((uint16_t)buf[5] << 8));
  if (codeLen == 0 || (size_t)codeLen > sz - 6u) {
    if (errorOut) *errorOut = "BAD CODE LENGTH";
    return false;
  }

  const uint8_t *code = buf + 6;
  const size_t bitmapSize = ((size_t)codeLen + 7u) / 8u;
  uint8_t *bits = (uint8_t *)calloc(bitmapSize, 1u);
  if (!bits) {
    if (errorOut) *errorOut = "OUT OF RAM";
    return false;
  }

  size_t pc = 0;
  while (pc < codeLen) {
    garMarkBoundary(bits, (uint16_t)pc);
    const uint8_t op = code[pc++];
    size_t operandBytes = 0;
    switch (op) {
      case 0x00:
      case 0x05: case 0x06: case 0x07: case 0x08: case 0x09:
      case 0x0A: case 0x0B: case 0x0C: case 0x0D: case 0x0E: case 0x0F:
      case 0x12: case 0x13: case 0x14: case 0x15: case 0x16: case 0x17:
      case 0x18: case 0x19: case 0x1A: case 0x1B: case 0x1C: case 0x1D:
      case 0x20: case 0x21: case 0x22: case 0x23: case 0x25: case 0x26:
      case 0x27: case 0x28: case 0x30: case 0x31: case 0x32: case 0x33:
      case 0x34: case 0x40: case 0x50: case 0x51: case 0x61: case 0x70:
      case 0x71: case 0x72: case 0x80: case 0x81: case 0x82: case 0x83:
      case 0x84: case 0x90: case 0x91: case 0x92:
        break;
      case 0x01:
        operandBytes = 1;
        break;
      case 0x02:
        operandBytes = 2;
        break;
      case 0x03: case 0x04:
        if (pc >= codeLen) { if (errorOut) *errorOut = "TRUNCATED OPERAND"; free(bits); return false; }
        if (code[pc] >= GAR_VARS) { if (errorOut) *errorOut = "BAD VARIABLE"; free(bits); return false; }
        operandBytes = 1;
        break;
      case 0x10: case 0x11: case 0x60:
        operandBytes = 2;
        break;
      case 0x62: // ENTER argc, localCount; optional in legacy code
        if ((size_t)codeLen - pc < 2u) { if (errorOut) *errorOut = "TRUNCATED ENTER"; free(bits); return false; }
        if (code[pc] > code[pc + 1] || code[pc + 1] > GAR_LOCALS) {
          if (errorOut) *errorOut = "BAD ENTER";
          free(bits);
          return false;
        }
        operandBytes = 2;
        break;
      case 0x63: case 0x64:
        if (pc >= codeLen) { if (errorOut) *errorOut = "TRUNCATED LOCAL"; free(bits); return false; }
        if (code[pc] >= GAR_LOCALS) { if (errorOut) *errorOut = "BAD LOCAL"; free(bits); return false; }
        operandBytes = 1;
        break;
      case 0x24: {
        // BASE compatibility: runtime displays at most 23 bytes but consumes the
        // entire NUL-terminated string, so older longer-string packages still load.
        while (pc < codeLen && code[pc] != 0) ++pc;
        if (pc >= codeLen) {
          if (errorOut) *errorOut = "UNTERMINATED STRING";
          free(bits);
          return false;
        }
        ++pc;
        continue;
      }
      default:
        if (errorOut) *errorOut = "BAD OPCODE";
        free(bits);
        return false;
    }
    if (operandBytes > (size_t)codeLen - pc) {
      if (errorOut) *errorOut = "TRUNCATED OPERAND";
      free(bits);
      return false;
    }
    pc += operandBytes;
  }

  // All absolute branch/call destinations must point to actual instructions.
  pc = 0;
  while (pc < codeLen) {
    const uint8_t op = code[pc++];
    if (op == 0x10 || op == 0x11 || op == 0x60) {
      if (pc + 2u > codeLen) { if (errorOut) *errorOut = "TRUNCATED TARGET"; free(bits); return false; }
      const uint16_t target = (uint16_t)(code[pc] | ((uint16_t)code[pc + 1] << 8));
      if (!garBoundaryAt(bits, target, codeLen)) {
        if (errorOut) *errorOut = "BAD JUMP TARGET";
        free(bits); return false;
      }
      pc += 2u;
    } else if (op == 0x01 || op == 0x03 || op == 0x04 || op == 0x63 || op == 0x64) {
      pc += 1u;
    } else if (op == 0x02 || op == 0x62) {
      pc += 2u;
    } else if (op == 0x24) {
      while (pc < codeLen && code[pc++] != 0) {}
    }
  }

  // Legacy files have no suffix. The only permitted extension is one complete AST1 block.
  const size_t assetOff = 6u + (size_t)codeLen;
  if (assetOff < sz) {
    if (sz - assetOff < 5u || memcmp(buf + assetOff, "AST1", 4) != 0) {
      if (errorOut) *errorOut = "BAD ASSET SECTION";
      free(bits);
      return false;
    }
    const uint8_t count = buf[assetOff + 4u];
    if (count > GAR_MAX_SPRITES) { if (errorOut) *errorOut = "TOO MANY SPRITES"; free(bits); return false; }
    bool seen[GAR_MAX_SPRITES] = {false};
    size_t pos = assetOff + 5u;
    for (uint8_t i = 0; i < count; ++i) {
      if (pos > sz || sz - pos < 3u) { if (errorOut) *errorOut = "TRUNCATED SPRITE"; free(bits); return false; }
      const uint8_t id = buf[pos++], w = buf[pos++], h = buf[pos++];
      if (id >= GAR_MAX_SPRITES || seen[id]) { if (errorOut) *errorOut = "BAD SPRITE ID"; free(bits); return false; }
      if (w == 0 || h == 0 || w > 128 || h > 64) { if (errorOut) *errorOut = "BAD SPRITE SIZE"; free(bits); return false; }
      seen[id] = true;
      const size_t bytes = (((size_t)w + 7u) / 8u) * (size_t)h;
      if (bytes > sz - pos) { if (errorOut) *errorOut = "TRUNCATED SPRITE"; free(bits); return false; }
      pos += bytes;
    }
    if (pos != sz) { if (errorOut) *errorOut = "TRAILING ASSET DATA"; free(bits); return false; }
  }

  if (codeLenOut) *codeLenOut = codeLen;
  if (errorOut) *errorOut = nullptr;
  if (boundaryOut) *boundaryOut = bits;
  else free(bits);
  return true;
}

void garStop() {
  if (garBase) free(garBase);
  if (garBoundaryBits) free(garBoundaryBits);
  garBase = nullptr;
  garCode = nullptr;
  garBoundaryBits = nullptr;
  garLen = 0;
  garPc = 0;
  garSp = 0;
  garRunning = false;
  garCallSp = 0;
  memset(garCallFrames, 0, sizeof(garCallFrames));
  memset(&garRootFrame, 0, sizeof(garRootFrame));
  garRenderWork = 0;
  garSpriteCount = 0;
  garCamX = 0;
  garCamY = 0;
  memset(garSprites, 0, sizeof(garSprites));
}

bool garLoad(const char *path) {
  garStop();
  garError = nullptr;
  if (!sdReady) { garError = "NO SD CARD"; return false; }
  if (!sdMutex) { garError = "SD LOCK FAIL"; return false; }
  if (!path || !path[0]) { garError = "BAD PATH"; return false; }
  if (xSemaphoreTake(sdMutex, pdMS_TO_TICKS(SD_LOCK_TIMEOUT_MS)) != pdTRUE) {
    garError = "SD BUSY";
    return false;
  }
  if (!sdReady) {
    xSemaphoreGive(sdMutex);
    garError = "NO SD CARD";
    return false;
  }

  File f = SD.open(path, FILE_READ);
  uint8_t *buf = nullptr;
  uint8_t *boundaries = nullptr;
  bool loadOK = false;
  if (!f) {
    garError = "FILE NOT FOUND";
  } else {
    const size_t sz = f.size();
    if (sz < 7u || sz > GAR_MAX_FILE) {
      garError = "BAD FILE SIZE";
    } else {
      buf = (uint8_t *)malloc(sz);
      if (!buf) {
        garError = "OUT OF RAM";
      } else {
        size_t bytesRead = 0;
        if (f.seek(0)) bytesRead = (size_t)f.read(buf, sz);
        if (bytesRead != sz) {
          garError = "READ FAILED";
        } else {
          uint16_t cl = 0;
          const char *validationError = nullptr;
          if (!garValidateBuffer(buf, sz, &cl, &validationError, &boundaries)) {
            garError = validationError ? validationError : "INVALID PACKAGE";
          } else {
            garBase = buf;
            garCode = buf + 6;
            garBoundaryBits = boundaries;
            garLen = cl;
            buf = nullptr;        // owned by garBase from here on
            boundaries = nullptr;  // owned by garBoundaryBits
            const size_t assetOff = 6u + (size_t)cl;
            garSpriteCount = 0;
            memset(garSprites, 0, sizeof(garSprites));
            if (assetOff < sz) {
              const uint8_t count = garBase[assetOff + 4u];
              size_t pos = assetOff + 5u;
              for (uint8_t i = 0; i < count; ++i) {
                const uint8_t id = garBase[pos++];
                const uint8_t w = garBase[pos++];
                const uint8_t h = garBase[pos++];
                garSprites[id].w = w;
                garSprites[id].h = h;
                garSprites[id].data = garBase + pos;
                pos += (((size_t)w + 7u) / 8u) * (size_t)h;
                if ((uint8_t)(id + 1u) > garSpriteCount) garSpriteCount = (uint8_t)(id + 1u);
              }
            }
            loadOK = true;
          }
        }
      }
    }
    f.close();
  }
  xSemaphoreGive(sdMutex);
  if (buf) free(buf);
  if (boundaries) free(boundaries);
  if (!loadOK) {
    garStop();
    if (!garError) garError = "LOAD FAILED";
    return false;
  }

  garPc = 0;
  garSp = 0;
  garCallSp = 0;
  memset(garCallFrames, 0, sizeof(garCallFrames));
  memset(&garRootFrame, 0, sizeof(garRootFrame));
  garCamX = 0;
  garCamY = 0;
  memset(garVar, 0, sizeof(garVar));
  memset(garMem, 0, sizeof(garMem));
  garRngState = 0xA5A5F00Du;
  garRenderWork = 0;
  garRunning = true;
  return true;
}

// Saturating int32 -> int16 (wrapping would draw 70000 at x=4464).
static inline int16_t s16(int32_t v) {
  return v > 32767 ? (int16_t)32767 : (v < -32768 ? (int16_t)-32768 : (int16_t)v);
}

#define G_FAIL(m) do { garError = (m); garRunning = false; return; } while (0)
#define G_NEED(n) do { if (garSp < (n)) G_FAIL("STACK UNDERFLOW"); } while (0)
#define G_PUSH(v) do { if (garSp >= GAR_STACK) G_FAIL("STACK OVERFLOW"); garStack[garSp++] = (int32_t)(v); } while (0)
#define G_POP()   (garStack[--garSp])
#define G_U8(dst) do { if (garPc >= garLen) G_FAIL("CODE TRUNCATED"); (dst) = garCode[garPc++]; } while (0)

static bool garChargeRenderWork(uint32_t amount) {
  if (amount > GAR_RENDER_BUDGET - garRenderWork) return false;
  garRenderWork += amount;
  return true;
}
// Clipped graphics helpers: untrusted bytecode cannot wrap 32-bit coordinates
// into int16_t or force huge off-screen fill loops.
static void garDrawPixelClipped(int32_t x, int32_t y) {
  if (x >= 0 && x < 128 && y >= 0 && y < 64) display.drawPixel((int16_t)x, (int16_t)y, C_ON);
}

static uint32_t garRectWork(int32_t x, int32_t y, int32_t w, int32_t h, bool filled) {
  if (w <= 0 || h <= 0) return 0;
  const int64_t right = (int64_t)x + w;
  const int64_t bottom = (int64_t)y + h;
  const int64_t l = x < 0 ? 0 : x;
  const int64_t t = y < 0 ? 0 : y;
  const int64_t r = right > 128 ? 128 : right;
  const int64_t b = bottom > 64 ? 64 : bottom;
  if (r <= l || b <= t) return 0;
  const uint32_t cw = (uint32_t)(r - l), ch = (uint32_t)(b - t);
  return filled ? cw * ch : (cw == 1 || ch == 1 ? cw * ch : 2u * cw + 2u * ch - 4u);
}

static void garDrawRectClipped(int32_t x, int32_t y, int32_t w, int32_t h, bool filled) {
  if (w <= 0 || h <= 0) return;
  const int64_t right = (int64_t)x + w;
  const int64_t bottom = (int64_t)y + h;
  const int32_t l = x < 0 ? 0 : x;
  const int32_t t = y < 0 ? 0 : y;
  const int32_t r = right > 128 ? 128 : (right < 0 ? 0 : (int32_t)right);
  const int32_t b = bottom > 64 ? 64 : (bottom < 0 ? 0 : (int32_t)bottom);
  if (r <= l || b <= t) return;
  if (filled) {
    display.fillRect(l, t, r - l, b - t, C_ON);
    return;
  }
  const int64_t xr = right - 1;
  const int64_t yb = bottom - 1;
  if (y >= 0 && y < 64) display.drawFastHLine(l, (int16_t)y, r - l, C_ON);
  if (yb >= 0 && yb < 64 && yb != y) display.drawFastHLine(l, (int16_t)yb, r - l, C_ON);
  if (x >= 0 && x < 128) display.drawFastVLine((int16_t)x, t, b - t, C_ON);
  if (xr >= 0 && xr < 128 && xr != x) display.drawFastVLine((int16_t)xr, t, b - t, C_ON);
}

static uint8_t garLineCode(double x, double y) {
  uint8_t c = 0;
  if (x < 0) c |= 1;
  else if (x > 127) c |= 2;
  if (y < 0) c |= 4;
  else if (y > 63) c |= 8;
  return c;
}
static void garDrawLineClipped(int32_t ix0, int32_t iy0, int32_t ix1, int32_t iy1) {
  double x0 = ix0, y0 = iy0, x1 = ix1, y1 = iy1;
  for (uint8_t tries = 0; tries < 8; ++tries) {
    const uint8_t c0 = garLineCode(x0, y0), c1 = garLineCode(x1, y1);
    if ((c0 | c1) == 0) {
      display.drawLine((int16_t)x0, (int16_t)y0, (int16_t)x1, (int16_t)y1, C_ON);
      return;
    }
    if (c0 & c1) return;
    const uint8_t out = c0 ? c0 : c1;
    double x = 0, y = 0;
    if (out & 8) {
      if (y1 == y0) return;
      y = 63; x = x0 + (x1 - x0) * (y - y0) / (y1 - y0);
    } else if (out & 4) {
      if (y1 == y0) return;
      y = 0; x = x0 + (x1 - x0) * (y - y0) / (y1 - y0);
    } else if (out & 2) {
      if (x1 == x0) return;
      x = 127; y = y0 + (y1 - y0) * (x - x0) / (x1 - x0);
    } else {
      if (x1 == x0) return;
      x = 0; y = y0 + (y1 - y0) * (x - x0) / (x1 - x0);
    }
    if (out == c0) { x0 = x; y0 = y; }
    else { x1 = x; y1 = y; }
  }
}

// Accept a sprite ID rather than GarSprite& so Arduino's generated prototypes
// do not refer to GarSprite before its definition.
static uint32_t garSpriteVisibleWork(uint8_t spriteId, int64_t x, int64_t y) {
  if (spriteId >= GAR_MAX_SPRITES) return 0;
  const GarSprite &sp = garSprites[spriteId];
  if (!sp.data || !sp.w || !sp.h) return 0;
  const int64_t l = x < 0 ? 0 : x;
  const int64_t t = y < 0 ? 0 : y;
  const int64_t r = x + sp.w > 128 ? 128 : x + sp.w;
  const int64_t b = y + sp.h > 64 ? 64 : y + sp.h;
  if (r <= l || b <= t) return 0;
  return (uint32_t)(r - l) * (uint32_t)(b - t);
}

static void garDrawSprite(uint8_t spriteId, int64_t x, int64_t y) {
  if (spriteId >= GAR_MAX_SPRITES) return;
  const GarSprite &sp = garSprites[spriteId];
  if (!sp.data || sp.w == 0 || sp.h == 0) return;
  const int64_t left = x < 0 ? 0 : x;
  const int64_t top = y < 0 ? 0 : y;
  const int64_t right = x + sp.w > 128 ? 128 : x + sp.w;
  const int64_t bottom = y + sp.h > 64 ? 64 : y + sp.h;
  if (right <= left || bottom <= top) return;
  const size_t rowBytes = ((size_t)sp.w + 7u) / 8u;
  for (int64_t py = top; py < bottom; ++py) {
    const size_t row = (size_t)(py - y);
    const uint8_t *src = sp.data + row * rowBytes;
    for (int64_t px = left; px < right; ++px) {
      const size_t col = (size_t)(px - x);
      if (src[col >> 3] & (uint8_t)(0x80u >> (col & 7u)))
        display.drawPixel((int16_t)px, (int16_t)py, C_ON);
    }
  }
}


// Runs until FRAME, END, error, or budget exhausted.
void garRunFrame() {
  if (!garRunning) return;
  garRenderWork = 0;
  uint32_t budget = GAR_BUDGET;
  while (budget--) {
    uint8_t op, u, u2;
    int32_t a, b, c, d;
    G_U8(op);
    switch (op) {
      // ── existing control / data ───────────────────────────────────
      case 0x00: garRunning = false; return;

      case 0x01: G_U8(u); G_PUSH((int8_t)u); break;
      case 0x02: G_U8(u); G_U8(u2); G_PUSH((int16_t)(u | (u2 << 8))); break;
      case 0x03:
        G_U8(u);
        if (u >= GAR_VARS) G_FAIL("BAD VARIABLE");
        G_PUSH(garVar[u]);
        break;
      case 0x04:
        G_U8(u);
        if (u >= GAR_VARS) G_FAIL("BAD VARIABLE");
        G_NEED(1);
        garVar[u] = G_POP();
        break;

      // ── existing math ─────────────────────────────────────────────
      case 0x05: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(garWrapAdd(a, b)); break;
      case 0x06: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(garWrapSub(a, b)); break;
      case 0x07: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(garWrapMul(a, b)); break;
      case 0x08: {
        G_NEED(2); b = G_POP(); a = G_POP();
        if (b == 0) G_FAIL("DIVIDE BY ZERO");
        // INT_MIN / -1 is undefined in C++ — clamp to INT_MIN
        if (a == (int32_t)0x80000000L && b == -1) { G_PUSH(a); }
        else G_PUSH(a / b);
        break;
      }
      case 0x09: {
        G_NEED(2); b = G_POP(); a = G_POP();
        if (b == 0) G_FAIL("DIVIDE BY ZERO");
        if (a == (int32_t)0x80000000L && b == -1) { G_PUSH(0); }
        else G_PUSH(a % b);
        break;
      }
      case 0x0A: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a <  b); break;
      case 0x0B: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a >  b); break;
      case 0x0C: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a == b); break;
      case 0x0D: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a != b); break;
      case 0x0E: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a <= b); break;
      case 0x0F: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a >= b); break;

      case 0x10: {
        G_U8(u); G_U8(u2);
        uint16_t t = (uint16_t)(u | (u2 << 8));
        if (!garBoundaryAt(garBoundaryBits, t, garLen)) G_FAIL("BAD JUMP");
        garPc = t;
        break;
      }
      case 0x11: {
        G_U8(u); G_U8(u2);
        uint16_t t = (uint16_t)(u | (u2 << 8));
        if (!garBoundaryAt(garBoundaryBits, t, garLen)) G_FAIL("BAD JUMP");
        G_NEED(1);
        a = G_POP();
        if (a == 0) garPc = t;
        break;
      }
      case 0x12: { G_NEED(1); a = G_POP();
        if (a == (int32_t)0x80000000L) G_PUSH(a); else G_PUSH(-a);
        break; }
      case 0x13: G_NEED(1); a = G_POP(); G_PUSH(a == 0); break;
      case 0x14: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH((a != 0) && (b != 0)); break;
      case 0x15: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH((a != 0) || (b != 0)); break;

      // ── NEW bitwise / abs ─────────────────────────────────────────
      case 0x16: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a & b); break;
      case 0x17: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a | b); break;
      case 0x18: G_NEED(2); b = G_POP(); a = G_POP(); G_PUSH(a ^ b); break;
      case 0x19: G_NEED(1); a = G_POP(); G_PUSH(garI32FromU32(~garU32FromI32(a))); break;
      case 0x1A: { // SHL
        G_NEED(2); b = G_POP(); a = G_POP();
        if (b < 0) b = 0;
        if (b > 31) b = 31;
        G_PUSH(garI32FromU32(garU32FromI32(a) << (uint8_t)b));
        break;
      }
      case 0x1B: { // SHR arithmetic
        G_NEED(2); b = G_POP(); a = G_POP();
        if (b < 0) b = 0;
        if (b > 31) b = 31;
        G_PUSH(garArithmeticShiftRight(a, (uint8_t)b));
        break;
      }
      case 0x1C: { // ABS — INT_MIN stays INT_MIN (defined safe behavior)
        G_NEED(1); a = G_POP();
        if (a == (int32_t)0x80000000L) { G_PUSH(a); }
        else G_PUSH(a < 0 ? -a : a);
        break;
      }
      case 0x1D: G_NEED(1); G_POP(); break;   // POP

      // ── existing + new graphics ───────────────────────────────────
      case 0x20:
        if (!garChargeRenderWork(8192)) G_FAIL("RENDER LIMIT");
        display.clearDisplay();
        break;
      case 0x21:
        G_NEED(2); b = G_POP(); a = G_POP();
        if (a >= 0 && a < 128 && b >= 0 && b < 64 && !garChargeRenderWork(1)) G_FAIL("RENDER LIMIT");
        garDrawPixelClipped(a, b);
        break;
      case 0x22:
        G_NEED(4); d = G_POP(); c = G_POP(); b = G_POP(); a = G_POP();
        if (!garChargeRenderWork(garRectWork(a, b, c, d, false))) G_FAIL("RENDER LIMIT");
        garDrawRectClipped(a, b, c, d, false);
        break;
      case 0x23:
        G_NEED(4); d = G_POP(); c = G_POP(); b = G_POP(); a = G_POP();
        if (!garChargeRenderWork(garRectWork(a, b, c, d, true))) G_FAIL("RENDER LIMIT");
        garDrawRectClipped(a, b, c, d, true);
        break;
      case 0x24: {
        G_NEED(2); b = G_POP(); a = G_POP();
        char buf[24];
        uint8_t n = 0;
        for (;;) {
          G_U8(u);
          if (u == 0) break;
          if (n >= 23) G_FAIL("STRING TOO LONG");
          buf[n++] = (char)u;
        }
        buf[n] = 0;
        // At most 23 glyphs (6 px each, 8 px tall); skip wholly off-screen text.
        if (a >= -138 && a < 128 && b >= -7 && b < 64) {
          if (!garChargeRenderWork((uint32_t)n * 6u)) G_FAIL("RENDER LIMIT");
          display.setTextSize(1);
          display.setTextColor(C_ON);
          display.setCursor((int16_t)a, (int16_t)b);
          display.print(buf);
        }
        break;
      }
      case 0x25:
        G_NEED(3); c = G_POP(); b = G_POP(); a = G_POP();
        if (a >= -66 && a < 128 && b >= -7 && b < 64) {
          if (!garChargeRenderWork(66)) G_FAIL("RENDER LIMIT");
          display.setTextSize(1);
          display.setTextColor(C_ON);
          display.setCursor((int16_t)a, (int16_t)b);
          display.print((long)c);
        }
        break;
      case 0x26:
        G_NEED(4); d = G_POP(); c = G_POP(); b = G_POP(); a = G_POP();
        if (!garChargeRenderWork(160)) G_FAIL("RENDER LIMIT");
        garDrawLineClipped(a, b, c, d);
        break;
      case 0x27: { // CIRCLE
        G_NEED(3); c = G_POP(); b = G_POP(); a = G_POP();
        if (c < 0) c = 0;
        if (c > 512) c = 512;
        if (a >= -c && a <= 127 + c && b >= -c && b <= 63 + c) {
          if (!garChargeRenderWork((uint32_t)(8 * c + 8))) G_FAIL("RENDER LIMIT");
          display.drawCircle((int16_t)a, (int16_t)b, (int16_t)c, C_ON);
        }
        break;
      }
      case 0x28: { // FCIRCLE
        G_NEED(3); c = G_POP(); b = G_POP(); a = G_POP();
        if (c < 0) c = 0;
        if (c > 512) c = 512;
        if (a >= -c && a <= 127 + c && b >= -c && b <= 63 + c) {
          const uint32_t work = (uint32_t)((int64_t)2 * c * c + 4 * c + 1);
          if (!garChargeRenderWork(work > 8192u ? 8192u : work)) G_FAIL("RENDER LIMIT");
          display.fillCircle((int16_t)a, (int16_t)b, (int16_t)c, C_ON);
        }
        break;
      }

      // ── existing + new input ──────────────────────────────────────
      case 0x30:
        G_NEED(1); a = G_POP();
        if (a < 0 || ((uint32_t)a & ~0x03FFu)) G_FAIL("BAD INPUT MASK");
        G_PUSH((gi.held & (uint16_t)a) ? 1 : 0);
        break;
      case 0x31:
        G_NEED(1); a = G_POP();
        if (a < 0 || ((uint32_t)a & ~0x03FFu)) G_FAIL("BAD INPUT MASK");
        G_PUSH((gi.pressed & (uint16_t)a) ? 1 : 0);
        break;
      case 0x32: G_PUSH(gi.ax); break;
      case 0x33: G_PUSH(gi.ay); break;
      case 0x34:
        G_NEED(1); a = G_POP();
        if (a < 0 || ((uint32_t)a & ~0x03FFu)) G_FAIL("BAD INPUT MASK");
        G_PUSH((gi.released & (uint16_t)a) ? 1 : 0);
        break;

      // ── FRAME ─────────────────────────────────────────────────────
      case 0x40: return;

      // ── RNG ───────────────────────────────────────────────────────
      case 0x50: {
        G_NEED(1); a = G_POP();
        if (a <= 0) { G_PUSH(0); break; }
        // modulo bias is negligible for games
        uint32_t r = garNextRnd();          // low LCG bits have tiny periods -> use the high ones
        if (a <= 0x1000000) r >>= 8;
        G_PUSH((int32_t)(r % (uint32_t)a));
        break;
      }
      case 0x51: // SEED
        G_NEED(1); a = G_POP();
        garRngState = (uint32_t)a;
        if (garRngState == 0) garRngState = 1;  // avoid stuck zero
        break;

      // ── FUNCTIONS ─────────────────────────────────────────────────
      case 0x60: { // CALL
        G_U8(u); G_U8(u2);
        const uint16_t t = (uint16_t)(u | ((uint16_t)u2 << 8));
        if (!garBoundaryAt(garBoundaryBits, t, garLen)) G_FAIL("BAD CALL");
        if (garCallSp >= GAR_CALL_DEPTH) G_FAIL("CALL DEPTH");
        GarCallFrame &frame = garCallFrames[garCallSp++];
        frame.returnPc = garPc;
        frame.localCount = 0;
        frame.localsReady = false;
        memset(frame.locals, 0, sizeof(frame.locals));
        garPc = t;
        break;
      }
      case 0x61: // RET
        if (garCallSp == 0) G_FAIL("RET UNDERFLOW");
        garPc = garCallFrames[--garCallSp].returnPc;
        break;
      case 0x62: { // ENTER argc, localCount (optional, backward-compatible)
        G_U8(u); G_U8(u2);
        if (u > u2 || u2 > GAR_LOCALS) G_FAIL("BAD ENTER");
        GarCallFrame &frame = (garCallSp > 0) ? garCallFrames[garCallSp - 1] : garRootFrame;
        if (frame.localsReady) G_FAIL("DUPLICATE ENTER");
        G_NEED(u);
        memset(frame.locals, 0, sizeof(frame.locals));
        frame.localCount = u2;
        frame.localsReady = true;
        for (int i = (int)u - 1; i >= 0; --i) frame.locals[i] = G_POP();
        break;
      }
      case 0x63: { // LOADL
        G_U8(u);
        GarCallFrame &frame = (garCallSp > 0) ? garCallFrames[garCallSp - 1] : garRootFrame;
        if (!frame.localsReady || u >= frame.localCount) G_FAIL("BAD LOCAL");
        G_PUSH(frame.locals[u]);
        break;
      }
      case 0x64: { // STOREL
        G_U8(u);
        GarCallFrame &frame = (garCallSp > 0) ? garCallFrames[garCallSp - 1] : garRootFrame;
        if (!frame.localsReady || u >= frame.localCount) G_FAIL("BAD LOCAL");
        G_NEED(1);
        frame.locals[u] = G_POP();
        break;
      }

      // ── MEMORY POOL / ARRAYS
      case 0x70: { // LOADM
        G_NEED(1); a = G_POP();
        if ((uint32_t)a >= GAR_MEM) G_FAIL("MEM BOUNDS");
        G_PUSH(garMem[a]);
        break;
      }
      case 0x71: { // STOREM
        G_NEED(2); b = G_POP(); a = G_POP();   // a = idx, b = val
        if ((uint32_t)a >= GAR_MEM) G_FAIL("MEM BOUNDS");
        garMem[a] = b;
        break;
      }
      case 0x72: // CLEARM
        memset(garMem, 0, sizeof(garMem));
        break;

      // ── FIXED-POINT 16.16 ─────────────────────────────────────────
      case 0x80: { // FP_MUL
        G_NEED(2); b = G_POP(); a = G_POP();
        G_PUSH(garWrap64(garFloorDiv65536((int64_t)a * (int64_t)b)));
        break;
      }
      case 0x81: { // FP_DIV
        G_NEED(2); b = G_POP(); a = G_POP();
        if (b == 0) G_FAIL("DIVIDE BY ZERO");
        G_PUSH(garWrap64(((int64_t)a * 65536LL) / (int64_t)b));
        break;
      }
      case 0x82: // TO_FP
        G_NEED(1); a = G_POP();
        G_PUSH(garWrap64((int64_t)a * 65536LL));
        break;
      case 0x83: // FROM_FP
        G_NEED(1); a = G_POP();
        G_PUSH(garWrap64(garFloorDiv65536(a)));
        break;
      case 0x84: { // FP_ROUND
        G_NEED(1); a = G_POP();
        G_PUSH(garWrap64(garFloorDiv65536((int64_t)a + 0x8000LL)));
        break;
      }

      // ── Phase 7: camera + sprites ────────────────────────────────
      case 0x90: { // SETCAM x y
        G_NEED(2); b = G_POP(); a = G_POP();
        garCamX = a;
        garCamY = b;
        break;
      }
      case 0x91: { // SPRITE id x y  (screen space)
        G_NEED(3); c = G_POP(); b = G_POP(); a = G_POP(); // a=id b=x c=y
        if ((uint32_t)a >= GAR_MAX_SPRITES || !garSprites[a].data)
          G_FAIL("BAD SPRITE");
        {
          const uint32_t work = garSpriteVisibleWork((uint8_t)a, b, c);
          if (!garChargeRenderWork(work)) G_FAIL("RENDER LIMIT");
          garDrawSprite((uint8_t)a, b, c);
        }
        break;
      }
      case 0x92: { // SPRITEW id x y  (world space = screen - camera)
        G_NEED(3); c = G_POP(); b = G_POP(); a = G_POP();
        if ((uint32_t)a >= GAR_MAX_SPRITES || !garSprites[a].data)
          G_FAIL("BAD SPRITE");
        {
          const int64_t sx = (int64_t)b - garCamX;
          const int64_t sy = (int64_t)c - garCamY;
          const uint32_t work = garSpriteVisibleWork((uint8_t)a, sx, sy);
          if (!garChargeRenderWork(work)) G_FAIL("RENDER LIMIT");
          garDrawSprite((uint8_t)a, sx, sy);
        }
        break;
      }

      default: G_FAIL("BAD OPCODE");
    }
  }
  G_FAIL("TOO SLOW");
}

// Called instead of renderScreen() while a game is active.
void garTick() {
  if (garPaused) return;               // suspended by pause menu
  if (garRunning) {
    garRunFrame();
    giEndFrame();                      // edges are consumed once per VM frame
    if (garRunning) return;
  }
  // Game ended or errored – show message; B returns to Games list
  display.clearDisplay();
  drawHeader(garError ? "GAME ERROR" : "GAME ENDED");
  display.setTextSize(1);
  display.setTextColor(C_ON);
  display.setCursor(2, 24);
  display.print(garError ? garError : "Game finished.");
  drawFooter("B: BACK");
}

void launchGame(const char *path) {
  // Remember title for the pause menu
  if (path != currentGamePath) {       // RESTART passes currentGamePath itself (overlap = UB)
    strncpy(currentGamePath, path, sizeof(currentGamePath) - 1);
    currentGamePath[sizeof(currentGamePath) - 1] = 0;
  }
  const char *base = strrchr(path, '/');
  base = base ? base + 1 : path;
  size_t n = strlen(base);
  if (n > 4 && (base[n-4]=='.')) n -= 4;
  if (n >= GAME_NAME_LEN) n = GAME_NAME_LEN - 1;
  memcpy(currentGameTitle, base, n);
  currentGameTitle[n] = 0;

  garModeRequested = false;
  garPaused = false;
  pauseSelection = 0;
  display.clearDisplay();               // no leftover menu pixels behind the game
  giEndFrame();
  garSwallowInput = true;              // the A that launched the game must not reach it
  if (!garLoad(path)) {
    Serial.printf("GAR load failed: %s (%s)\n", path, garError ? garError : "unknown error");
  }
  screen = SCREEN_GAME;
}

// During gameplay:
//   B+Y held 0.6 s → open universal pause menu
//   On end/error screen: B → Games list
void gameExitCheck() {
  static uint32_t since = 0;
  static bool pauseArmed = true;  // require combo release after resume

  if (!garRunning) {
    since = 0;
    pauseArmed = true;
    if (pressed(BTN_B)) {
      garStop();
      screen = SCREEN_GAMES;
    }
    return;
  }

  // Reserved pause control: hold B + Y
  bool combo = down(BTN_B) && down(BTN_Y);
  if (!combo) {
    since = 0;
    pauseArmed = true;
  } else if (!pauseArmed) {
    // still holding after CONTINUE/MODE — ignore until release
  } else if (since == 0) {
    since = millis();
  } else if (millis() - since >= PAUSE_HOLD_MS) {
    garPaused = true;
    pauseSelection = 0;
    screen = SCREEN_PAUSE;
    since = 0;
    pauseArmed = false;  // will re-arm on release
  }
}

// ---------- Setup / loop ----------
uint8_t findOLEDAddress() {
  Serial.println(F("Scanning I2C bus..."));
  uint8_t found = 0;
  for (uint8_t address = 1; address < 127; ++address) {
    Wire.beginTransmission(address);
    uint8_t error = Wire.endTransmission();
    if (error == 0) {
      Serial.printf("I2C device found at 0x%02X\n", address);
      if (address == 0x3C || address == 0x3D) found = address;
    }
  }
  if (found == 0) Serial.println(F("No OLED address 0x3C/0x3D found."));
  return found;
}

void setup() {
  Serial.begin(115200);
  Serial.println(F("\n=== GHOST ARCADE STARTUP ==="));

  // Silence the repeated "sdcard_mount failed" log spam when no card is inserted.
  esp_log_level_set("sd_diskio", ESP_LOG_NONE);
  esp_log_level_set("sdmmc_cmd", ESP_LOG_NONE);
  esp_log_level_set("vfs_fat_sdmmc", ESP_LOG_NONE);

  for (int i = 0; i < BTN_COUNT; ++i) {
    pinMode(buttons[i].pin, INPUT_PULLUP);
    buttons[i].rawLast = (digitalRead(buttons[i].pin) == LOW);
    buttons[i].stableLast = buttons[i].rawLast;
    buttons[i].down = buttons[i].stableLast;
    buttons[i].rawChangedAt = millis();
  }

  analogReadResolution(12);
  analogSetPinAttenuation(PIN_JOY_X, ADC_11db);
  analogSetPinAttenuation(PIN_JOY_Y, ADC_11db);

  // Calibrate the stick centre (keep the stick at rest while booting).
  {
    long sx = 0, sy = 0;
    for (int i = 0; i < 16; ++i) {
      sx += analogRead(PIN_JOY_X);
      sy += analogRead(PIN_JOY_Y);
      delay(2);
    }
    const int cx = (int)(sx / 16), cy = (int)(sy / 16);
    if (cx > 1500 && cx < 2600) joyCenX = cx;
    if (cy > 1500 && cy < 2600) joyCenY = cy;
    joyX = joyCenX;
    joyY = joyCenY;
    Serial.printf("Joystick centre: X=%d Y=%d\n", joyCenX, joyCenY);
  }

  // Saved display settings
  prefsReady = prefs.begin("ghostarcade", false);
  if (prefsReady) {
    invertDisplay = prefs.getBool("inv", false);
    contrastValue = prefs.getUChar("ctr", contrastValue);
  }

  Wire.begin(PIN_OLED_SDA, PIN_OLED_SCL);
  Wire.setClock(100000);

  uint8_t detectedAddress = findOLEDAddress();
  if (detectedAddress != 0) {
    Wire.setClock(400000);
    displayReady = display.begin(detectedAddress, true);
    if (displayReady) {
      display.setContrast(contrastValue);
      display.invertDisplay(invertDisplay);
      display.setTextWrap(false);   // games/menus never wrap text onto the next line
      cvA = new (std::nothrow) GFXcanvas1(128, 64);
      cvB = new (std::nothrow) GFXcanvas1(128, 64);
      if (!cvA || !cvB || !cvA->getBuffer() || !cvB->getBuffer()) {
        Serial.println(F("WARN: boot canvas alloc failed (no dissolve)"));
        delete cvA; cvA = nullptr;
        delete cvB; cvB = nullptr;
      }
    } else {
      Serial.println(F("SH1106 driver initialization failed."));
    }
  } else {
    Serial.println(F("OLED not detected. Check power, GND, SDA=21, SCL=22."));
  }

  // SD runs entirely in its own task: the UI never waits for it.
  sdSPI.begin(PIN_SD_SCK, PIN_SD_MISO, PIN_SD_MOSI, PIN_SD_CS);
  sdMutex = xSemaphoreCreateMutex();
  if (!sdMutex) {
    Serial.println(F("FATAL: sdMutex create failed"));
  } else {
    BaseType_t ok = xTaskCreatePinnedToCore(sdTask, "sdTask", 8192, nullptr, 1, nullptr, 0);
    if (ok != pdPASS) {
      Serial.println(F("FATAL: sdTask create failed"));
    }
  }

  bootStartedAt = millis();
  screen = displayReady ? SCREEN_BOOT : SCREEN_DIAGNOSTICS;
  Serial.println(F("GHOST ARCADE M1 + GAR1 extensions running."));
}

static uint8_t frameBackup[128 * 64 / 8];   // game frame without the SD popup on top

void loop() {
  updateInputs();
  giUpdate();
  pollSdEvents();
  syncGamesWithSd();

#if DEBUG_RAW_SERIAL
  if (millis() - lastRawAt >= 250) {
    lastRawAt = millis();
    Serial.printf("X=%d Y=%d SW=%d A=%d B=%d Xbtn=%d Ybtn=%d SD=%d\n",
      joyX, joyY, down(BTN_JOY) ? 0 : 1, down(BTN_A) ? 0 : 1,
      down(BTN_B) ? 0 : 1, down(BTN_X) ? 0 : 1, down(BTN_Y) ? 0 : 1,
      sdReady ? 1 : 0);
  }
#endif

  // Edges live for one loop pass only, so the boot skip is handled here (not in the
  // renderer), and the skipping press is consumed instead of also acting on Home.
  if (screen == SCREEN_BOOT) {
    if (anyPressed()) screen = SCREEN_HOME;
  } else if (screen == SCREEN_GAME) {
    gameExitCheck();
  } else {
    handleNavigation();
  }

  const uint32_t now = millis();
  if (now - lastFrameAt >= FRAME_INTERVAL_MS) {
    lastFrameAt = now;
    if (displayReady) {
      const bool inGame = (screen == SCREEN_GAME);
      if (inGame) garTick(); else renderScreen();

      if (showSdPopup) {
        // Games may not clear the screen every frame: draw the popup on top, push the
        // frame, then restore the clean game frame so the popup leaves no ghost pixels.
        uint8_t *fb = display.getBuffer();
        if (inGame && fb) memcpy(frameBackup, fb, sizeof(frameBackup));
        drawSdPopup();
        display.display();
        if (inGame && fb) memcpy(fb, frameBackup, sizeof(frameBackup));
      } else {
        display.display();
      }
    }
  }

  delay(1);   // yield: lets the idle task run and saves power (debounce is 25 ms)
}
