# Ghost Arcade (GAR1 MERGED FINAL) - Code Review

This document provides an overview of the firmware architecture, identified dependencies, potential bugs, and suggestions for improvements for the Ghost Arcade project.

## 1. Architecture and Code Structure

The codebase is contained entirely within a single large file (`GhostArcade_M1_MERGED_FINAL.ino`, ~2600 lines). It functions as the firmware for an ESP32-based portable game console and consists of several key subsystems:

*   **Hardware Abstraction & Input Handling (`updateInputs`):** Manages the physical inputs (Joystick + 5 buttons). It provides software debouncing and tracks state changes (pressed, released, held) using `millis()`.
*   **Display & UI State Machine:** The system uses a centralized state machine (`enum Mode { BOOT, HOME, GAMES, PLAY, PAUSE, SETTINGS, ERROR }`). It handles screen rendering via the `Adafruit_SH110X` library, including a detailed boot sequence with dissolve transitions and an interactive menu system.
*   **SD Card Management (FreeRTOS Task):** To prevent blocking the UI, SD card polling and mounting are offloaded to a dedicated FreeRTOS task (`sdTask`) running on Core 0. The main thread (Core 1) communicates with this task using atomic variables (`sdEvent`) and a mutex (`sdMutex`) to safely coordinate file access.
*   **Game Management & Validation:** Scans the SD card for `.gar` files. It employs a two-tier validation approach:
    *   *Lightweight structural validation* during scanning to keep memory usage low.
    *   *Full validation* (`garValidateBuffer`) upon loading, which verifies bytecode integrity, checks instruction boundaries, and ensures absolute jumps/calls are valid.
*   **GAR1 Virtual Machine (VM):** A custom, robust stack-based interpreter that executes game bytecode.
    *   **Safety mechanisms:** It enforces a strictly bounded execution environment. Includes a call stack, local variables, bounds checking for memory/stack access, and explicit wrapping for integer arithmetic to prevent undefined behavior.
    *   **Render Budgeting:** It tracks rendering work (`garRenderWork`) to prevent malicious or poorly written games from causing infinite loops or triggering the ESP32 hardware watchdog (WDT).
    *   **Clipped Graphics:** All VM drawing routines (pixels, rects, lines, sprites) use custom clipping helpers to guarantee they cannot draw outside the 128x64 display buffer.

## 2. Dependencies and Hardware

*   **Microcontroller:** ESP32 (Specifically designed for DevKit V1 layouts).
*   **Display:** 128x64 I2C OLED (SH1106G or compatible).
*   **Storage:** MicroSD Card via SPI adapter.
*   **Inputs:** Analog Joystick (X/Y axes + push button) and 4 digital push buttons (A, B, X, Y).
*   **Required Arduino Libraries:**
    *   `Adafruit_GFX` (Core graphics)
    *   `Adafruit_SH110X` (OLED driver)
    *   Standard ESP32 packages (`Preferences`, `SD`, `SPI`, `Wire`, `freertos`)

## 3. Potential Bugs and Concerns

While the code is well-structured and highly defensive (especially the VM), there are a few areas of concern:

1.  **Floating-Point Math in VM (`garDrawLineClipped`):** The line clipping function uses `double` precision for its calculations. The ESP32's FPU only supports single-precision (`float`); `double` is emulated via software and is significantly slower. Running this extensively within VM graphics operations could lead to performance bottlenecks.
2.  **Strapping Pin Conflict (GPIO5):** As noted in the comments, GPIO5 is used for the SD card CS (Chip Select). GPIO5 is a strapping pin on the ESP32 that controls the boot timing. If the SD card adapter pulls this pin LOW during a hardware reset, the ESP32 will fail to boot.
3.  **SD SPI Speed:** `SD_SPI_HZ` is set to `1000000` (1 MHz). While this ensures reliability on messy jumper wires, it is quite slow. If loading larger `.gar` packages or parsing many files, this may cause noticeable UI stutters during synchronous operations.

## 4. Suggested Improvements

1.  **Code Modularization:** Split the massive `.ino` file into smaller, focused C++ files (`UI.cpp`, `VM.cpp`, `Input.cpp`, `SD_Task.cpp`). This will greatly improve maintainability, readability, and collaboration.
2.  **Fixed-Point Line Clipping:** Replace the `double` floating-point logic in `garDrawLineClipped` with an integer or fixed-point based Cohen-Sutherland line clipping algorithm. This will dramatically improve the performance of line drawing.
3.  **Optimized SPI Speed:** Consider increasing `SD_SPI_HZ` to `4000000` (4 MHz) or higher, possibly adding a fallback mechanism. Most generic SD adapters can comfortably handle 4-10 MHz even on breadboards.
4.  **Interrupt-Based Input Handling (Optional):** While polling via `updateInputs()` at ~33ms intervals is sufficient for many games, using hardware interrupts or a high-frequency FreeRTOS software timer for the buttons could capture extremely brief button presses more reliably.
