#!/bin/bash
set -e

echo "Downloading Arduino CLI..."
curl -fsSL https://raw.githubusercontent.com/arduino/arduino-cli/master/install.sh > install_arduino_cli.sh
bash install_arduino_cli.sh
rm install_arduino_cli.sh

export PATH=$PATH:$(pwd)/bin

echo "Initializing config..."
arduino-cli config init || true

echo "Setting ESP32 board manager URL..."
arduino-cli config set board_manager.additional_urls https://raw.githubusercontent.com/espressif/arduino-esp32/gh-pages/package_esp32_index.json

echo "Updating index..."
arduino-cli core update-index

echo "Installing esp32 core..."
arduino-cli core install esp32:esp32

echo "Done!"
