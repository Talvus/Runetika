#!/bin/bash
# Build script for iOS static library

set -e

echo "Building Runetika for iOS..."

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if we have the iOS targets installed
check_target() {
    local target=$1
    if ! rustup target list --installed | grep -q "$target"; then
        echo -e "${YELLOW}Installing target: $target${NC}"
        rustup target add "$target"
    fi
}

# Install required iOS targets
echo -e "${GREEN}Checking iOS targets...${NC}"
check_target "aarch64-apple-ios"
check_target "aarch64-apple-ios-sim"
check_target "x86_64-apple-ios"

# Create output directory
OUTPUT_DIR="build/ios"
mkdir -p "$OUTPUT_DIR"

# Build for iOS device (ARM64)
echo -e "${GREEN}Building for iOS device (arm64)...${NC}"
cargo build --target aarch64-apple-ios --release --features ios-ffi --lib
cp target/aarch64-apple-ios/release/librunetika.a "$OUTPUT_DIR/librunetika_device.a"

# Build for iOS simulator (ARM64 - Apple Silicon Macs)
echo -e "${GREEN}Building for iOS simulator (arm64)...${NC}"
cargo build --target aarch64-apple-ios-sim --release --features ios-ffi --lib
cp target/aarch64-apple-ios-sim/release/librunetika.a "$OUTPUT_DIR/librunetika_sim_arm64.a"

# Build for iOS simulator (x86_64 - Intel Macs)
echo -e "${GREEN}Building for iOS simulator (x86_64)...${NC}"
cargo build --target x86_64-apple-ios --release --features ios-ffi --lib
cp target/x86_64-apple-ios/release/librunetika.a "$OUTPUT_DIR/librunetika_sim_x86_64.a"

# Create universal binary for simulator
echo -e "${GREEN}Creating universal simulator library...${NC}"
lipo -create \
    "$OUTPUT_DIR/librunetika_sim_arm64.a" \
    "$OUTPUT_DIR/librunetika_sim_x86_64.a" \
    -output "$OUTPUT_DIR/librunetika_simulator.a"

# Create XCFramework
echo -e "${GREEN}Creating XCFramework...${NC}"
rm -rf "$OUTPUT_DIR/Runetika.xcframework"
xcodebuild -create-xcframework \
    -library "$OUTPUT_DIR/librunetika_device.a" \
    -headers "ios" \
    -library "$OUTPUT_DIR/librunetika_simulator.a" \
    -headers "ios" \
    -output "$OUTPUT_DIR/Runetika.xcframework"

# Copy header file
cp ios/runetika.h "$OUTPUT_DIR/"

echo -e "${GREEN}✅ Build complete!${NC}"
echo -e "${GREEN}Output files:${NC}"
echo "  - $OUTPUT_DIR/librunetika_device.a (iOS device)"
echo "  - $OUTPUT_DIR/librunetika_simulator.a (iOS simulator)"
echo "  - $OUTPUT_DIR/Runetika.xcframework (Universal framework)"
echo "  - $OUTPUT_DIR/runetika.h (C header)"

echo -e "\n${YELLOW}To use in Xcode:${NC}"
echo "1. Add Runetika.xcframework to your project"
echo "2. Add runetika.h to your bridging header"
echo "3. Link with system libraries: Metal, CoreMotion, AVFoundation"
echo "4. Enable 'Allow Non-modular Includes' in build settings"