#!/bin/bash
# Runetika Quick Run Script - Optimized for fastest iteration

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${BLUE}🎮 Runetika - Quick Launch${NC}"
echo -e "${YELLOW}Using optimized build configuration...${NC}"

# Use the fastest development build profile
CARGO_PROFILE=dev-fast

# Enable all performance optimizations
export RUSTFLAGS="-C target-cpu=native -C opt-level=2 -C debuginfo=0"

# Use all CPU cores
export CARGO_BUILD_JOBS=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Run with the optimized profile
echo -e "${GREEN}Starting Runetika...${NC}"
cargo run --profile dev-fast --features "bevy/dynamic_linking" 2>/dev/null || cargo run --profile dev-fast

# Alternative: if you want the absolute fastest startup with no compilation check:
# ./target/dev-fast/runetika