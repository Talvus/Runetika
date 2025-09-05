#!/bin/bash
# Launch script for Runetika

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}🚀 Launching Runetika...${NC}"

# Check if cargo is installed
if ! command -v cargo &> /dev/null; then
    echo "Error: Cargo is not installed. Please install Rust first."
    echo "Visit: https://rustup.rs/"
    exit 1
fi

# Run in release mode for best performance
echo -e "${GREEN}Building and running in release mode...${NC}"
cargo run --release

# If you prefer debug mode for faster compilation, comment above and uncomment below:
# echo -e "${GREEN}Building and running in debug mode...${NC}"
# cargo run