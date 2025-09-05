#!/bin/bash

echo "Building and running Runetika - Main Room Test"
echo "=============================================="
echo ""
echo "Controls:"
echo "  • WASD or Arrow Keys: Move the blue dot"
echo "  • R: Reset position to center"
echo "  • Space: Show current position"
echo "  • ESC: Return to main menu"
echo ""
echo "Building project..."

# Try to build with reduced output
cargo build 2>&1 | grep -E "Compiling runetika|Finished|error"

if [ $? -eq 0 ]; then
    echo "Build complete! Launching game..."
    echo ""
    cargo run
else
    echo "Build failed. Checking for errors..."
    cargo check 2>&1 | tail -20
fi