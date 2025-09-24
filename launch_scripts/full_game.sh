#!/bin/bash
# Launch full Runetika game

echo "🎮 Launching Runetika..."
cd "$(dirname "$0")/.."
cargo run --release