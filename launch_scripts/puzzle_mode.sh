#!/bin/bash
# Launch Runetika puzzle mode

echo "🧩 Launching Runetika Puzzle Mode..."
cd "$(dirname "$0")/.."
cargo run --release --features puzzle-only