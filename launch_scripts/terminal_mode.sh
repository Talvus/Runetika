#!/bin/bash
# Launch Runetika in terminal mode

echo "💻 Launching Runetika Terminal Mode..."
cd "$(dirname "$0")/.."
cargo run --release --features terminal-only