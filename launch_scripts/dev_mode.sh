#!/bin/bash
# Launch Runetika in development mode with hot reload

echo "🔧 Launching Runetika Development Mode..."
cd "$(dirname "$0")/.."
cargo watch -x run