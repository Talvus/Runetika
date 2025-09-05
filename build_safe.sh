#!/bin/bash
# Memory-safe build script for Runetika
# Use this when regular cargo build crashes your system

echo "🚀 Starting memory-safe build for Runetika..."
echo "This build uses reduced parallelism and memory optimizations"

# Set environment variables for low memory usage
export CARGO_BUILD_JOBS=1
export CARGO_INCREMENTAL=1
export RUSTC_FORCE_INCREMENTAL=1
export CARGO_NET_OFFLINE=true  # Avoid network operations during build

# Clear previous build cache if needed (uncomment if you have issues)
# cargo clean

# Build with the fast-dev profile for minimum memory usage
echo "Building with memory-efficient settings..."
cargo build --profile fast-dev

# Alternative: Use regular dev profile with limited jobs
# cargo build -j 1

echo "✅ Build complete!"
echo ""
echo "Tips for reducing memory usage further:"
echo "  1. Close other applications before building"
echo "  2. Run 'cargo clean' if you haven't in a while"
echo "  3. Use 'cargo check' instead of 'cargo build' for syntax checking"
echo "  4. Consider using 'sccache' for caching compiled dependencies"