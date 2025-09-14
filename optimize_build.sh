#!/bin/bash

# Runetika Build Optimization Script
# Measures and optimizes compilation times

set -e

echo "╔══════════════════════════════════════════════════════════╗"
echo "║         Runetika Build Performance Optimizer              ║"
echo "╚══════════════════════════════════════════════════════════╝"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to measure build time
measure_build() {
    local profile=$1
    local features=$2
    local description=$3
    
    echo -e "\n${BLUE}Testing: ${description}${NC}"
    
    # Clean to ensure fresh build
    cargo clean 2>/dev/null || true
    
    # Measure build time
    local start_time=$(date +%s)
    
    if [ -z "$features" ]; then
        cargo build --profile="$profile" 2>&1 | tail -5
    else
        cargo build --profile="$profile" --features="$features" 2>&1 | tail -5
    fi
    
    local end_time=$(date +%s)
    local build_time=$((end_time - start_time))
    
    echo -e "${GREEN}Build time: ${build_time} seconds${NC}"
    
    return $build_time
}

# Check system info
echo -e "\n${YELLOW}System Information:${NC}"
echo "CPU: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || lscpu | grep 'Model name' | cut -d: -f2 | xargs)"
echo "Cores: $(sysctl -n hw.ncpu 2>/dev/null || nproc)"
echo "RAM: $(sysctl -n hw.memsize 2>/dev/null | awk '{print $1/1024/1024/1024 " GB"}' || free -h | grep Mem | awk '{print $2}')"
echo "Rust: $(rustc --version)"
echo "Cargo: $(cargo --version)"

# Check for optimization tools
echo -e "\n${YELLOW}Checking optimization tools:${NC}"

# Check for sccache
if command -v sccache &> /dev/null; then
    echo -e "${GREEN}✓ sccache found${NC}"
    export RUSTC_WRAPPER=sccache
    sccache --start-server 2>/dev/null || true
else
    echo -e "${YELLOW}✗ sccache not found (install with: cargo install sccache)${NC}"
fi

# Check for mold linker (Linux)
if command -v mold &> /dev/null; then
    echo -e "${GREEN}✓ mold linker found${NC}"
elif command -v lld &> /dev/null; then
    echo -e "${GREEN}✓ lld linker found${NC}"
else
    echo -e "${YELLOW}✗ Fast linker not found${NC}"
fi

# Test different build configurations
echo -e "\n${YELLOW}Running build performance tests...${NC}"

# Array to store results
declare -a results

# Test 1: Standard dev build
measure_build "dev" "" "Standard dev build"
results[0]=$?

# Test 2: Dev build with fast-compile feature
measure_build "dev" "fast-compile" "Dev build with fast-compile"
results[1]=$?

# Test 3: Fast-runtime profile
measure_build "fast-runtime" "fast-compile" "Fast-runtime profile"
results[2]=$?

# Test 4: Check if dynamic linking helps
export CARGO_BUILD_RUSTFLAGS="-C prefer-dynamic"
measure_build "dev" "fast-compile" "Dev with dynamic linking"
results[3]=$?
unset CARGO_BUILD_RUSTFLAGS

# Generate optimization report
echo -e "\n${YELLOW}═══════════════════════════════════════════════════════════${NC}"
echo -e "${YELLOW}                    Optimization Report                       ${NC}"
echo -e "${YELLOW}═══════════════════════════════════════════════════════════${NC}"

# Find fastest configuration
min_time=${results[0]}
min_index=0
for i in "${!results[@]}"; do
    if [ ${results[$i]} -lt $min_time ]; then
        min_time=${results[$i]}
        min_index=$i
    fi
done

configs=("Standard dev" "Dev with fast-compile" "Fast-runtime" "Dynamic linking")
echo -e "\n${GREEN}Fastest configuration: ${configs[$min_index]} (${min_time}s)${NC}"

# Provide recommendations
echo -e "\n${YELLOW}Recommendations:${NC}"

if [ $min_time -gt 30 ]; then
    echo "• Build time exceeds 30s target. Consider:"
    echo "  - Enable fast-compile feature by default"
    echo "  - Use cargo check for rapid iteration"
    echo "  - Split large modules into smaller crates"
    echo "  - Reduce dependencies or use fewer features"
fi

if ! command -v sccache &> /dev/null; then
    echo "• Install sccache for build caching: cargo install sccache"
fi

if [[ "$OSTYPE" == "linux-gnu"* ]] && ! command -v mold &> /dev/null; then
    echo "• Install mold linker for faster linking: sudo apt install mold"
fi

echo -e "\n${YELLOW}Quick commands for fast development:${NC}"
echo "• Fast check:     cargo ch"
echo "• Fast build:     cargo dev"
echo "• Fast run:       cargo run-fast"
echo "• Production:     cargo prod"

# Test incremental compilation effectiveness
echo -e "\n${YELLOW}Testing incremental compilation...${NC}"

# First build
cargo build --profile=dev 2>&1 > /dev/null
# Make a small change
echo "// Incremental test" >> src/main.rs
# Measure incremental build
start_time=$(date +%s)
cargo build --profile=dev 2>&1 | tail -3
end_time=$(date +%s)
incremental_time=$((end_time - start_time))

# Restore file
sed -i.bak '$d' src/main.rs && rm src/main.rs.bak 2>/dev/null || true

echo -e "${GREEN}Incremental build time: ${incremental_time}s${NC}"

if [ $incremental_time -gt 5 ]; then
    echo -e "${YELLOW}Incremental compilation could be improved${NC}"
fi

echo -e "\n${GREEN}Optimization complete!${NC}"

# Create optimized build script
cat > fast_build.sh << 'EOF'
#!/bin/bash
# Fast build script with optimal settings
export CARGO_BUILD_JOBS=-1
export CARGO_INCREMENTAL=1
export CARGO_BUILD_PIPELINING=true

# Use fast-compile feature and optimal profile
exec cargo build --features=fast-compile
EOF

chmod +x fast_build.sh
echo -e "\n${GREEN}Created fast_build.sh for optimized builds${NC}"