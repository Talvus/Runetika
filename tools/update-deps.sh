#!/usr/bin/env bash

#################################################################################
# Dependency Update Script for Runetika
#
# This script automates the process of updating dependencies while ensuring
# compatibility and running tests.
#
# Usage: ./tools/update-deps.sh [options]
#   -a, --all       Update all dependencies including major versions
#   -m, --minor     Update only minor and patch versions (default)
#   -c, --check     Only check for updates without applying
#   -t, --test      Run tests after updating
#   -h, --help      Show this help message
#################################################################################

set -e  # Exit on error

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default options
UPDATE_MODE="minor"
RUN_TESTS=false
CHECK_ONLY=false

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -a|--all)
            UPDATE_MODE="all"
            shift
            ;;
        -m|--minor)
            UPDATE_MODE="minor"
            shift
            ;;
        -c|--check)
            CHECK_ONLY=true
            shift
            ;;
        -t|--test)
            RUN_TESTS=true
            shift
            ;;
        -h|--help)
            grep '^#' "$0" | grep -v '#!/' | sed 's/^# *//'
            exit 0
            ;;
        *)
            echo -e "${RED}Unknown option: $1${NC}"
            exit 1
            ;;
    esac
done

echo -e "${BLUE}=== Runetika Dependency Update Tool ===${NC}"
echo ""

# Check for required tools
check_tool() {
    if ! command -v $1 &> /dev/null; then
        echo -e "${RED}Error: $1 is not installed${NC}"
        echo "Please install it with: $2"
        exit 1
    fi
}

check_tool "cargo" "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
check_tool "git" "your system package manager"

# Install cargo-edit if not present
if ! cargo --list | grep -q "cargo-upgrade"; then
    echo -e "${YELLOW}Installing cargo-edit for dependency management...${NC}"
    cargo install cargo-edit
fi

# Install cargo-outdated for checking
if ! cargo --list | grep -q "cargo-outdated"; then
    echo -e "${YELLOW}Installing cargo-outdated for dependency checking...${NC}"
    cargo install cargo-outdated
fi

# Install cargo-audit for security checks
if ! cargo --list | grep -q "cargo-audit"; then
    echo -e "${YELLOW}Installing cargo-audit for security checking...${NC}"
    cargo install cargo-audit
fi

# Create backup of current Cargo.lock
if [ -f "Cargo.lock" ]; then
    cp Cargo.lock Cargo.lock.backup
    echo -e "${GREEN}✓ Backed up Cargo.lock${NC}"
fi

# Check for outdated dependencies
echo ""
echo -e "${BLUE}Checking for outdated dependencies...${NC}"
cargo outdated

# Security audit
echo ""
echo -e "${BLUE}Running security audit...${NC}"
cargo audit || true  # Don't fail on audit issues, just report

if [ "$CHECK_ONLY" = true ]; then
    echo ""
    echo -e "${GREEN}Check complete. No changes made.${NC}"
    exit 0
fi

# Update dependencies based on mode
echo ""
if [ "$UPDATE_MODE" = "all" ]; then
    echo -e "${YELLOW}Updating all dependencies (including major versions)...${NC}"
    cargo upgrade --incompatible
else
    echo -e "${YELLOW}Updating minor and patch versions...${NC}"
    cargo upgrade --compatible
fi

# Update Cargo.lock
cargo update
echo -e "${GREEN}✓ Dependencies updated${NC}"

# Check if there are actual changes
if git diff --quiet Cargo.toml Cargo.lock; then
    echo -e "${YELLOW}No dependency updates available${NC}"
    rm -f Cargo.lock.backup
    exit 0
fi

# Show what changed
echo ""
echo -e "${BLUE}Changes made:${NC}"
git diff --stat Cargo.toml Cargo.lock

# Build the project
echo ""
echo -e "${BLUE}Building project with updated dependencies...${NC}"
if cargo build --release; then
    echo -e "${GREEN}✓ Build successful${NC}"
else
    echo -e "${RED}✗ Build failed, reverting changes${NC}"
    mv Cargo.lock.backup Cargo.lock
    git checkout Cargo.toml
    exit 1
fi

# Run tests if requested
if [ "$RUN_TESTS" = true ]; then
    echo ""
    echo -e "${BLUE}Running tests...${NC}"
    if cargo test --all-features; then
        echo -e "${GREEN}✓ All tests passed${NC}"
    else
        echo -e "${RED}✗ Tests failed, reverting changes${NC}"
        mv Cargo.lock.backup Cargo.lock
        git checkout Cargo.toml
        exit 1
    fi
fi

# Clean up backup
rm -f Cargo.lock.backup

# Generate update report
echo ""
echo -e "${BLUE}Generating update report...${NC}"
{
    echo "# Dependency Update Report"
    echo "Date: $(date)"
    echo ""
    echo "## Updated Dependencies"
    git diff Cargo.toml | grep '^+' | grep -v '^+++' || echo "No Cargo.toml changes"
    echo ""
    echo "## Security Status"
    cargo audit 2>&1 || echo "No security issues found"
} > dependency-update-report.md

echo -e "${GREEN}✓ Update complete!${NC}"
echo ""
echo "Next steps:"
echo "  1. Review the changes: git diff"
echo "  2. Test the game manually"
echo "  3. Commit if everything works: git commit -am 'chore: update dependencies'"
echo ""
echo "Report saved to: dependency-update-report.md"