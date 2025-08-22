#!/bin/bash

# Comprehensive Debug Analysis Script for Runetika
# This script provides thorough analysis of the codebase, dependencies, and potential issues

set -e

echo "🔍 Starting comprehensive debug analysis for Runetika..."
echo "=================================================="

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    local status=$1
    local message=$2
    case $status in
        "SUCCESS") echo -e "${GREEN}✅ $message${NC}" ;;
        "WARNING") echo -e "${YELLOW}⚠️  $message${NC}" ;;
        "ERROR") echo -e "${RED}❌ $message${NC}" ;;
        "INFO") echo -e "${BLUE}ℹ️  $message${NC}" ;;
    esac
}

# Change to project root
cd "$(dirname "$0")/.."

print_status "INFO" "Project root: $(pwd)"

# 1. RUST ENVIRONMENT ANALYSIS
echo ""
echo "🦀 Rust Environment Analysis"
echo "---------------------------"

if command -v rustc &> /dev/null; then
    RUST_VERSION=$(rustc --version)
    print_status "SUCCESS" "Rust compiler: $RUST_VERSION"
    
    if command -v cargo &> /dev/null; then
        CARGO_VERSION=$(cargo --version)
        print_status "SUCCESS" "Cargo: $CARGO_VERSION"
        
        # Check Rust toolchain
        if [ -f "rust-toolchain.toml" ]; then
            print_status "INFO" "Custom Rust toolchain configured"
        else
            print_status "WARNING" "No custom Rust toolchain specified"
        fi
    else
        print_status "ERROR" "Cargo not found"
    fi
else
    print_status "ERROR" "Rust compiler not found"
fi

# 2. DEPENDENCY ANALYSIS
echo ""
echo "📦 Dependency Analysis"
echo "---------------------"

if [ -f "Cargo.toml" ]; then
    print_status "SUCCESS" "Cargo.toml found"
    
    # Check for dependency vulnerabilities
    if command -v cargo &> /dev/null; then
        echo "   Checking for outdated dependencies..."
        OUTDATED=$(cargo outdated 2>/dev/null | grep -E "^[a-zA-Z]" | wc -l || echo "0")
        if [ "$OUTDATED" -gt 0 ]; then
            print_status "WARNING" "Found $OUTDATED outdated dependencies"
        else
            print_status "SUCCESS" "All dependencies are up to date"
        fi
        
        # Check for duplicate dependencies
        echo "   Checking for duplicate dependencies..."
        DUPLICATES=$(cargo tree --duplicates 2>/dev/null | grep -E "(WARNING|duplicate)" | wc -l || echo "0")
        if [ "$DUPLICATES" -gt 0 ]; then
            print_status "WARNING" "Found $DUPLICATES duplicate dependencies"
        else
            print_status "SUCCESS" "No duplicate dependencies found"
        fi
    fi
else
    print_status "ERROR" "Cargo.toml not found"
fi

# 3. CODE QUALITY ANALYSIS
echo ""
echo "🔍 Code Quality Analysis"
echo "-----------------------"

# Count lines of code
TOTAL_LINES=$(find src/ -name "*.rs" -exec wc -l {} + | tail -1 | awk '{print $1}' || echo "0")
print_status "INFO" "Total lines of Rust code: $TOTAL_LINES"

# Check for common code smells
echo "   Analyzing code patterns..."

# TODO/FIXME comments
TODO_COUNT=$(grep -r "TODO\|FIXME\|XXX\|HACK" src/ 2>/dev/null | wc -l || echo "0")
if [ "$TODO_COUNT" -gt 0 ]; then
    print_status "WARNING" "Found $TODO_COUNT TODO/FIXME comments"
    echo "   Details:"
    grep -r "TODO\|FIXME\|XXX\|HACK" src/ 2>/dev/null | head -5 | sed 's/^/     /'
    if [ "$TODO_COUNT" -gt 5 ]; then
        echo "     ... and $((TODO_COUNT - 5)) more"
    fi
else
    print_status "SUCCESS" "No TODO/FIXME comments found"
fi

# Unwrap/expect/panic calls
UNSAFE_COUNT=$(grep -r "unwrap\|expect\|panic" src/ 2>/dev/null | wc -l || echo "0")
if [ "$UNSAFE_COUNT" -gt 0 ]; then
    print_status "WARNING" "Found $UNSAFE_COUNT unwrap/expect/panic calls"
    echo "   Details:"
    grep -r "unwrap\|expect\|panic" src/ 2>/dev/null | head -5 | sed 's/^/     /'
    if [ "$UNSAFE_COUNT" -gt 5 ]; then
        echo "     ... and $((UNSAFE_COUNT - 5)) more"
    fi
else
    print_status "SUCCESS" "No unwrap/expect/panic calls found"
fi

# Hardcoded values
HARDCODED_COUNT=$(grep -r "magic\|hardcoded\|123\|999\|1000" src/ 2>/dev/null | wc -l || echo "0")
if [ "$HARDCODED_COUNT" -gt 0 ]; then
    print_status "WARNING" "Found $HARDCODED_COUNT potential hardcoded values"
else
    print_status "SUCCESS" "No obvious hardcoded values found"
fi

# 4. COMPILATION AND TESTING
echo ""
echo "🏗️  Compilation and Testing"
echo "---------------------------"

if command -v cargo &> /dev/null; then
    echo "   Running cargo check..."
    if cargo check --quiet; then
        print_status "SUCCESS" "Code compiles successfully"
    else
        print_status "ERROR" "Code compilation failed"
        exit 1
    fi
    
    echo "   Running cargo clippy..."
    if cargo clippy -- -D warnings 2>/dev/null; then
        print_status "SUCCESS" "Clippy linting passed"
    else
        print_status "WARNING" "Clippy found issues"
    fi
    
    echo "   Checking test compilation..."
    if cargo test --no-run --quiet; then
        print_status "SUCCESS" "Tests compile successfully"
        
        # Count tests
        TEST_COUNT=$(cargo test --no-run --quiet 2>&1 | grep -E "test result.*passed" | sed 's/.*passed \([0-9]*\) .*/\1/' || echo "0")
        print_status "INFO" "Found $TEST_COUNT tests"
    else
        print_status "WARNING" "Test compilation failed"
    fi
else
    print_status "ERROR" "Cargo not available for compilation checks"
fi

# 5. PERFORMANCE ANALYSIS
echo ""
echo "⚡ Performance Analysis"
echo "----------------------"

# Check for performance anti-patterns
echo "   Analyzing performance patterns..."

# Check for potential memory leaks
MEMORY_PATTERNS=$(grep -r "Box::leak\|std::mem::forget\|ManuallyDrop" src/ 2>/dev/null | wc -l || echo "0")
if [ "$MEMORY_PATTERNS" -gt 0 ]; then
    print_status "WARNING" "Found $MEMORY_PATTERNS potential memory leak patterns"
else
    print_status "SUCCESS" "No obvious memory leak patterns found"
fi

# Check for expensive operations in loops
EXPENSIVE_LOOPS=$(grep -r "for.*in.*collect\|for.*in.*clone" src/ 2>/dev/null | wc -l || echo "0")
if [ "$EXPENSIVE_LOOPS" -gt 0 ]; then
    print_status "WARNING" "Found $EXPENSIVE_LOOPS potentially expensive loop operations"
else
    print_status "SUCCESS" "No obvious expensive loop operations found"
fi

# 6. SECURITY ANALYSIS
echo ""
echo "🔒 Security Analysis"
echo "-------------------"

# Check for common security issues
echo "   Checking for security vulnerabilities..."

# Check for unsafe blocks
UNSAFE_BLOCKS=$(grep -r "unsafe" src/ 2>/dev/null | wc -l || echo "0")
if [ "$UNSAFE_BLOCKS" -gt 0 ]; then
    print_status "WARNING" "Found $UNSAFE_BLOCKS unsafe blocks"
    echo "   Details:"
    grep -r "unsafe" src/ 2>/dev/null | head -3 | sed 's/^/     /'
else
    print_status "SUCCESS" "No unsafe blocks found"
fi

# Check for potential integer overflow
OVERFLOW_PATTERNS=$(grep -r "overflow\|wrapping\|saturating" src/ 2>/dev/null | wc -l || echo "0")
if [ "$OVERFLOW_PATTERNS" -gt 0 ]; then
    print_status "INFO" "Found $OVERFLOW_PATTERNS overflow handling patterns"
else
    print_status "WARNING" "No explicit overflow handling found"
fi

# 7. DOCUMENTATION ANALYSIS
echo ""
echo "📚 Documentation Analysis"
echo "------------------------"

# Check documentation coverage
DOC_COMMENTS=$(grep -r "///\|//!" src/ 2>/dev/null | wc -l || echo "0")
if [ "$DOC_COMMENTS" -gt 0 ]; then
    print_status "SUCCESS" "Found $DOC_COMMENTS documentation comments"
    
    # Calculate rough documentation ratio
    if [ "$TOTAL_LINES" -gt 0 ]; then
        DOC_RATIO=$((DOC_COMMENTS * 100 / TOTAL_LINES))
        if [ "$DOC_RATIO" -gt 10 ]; then
            print_status "SUCCESS" "Documentation ratio: $DOC_RATIO% (good coverage)"
        else
            print_status "WARNING" "Documentation ratio: $DOC_RATIO% (could be improved)"
        fi
    fi
else
    print_status "WARNING" "No documentation comments found"
fi

# Check for README and other docs
if [ -f "README.md" ]; then
    README_SIZE=$(wc -c < README.md)
    if [ "$README_SIZE" -gt 1000 ]; then
        print_status "SUCCESS" "README.md exists and substantial ($README_SIZE bytes)"
    else
        print_status "WARNING" "README.md exists but may be too brief"
    fi
else
    print_status "ERROR" "README.md not found"
fi

# 8. PROJECT STRUCTURE ANALYSIS
echo ""
echo "🏗️  Project Structure Analysis"
echo "-----------------------------"

# Check for common project files
MISSING_FILES=()
[ ! -f "LICENSE" ] && MISSING_FILES+=("LICENSE")
[ ! -f ".gitignore" ] && MISSING_FILES+=(".gitignore")
[ ! -f "Cargo.lock" ] && MISSING_FILES+=("Cargo.lock")

if [ ${#MISSING_FILES[@]} -eq 0 ]; then
    print_status "SUCCESS" "All essential project files present"
else
    print_status "WARNING" "Missing files: ${MISSING_FILES[*]}"
fi

# Check source directory structure
if [ -d "src" ]; then
    SRC_FILES=$(find src/ -name "*.rs" | wc -l)
    print_status "INFO" "Source files: $SRC_FILES"
    
    # Check for main.rs
    if [ -f "src/main.rs" ]; then
        print_status "SUCCESS" "main.rs found"
    else
        print_status "ERROR" "main.rs not found"
    fi
else
    print_status "ERROR" "src/ directory not found"
fi

# 9. GENERATE COMPREHENSIVE REPORT
echo ""
echo "📊 Generating Comprehensive Report"
echo "--------------------------------"

REPORT_FILE="DEBUG_ANALYSIS_REPORT_$(date +%Y%m%d_%H%M%S).md"

cat > "$REPORT_FILE" << EOF
# Runetika Debug Analysis Report

**Generated:** $(date)
**Project:** Runetika
**Total Lines of Code:** $TOTAL_LINES

## Summary

### ✅ Successes
- Rust environment: $(command -v rustc &> /dev/null && echo "Available" || echo "Missing")
- Cargo: $(command -v cargo &> /dev/null && echo "Available" || echo "Missing")
- Code compilation: $(cargo check --quiet 2>/dev/null && echo "Successful" || echo "Failed")
- Documentation comments: $DOC_COMMENTS

### ⚠️ Warnings
- TODO/FIXME comments: $TODO_COUNT
- Unwrap/expect/panic calls: $UNSAFE_COUNT
- Potential hardcoded values: $HARDCODED_COUNT
- Unsafe blocks: $UNSAFE_BLOCKS

### 📊 Metrics
- Documentation ratio: $([ "$TOTAL_LINES" -gt 0 ] && echo "$((DOC_COMMENTS * 100 / TOTAL_LINES))%" || echo "N/A")
- Test count: $TEST_COUNT
- Source files: $SRC_FILES

## Detailed Analysis

### Code Quality Issues
- **TODO/FIXME Comments:** $TODO_COUNT found
- **Unsafe Operations:** $UNSAFE_COUNT unwrap/expect/panic calls
- **Memory Patterns:** $MEMORY_PATTERNS potential memory leak patterns
- **Performance:** $EXPENSIVE_LOOPS potentially expensive loop operations

### Security Considerations
- **Unsafe Blocks:** $UNSAFE_BLOCKS found
- **Overflow Handling:** $OVERFLOW_PATTERNS patterns found

### Dependencies
- **Outdated:** $OUTDATED dependencies
- **Duplicates:** $DUPLICATES found

## Recommendations

1. **Immediate Actions:**
   - Address TODO/FIXME comments
   - Replace unwrap/expect calls with proper error handling
   - Add comprehensive error handling

2. **Code Quality:**
   - Implement comprehensive testing
   - Add performance profiling
   - Improve documentation coverage

3. **Security:**
   - Review unsafe blocks for necessity
   - Implement proper overflow handling
   - Regular dependency updates

4. **Performance:**
   - Profile critical code paths
   - Optimize expensive operations
   - Implement caching where appropriate

## Next Steps

1. Run \`cargo test\` to execute all tests
2. Address high-priority warnings
3. Implement missing documentation
4. Set up continuous integration
5. Regular performance benchmarking

---
*Report generated by debug_analysis.sh*
EOF

print_status "SUCCESS" "Comprehensive report generated: $REPORT_FILE"

# 10. FINAL SUMMARY
echo ""
echo "🎯 Analysis Complete!"
echo "==================="

print_status "INFO" "Total issues found: $((TODO_COUNT + UNSAFE_COUNT + HARDCODED_COUNT))"
print_status "INFO" "Report saved to: $REPORT_FILE"

if [ "$TODO_COUNT" -gt 0 ] || [ "$UNSAFE_COUNT" -gt 0 ]; then
    echo ""
    print_status "WARNING" "Consider addressing the following high-priority items:"
    [ "$TODO_COUNT" -gt 0 ] && echo "   - $TODO_COUNT TODO/FIXME comments"
    [ "$UNSAFE_COUNT" -gt 0 ] && echo "   - $UNSAFE_COUNT unsafe operations"
    echo ""
fi

print_status "SUCCESS" "Debug analysis completed successfully!"
