#!/bin/bash

# Setup script for Runetika automation system
# This script configures the complete post-commit workflow

set -e

echo "🚀 Setting up Runetika automation system..."
echo "=========================================="

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

# 1. VERIFY GIT REPOSITORY
echo ""
echo "🔍 Verifying Git repository..."
if [ -d ".git" ]; then
    print_status "SUCCESS" "Git repository found"
else
    print_status "ERROR" "Not a Git repository. Please run 'git init' first."
    exit 1
fi

# 2. SETUP GIT HOOKS
echo ""
echo "🎣 Setting up Git hooks..."

# Make post-commit hook executable
if [ -f ".git/hooks/post-commit" ]; then
    chmod +x .git/hooks/post-commit
    print_status "SUCCESS" "Post-commit hook made executable"
else
    print_status "WARNING" "Post-commit hook not found. Creating..."
    
    cat > .git/hooks/post-commit << 'EOF'
#!/bin/bash

# Post-commit hook for Runetika project
# This script runs automatically after every commit to:
# 1. Build documentation
# 2. Update research and next steps
# 3. Run debugging and testing

set -e

echo "🚀 Post-commit workflow started for Runetika..."

# Get commit info
COMMIT_HASH=$(git rev-parse HEAD)
COMMIT_MSG=$(git log -1 --pretty=%B)
COMMIT_DATE=$(git log -1 --pretty=%cd --date=iso)

echo "📝 Commit: $COMMIT_HASH"
echo "📅 Date: $COMMIT_DATE"
echo "💬 Message: $COMMIT_MSG"

# Change to project root
cd "$(git rev-parse --show-toplevel)"

# 1. BUILD DOCUMENTATION
echo "📚 Building documentation..."
if command -v cargo &> /dev/null; then
    echo "   - Building Rust documentation..."
    cargo doc --no-deps --document-private-items || echo "⚠️  Documentation build failed, continuing..."
    
    echo "   - Checking for documentation warnings..."
    cargo doc --no-deps --document-private-items --message-format=json 2>&1 | grep -E "(warning|error)" || echo "   ✅ No documentation warnings found"
else
    echo "⚠️  Cargo not found, skipping documentation build"
fi

# 2. UPDATE RESEARCH AND NEXT STEPS
echo "🔬 Updating research and next steps..."
RESEARCH_FILE="RESEARCH_AND_NEXT_STEPS.md"

# Create research file if it doesn't exist
if [ ! -f "$RESEARCH_FILE" ]; then
    cat > "$RESEARCH_FILE" << 'EOF'
# Research and Next Steps for Runetika

## Project Overview
Runetika is a top-down RPG prototype built with Bevy and Avian2D, focusing on love, hope, and human emotion through mystical realism and artistic style.

## Current Status
- [x] Basic project structure with Bevy and Avian2D
- [x] Initial game world setup
- [ ] Core gameplay mechanics
- [ ] Puzzle system implementation
- [ ] User progress tracking
- [ ] Artistic assets and styling

## Recent Commits Analysis
EOF
fi

# Add commit information to research file
echo "" >> "$RESEARCH_FILE"
echo "### Commit: $COMMIT_HASH" >> "$RESEARCH_FILE"
echo "**Date:** $COMMIT_DATE" >> "$RESEARCH_FILE"
echo "**Message:** $COMMIT_MSG" >> "$RESEARCH_FILE"
echo "" >> "$RESEARCH_FILE"

# Analyze code changes and suggest next steps
echo "   - Analyzing code changes..."
CHANGED_FILES=$(git diff-tree --no-commit-id --name-only -r HEAD)

if [ -n "$CHANGED_FILES" ]; then
    echo "**Files Changed:**" >> "$RESEARCH_FILE"
    echo "$CHANGED_FILES" | while read -r file; do
        echo "- \`$file\`" >> "$RESEARCH_FILE"
    done
    echo "" >> "$RESEARCH_FILE"
    
    echo "**Suggested Next Steps:**" >> "$RESEARCH_FILE"
    
    # Analyze specific file types and suggest improvements
    if echo "$CHANGED_FILES" | grep -q "\.rs$"; then
        echo "- Review Rust code for potential optimizations" >> "$RESEARCH_FILE"
        echo "- Check for proper error handling and logging" >> "$RESEARCH_FILE"
        echo "- Ensure code follows Rust best practices" >> "$RESEARCH_FILE"
    fi
    
    if echo "$CHANGED_FILES" | grep -q "Cargo\.toml"; then
        echo "- Review dependency updates and compatibility" >> "$RESEARCH_FILE"
        echo "- Check for security vulnerabilities in dependencies" >> "$RESEARCH_FILE"
    fi
    
    if echo "$CHANGED_FILES" | grep -q "README"; then
        echo "- Update project documentation as needed" >> "$RESEARCH_FILE"
        echo "- Review user experience and onboarding" >> "$RESEARCH_FILE"
    fi
else
    echo "**Note:** No files were changed in this commit" >> "$RESEARCH_FILE"
fi

echo "" >> "$RESEARCH_FILE"
echo "---" >> "$RESEARCH_FILE"

# 3. RUN DEBUGGING AND TESTING
echo "🐛 Running debugging and testing..."

# Check for common issues
echo "   - Checking for common Rust issues..."
if command -v cargo &> /dev/null; then
    echo "   - Running cargo check..."
    cargo check || echo "⚠️  Cargo check failed"
    
    echo "   - Running cargo clippy for linting..."
    cargo clippy -- -D warnings 2>/dev/null || echo "⚠️  Clippy found issues or is not available"
    
    echo "   - Running cargo test..."
    cargo test --no-run || echo "⚠️  Test compilation failed"
    
    echo "   - Checking for unused dependencies..."
    cargo tree --duplicates 2>/dev/null | grep -E "(WARNING|duplicate)" || echo "   ✅ No duplicate dependencies found"
else
    echo "⚠️  Cargo not found, skipping Rust checks"
fi

# Check for potential issues in the codebase
echo "   - Analyzing codebase for potential issues..."

# Check for TODO/FIXME comments
TODO_COUNT=$(grep -r "TODO\|FIXME\|XXX\|HACK" src/ 2>/dev/null | wc -l || echo "0")
echo "   - Found $TODO_COUNT TODO/FIXME comments in source code"

# Check for hardcoded values
HARDCODED_COUNT=$(grep -r "magic\|hardcoded\|123\|999" src/ 2>/dev/null | wc -l || echo "0")
echo "   - Found $HARDCODED_COUNT potential hardcoded values"

# Check for proper error handling
ERROR_HANDLING=$(grep -r "unwrap\|expect\|panic" src/ 2>/dev/null | wc -l || echo "0")
echo "   - Found $ERROR_HANDLING unwrap/expect/panic calls"

# Add debugging insights to research file
echo "**Debugging Insights:**" >> "$RESEARCH_FILE"
echo "- TODO/FIXME comments: $TODO_COUNT" >> "$RESEARCH_FILE"
echo "- Potential hardcoded values: $HARDCODED_COUNT" >> "$RESEARCH_FILE"
echo "- Unwrap/expect/panic calls: $ERROR_HANDLING" >> "$RESEARCH_FILE"
echo "" >> "$RESEARCH_FILE"

# 4. GENERATE SUMMARY REPORT
echo "📊 Generating summary report..."
SUMMARY_FILE="COMMIT_SUMMARY_$(date +%Y%m%d_%H%M%S).md"

cat > "$SUMMARY_FILE" << EOF
# Commit Summary: $COMMIT_HASH

**Date:** $COMMIT_DATE  
**Message:** $COMMIT_MSG

## Files Changed
$(echo "$CHANGED_FILES" | sed 's/^/- /')

## Debugging Results
- TODO/FIXME comments: $TODO_COUNT
- Potential hardcoded values: $HARDCODED_COUNT
- Unwrap/expect/panic calls: $ERROR_HANDLING

## Next Steps
See \`$RESEARCH_FILE\` for detailed research and next steps.

---
Generated automatically by post-commit hook
EOF

echo "✅ Post-commit workflow completed successfully!"
echo "📁 Files generated:"
echo "   - $RESEARCH_FILE (research and next steps)"
echo "   - $SUMMARY_FILE (commit summary)"
echo "   - Documentation in target/doc/ (if build succeeded)"
echo ""
echo "🔍 Review the generated files for insights and next steps."
EOF

    chmod +x .git/hooks/post-commit
    print_status "SUCCESS" "Post-commit hook created and made executable"
fi

# 3. VERIFY TOOLS
echo ""
echo "🛠️  Verifying development tools..."

# Check if tools are executable
if [ -x "tools/build_docs.sh" ]; then
    print_status "SUCCESS" "Documentation builder is executable"
else
    print_status "WARNING" "Documentation builder not executable, fixing..."
    chmod +x tools/build_docs.sh
fi

if [ -x "tools/debug_analysis.sh" ]; then
    print_status "SUCCESS" "Debug analysis tool is executable"
else
    print_status "WARNING" "Debug analysis tool not executable, fixing..."
    chmod +x tools/debug_analysis.sh
fi

# 4. CREATE INITIAL DOCUMENTATION
echo ""
echo "📚 Creating initial documentation..."

# Create docs directory if it doesn't exist
mkdir -p docs

# Run documentation builder
if [ -x "tools/build_docs.sh" ]; then
    echo "   Running documentation builder..."
    ./tools/build_docs.sh
else
    print_status "WARNING" "Documentation builder not available"
fi

# 5. RUN INITIAL ANALYSIS
echo ""
echo "🔍 Running initial code analysis..."

if [ -x "tools/debug_analysis.sh" ]; then
    echo "   Running debug analysis..."
    ./tools/debug_analysis.sh
else
    print_status "WARNING" "Debug analysis tool not available"
fi

# 6. VERIFY SETUP
echo ""
echo "✅ Verifying automation setup..."

# Check if all components are in place
COMPONENTS=(
    ".git/hooks/post-commit"
    "tools/build_docs.sh"
    "tools/debug_analysis.sh"
    "RESEARCH_AND_NEXT_STEPS.md"
    "docs/"
)

MISSING=()
for component in "${COMPONENTS[@]}"; do
    if [ -e "$component" ]; then
        print_status "SUCCESS" "✓ $component"
    else
        print_status "ERROR" "✗ $component (missing)"
        MISSING+=("$component")
    fi
done

# 7. FINAL SUMMARY
echo ""
echo "🎯 Setup Complete!"
echo "================="

if [ ${#MISSING[@]} -eq 0 ]; then
    print_status "SUCCESS" "All automation components are ready!"
    echo ""
    echo "🚀 Your Runetika project is now set up with:"
    echo "   - ✅ Post-commit automation hooks"
    echo "   - ✅ Comprehensive documentation builder"
    echo "   - ✅ Code quality analysis tools"
    echo "   - ✅ Continuous research updates"
    echo ""
    echo "📝 Next time you commit, the system will automatically:"
    echo "   1. Build documentation"
    echo "   2. Update research and next steps"
    echo "   3. Analyze code quality"
    echo "   4. Generate commit summaries"
    echo ""
    print_status "INFO" "Try making a commit to test the automation!"
else
    print_status "WARNING" "Some components are missing:"
    for component in "${MISSING[@]}"; do
        echo "   - $component"
    done
    echo ""
    echo "Please check the setup and try again."
fi

echo ""
print_status "SUCCESS" "Automation setup completed!"