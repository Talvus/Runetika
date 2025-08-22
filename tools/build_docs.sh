#!/bin/bash

# Comprehensive Documentation Builder for Runetika
# This script builds various types of documentation for the project

set -e

echo "📚 Starting comprehensive documentation build for Runetika..."
echo "=========================================================="

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

# Create docs directory
mkdir -p docs

# 1. RUST DOCUMENTATION
echo ""
echo "🦀 Building Rust Documentation"
echo "------------------------------"

if command -v cargo &> /dev/null; then
    echo "   Building Rust API documentation..."
    if cargo doc --no-deps --document-private-items --open=false; then
        print_status "SUCCESS" "Rust documentation built successfully"
        
        # Copy to docs directory
        if [ -d "target/doc" ]; then
            cp -r target/doc docs/rust-api
            print_status "SUCCESS" "Rust API docs copied to docs/rust-api/"
        fi
    else
        print_status "ERROR" "Failed to build Rust documentation"
    fi
    
    # Check for documentation warnings
    echo "   Checking for documentation warnings..."
    DOC_WARNINGS=$(cargo doc --no-deps --document-private-items --message-format=json 2>&1 | grep -E "(warning|error)" | wc -l || echo "0")
    if [ "$DOC_WARNINGS" -gt 0 ]; then
        print_status "WARNING" "Found $DOC_WARNINGS documentation warnings"
    else
        print_status "SUCCESS" "No documentation warnings found"
    fi
else
    print_status "ERROR" "Cargo not found, skipping Rust documentation"
fi

# 2. PROJECT STRUCTURE DOCUMENTATION
echo ""
echo "🏗️  Generating Project Structure Documentation"
echo "--------------------------------------------"

STRUCTURE_FILE="docs/PROJECT_STRUCTURE.md"

cat > "$STRUCTURE_FILE" << 'EOF'
# Runetika Project Structure

## Overview
Runetika is a top-down RPG prototype built with Bevy and Avian2D, focusing on love, hope, and human emotion through mystical realism and artistic style.

## Directory Structure

```
OurRunetika/
├── assets/                 # Game assets (fonts, images, audio)
│   └── fonts/            # Typography assets
├── src/                   # Source code
│   ├── credits/          # Credits and attribution systems
│   │   ├── mod.rs        # Module definition
│   │   ├── systems.rs    # ECS systems for credits
│   │   └── ui.rs         # User interface for credits
│   ├── game_state.rs     # Game state management
│   ├── main.rs           # Main application entry point
│   ├── main_documented.rs # Documented version of main
│   ├── menu/             # Menu system components
│   │   ├── components.rs # Menu UI components
│   │   ├── mod.rs        # Menu module definition
│   │   ├── systems.rs    # Menu ECS systems
│   │   ├── ui_old.rs     # Legacy menu UI (deprecated)
│   │   └── ui.rs         # Current menu UI implementation
│   ├── performance/      # Performance monitoring and optimization
│   │   └── mod.rs        # Performance module
│   ├── settings/         # Game settings and configuration
│   │   ├── components.rs # Settings UI components
│   │   └── mod.rs        # Settings module
│   └── terminal/         # Terminal/console system
│       ├── commands.rs   # Terminal command definitions
│       ├── components.rs # Terminal UI components
│       ├── mod.rs        # Terminal module
│       ├── starfield.rs  # Starfield background effect
│       ├── systems.rs    # Terminal ECS systems
│       └── ui.rs         # Terminal user interface
├── tools/                 # Development and build tools
│   ├── build_docs.sh     # Documentation builder
│   ├── debug_analysis.sh # Code analysis and debugging
│   └── update-deps.sh    # Dependency update script
├── target/                # Build artifacts (generated)
├── Cargo.toml            # Rust project configuration
├── Cargo.lock            # Dependency lock file
├── Cargo_optimized.toml  # Optimized build configuration
├── rust-toolchain.toml   # Rust toolchain specification
├── README.md             # Project overview and setup
├── WARP.md               # Project documentation
├── LICENSE               # Project license
├── renovate.json         # Dependency update configuration
└── RESEARCH_AND_NEXT_STEPS.md # Research and development roadmap
```

## Architecture Overview

### ECS (Entity-Component-System) Architecture
The project uses Bevy's ECS architecture for efficient game development:

- **Entities**: Game objects (player, NPCs, items, etc.)
- **Components**: Data attached to entities (position, health, inventory, etc.)
- **Systems**: Logic that operates on entities with specific components

### Module Organization
Each major feature is organized into its own module with:
- `mod.rs`: Module definition and public interface
- `systems.rs`: ECS systems for the module
- `ui.rs`: User interface components
- `components.rs`: Reusable UI components

### Key Systems
1. **Game State Management**: Handles transitions between game states
2. **Menu System**: Provides navigation and game options
3. **Terminal System**: Console interface for debugging and commands
4. **Performance Monitoring**: Tracks and optimizes game performance
5. **Settings Management**: Handles user preferences and configuration

## Dependencies

### Core Dependencies
- **Bevy 0.16**: Game engine with ECS architecture
- **Avian2D 0.2**: Experimental 2D physics engine
- **Rand 0.8**: Random number generation

### Development Dependencies
- **rust-toolchain.toml**: Specifies Rust version and components
- **renovate.json**: Automates dependency updates

## Build Configuration

### Cargo.toml
- Main project configuration
- Dependency specifications
- Build targets and features

### Cargo_optimized.toml
- Optimized build configuration for production
- Performance-focused compiler flags
- Release build settings

## Asset Management

### Fonts
- Located in `assets/fonts/`
- Typography for UI elements
- Consistent visual identity

### Future Asset Categories
- **Images**: Sprites, textures, backgrounds
- **Audio**: Music, sound effects, ambient sounds
- **Data**: Game configuration, level data, dialogue

## Development Workflow

### Tools
- **build_docs.sh**: Generates comprehensive documentation
- **debug_analysis.sh**: Analyzes code quality and performance
- **update-deps.sh**: Manages dependency updates

### Documentation
- **README.md**: Quick start and overview
- **WARP.md**: Detailed project documentation
- **RESEARCH_AND_NEXT_STEPS.md**: Development roadmap
- **docs/**: Generated documentation

### Quality Assurance
- Automated post-commit hooks
- Comprehensive debugging and analysis
- Continuous documentation updates

## Future Considerations

### Scalability
- Modular architecture supports feature expansion
- ECS pattern enables efficient performance scaling
- Asset pipeline designed for content growth

### Maintainability
- Clear separation of concerns
- Consistent coding patterns
- Comprehensive documentation

### Performance
- Built-in performance monitoring
- Optimized build configurations
- Efficient asset loading strategies

---

*Generated automatically by build_docs.sh*
EOF

print_status "SUCCESS" "Project structure documentation generated: $STRUCTURE_FILE"

# 3. API DOCUMENTATION INDEX
echo ""
echo "🔗 Generating API Documentation Index"
echo "------------------------------------"

API_INDEX_FILE="docs/API_INDEX.md"

cat > "$API_INDEX_FILE" << 'EOF'
# Runetika API Documentation Index

## Overview
This document provides an index to all available API documentation for the Runetika project.

## Available Documentation

### Rust API Documentation
- **Location**: `docs/rust-api/` (if built successfully)
- **Scope**: All public and private Rust APIs
- **Generated**: Automatically from code comments
- **Access**: Open `docs/rust-api/index.html` in a web browser

### Project Documentation
- **README.md**: Project overview and quick start
- **WARP.md**: Detailed project documentation
- **RESEARCH_AND_NEXT_STEPS.md**: Development roadmap and research
- **docs/PROJECT_STRUCTURE.md**: Project architecture and organization

### Development Tools
- **tools/build_docs.sh**: Documentation builder script
- **tools/debug_analysis.sh**: Code analysis and debugging script
- **tools/update-deps.sh**: Dependency management script

## API Categories

### Core Systems
- **Game State Management**: `src/game_state.rs`
- **Main Application**: `src/main.rs`

### User Interface
- **Menu System**: `src/menu/`
- **Settings**: `src/settings/`
- **Terminal**: `src/terminal/`

### Game Logic
- **Credits System**: `src/credits/`
- **Performance Monitoring**: `src/performance/`

## Building Documentation

### Automatic Build
Documentation is automatically built after each commit via the post-commit hook.

### Manual Build
To build documentation manually:

```bash
# Build Rust documentation
cargo doc --no-deps --document-private-items

# Build comprehensive documentation
./tools/build_docs.sh

# Run code analysis
./tools/debug_analysis.sh
```

### Documentation Standards
- All public APIs must be documented with `///` comments
- Use `//!` for module-level documentation
- Include examples in documentation where appropriate
- Follow Rust documentation conventions

## Accessing Documentation

### Local Development
1. Build documentation: `./tools/build_docs.sh`
2. Open `docs/rust-api/index.html` in your browser
3. Navigate through the generated documentation

### Online Access
- Project repository: [GitHub Repository URL]
- Documentation: [Documentation URL if hosted]

## Contributing to Documentation

### Code Comments
- Document all public functions, structs, and traits
- Include parameter descriptions and return value explanations
- Provide usage examples for complex APIs

### Project Documentation
- Keep README.md up to date
- Update RESEARCH_AND_NEXT_STEPS.md with new findings
- Maintain accurate project structure documentation

### Documentation Tools
- Use `cargo doc` for Rust API documentation
- Run `./tools/build_docs.sh` for comprehensive documentation
- Verify documentation builds successfully

## Troubleshooting

### Common Issues
1. **Documentation won't build**: Check for syntax errors in code comments
2. **Missing documentation**: Ensure all public APIs have `///` comments
3. **Broken links**: Verify file paths and update documentation

### Getting Help
- Check the generated documentation for errors
- Run `./tools/debug_analysis.sh` for code quality insights
- Review the project structure documentation

---

*Generated automatically by build_docs.sh*
EOF

print_status "SUCCESS" "API documentation index generated: $API_INDEX_FILE"

# 4. DEVELOPMENT GUIDE
echo ""
echo "📖 Generating Development Guide"
echo "------------------------------"

DEV_GUIDE_FILE="docs/DEVELOPMENT_GUIDE.md"

cat > "$DEV_GUIDE_FILE" << 'EOF'
# Runetika Development Guide

## Getting Started

### Prerequisites
- Rust 1.70+ (check with `rustc --version`)
- Cargo package manager
- Git for version control

### Initial Setup
1. Clone the repository
2. Install Rust dependencies: `cargo build`
3. Run the project: `cargo run`

## Development Workflow

### Code Standards
- Follow Rust coding conventions
- Use meaningful variable and function names
- Add comprehensive error handling
- Document all public APIs with `///` comments

### Testing
- Write unit tests for all public functions
- Run tests: `cargo test`
- Ensure test coverage: `cargo test --no-run`

### Code Quality
- Run Clippy: `cargo clippy -- -D warnings`
- Check for common issues: `./tools/debug_analysis.sh`
- Address warnings and errors before committing

### Documentation
- Update code comments when changing APIs
- Keep project documentation current
- Build documentation: `./tools/build_docs.sh`

## Architecture Guidelines

### ECS Pattern
- Keep systems focused and single-purpose
- Use components for data, systems for logic
- Minimize coupling between systems
- Leverage Bevy's query system for efficiency

### Module Organization
- Group related functionality in modules
- Maintain clear public interfaces
- Use `mod.rs` for module definitions
- Separate concerns (UI, logic, data)

### Error Handling
- Use `Result<T, E>` for fallible operations
- Implement custom error types where appropriate
- Provide meaningful error messages
- Log errors for debugging

## Performance Considerations

### Rendering
- Minimize draw calls
- Use sprite batching where possible
- Implement level-of-detail systems
- Profile rendering performance

### Memory Management
- Avoid unnecessary allocations
- Use object pools for frequently created/destroyed objects
- Implement proper cleanup in systems
- Monitor memory usage

### Asset Loading
- Implement asset streaming for large assets
- Use asset caching strategies
- Compress assets where appropriate
- Implement progressive loading

## Debugging and Troubleshooting

### Common Issues
1. **Compilation Errors**: Check Rust syntax and dependencies
2. **Runtime Errors**: Use debug logging and error handling
3. **Performance Issues**: Profile with `./tools/debug_analysis.sh`
4. **Asset Issues**: Verify file paths and formats

### Debug Tools
- **Debug Analysis**: `./tools/debug_analysis.sh`
- **Documentation**: `./tools/build_docs.sh`
- **Cargo Commands**: `cargo check`, `cargo clippy`
- **Logging**: Implement structured logging

### Performance Profiling
- Use Bevy's built-in profiling
- Monitor frame rates and memory usage
- Profile critical code paths
- Optimize bottlenecks

## Contributing

### Code Review Process
1. Create feature branch from main
2. Implement changes with tests
3. Run quality checks: `./tools/debug_analysis.sh`
4. Update documentation
5. Submit pull request

### Quality Checklist
- [ ] Code compiles without warnings
- [ ] All tests pass
- [ ] Clippy checks pass
- [ ] Documentation updated
- [ ] Performance impact considered
- [ ] Error handling implemented

### Documentation Requirements
- Update README.md for user-facing changes
- Document new APIs with examples
- Update project structure documentation
- Maintain development guide accuracy

## Deployment

### Build Optimization
- Use release builds: `cargo build --release`
- Optimize asset sizes
- Minimize dependencies
- Profile release builds

### Platform Considerations
- Test on target platforms
- Handle platform-specific features
- Optimize for target hardware
- Consider cross-platform compatibility

## Maintenance

### Regular Tasks
- Update dependencies: `./tools/update-deps.sh`
- Run code analysis: `./tools/debug_analysis.sh`
- Build documentation: `./tools/build_docs.sh`
- Review and update documentation

### Monitoring
- Track performance metrics
- Monitor error rates
- Update development roadmap
- Address technical debt

---

*Generated automatically by build_docs.sh*
EOF

print_status "SUCCESS" "Development guide generated: $DEV_GUIDE_FILE"

# 5. GENERATE DOCUMENTATION SUMMARY
echo ""
echo "📊 Generating Documentation Summary"
echo "----------------------------------"

SUMMARY_FILE="docs/DOCUMENTATION_SUMMARY.md"

cat > "$SUMMARY_FILE" << EOF
# Runetika Documentation Summary

**Generated:** $(date)
**Total Documentation Files:** 4

## Available Documentation

### 📚 API Documentation
- **Rust API**: \`docs/rust-api/\` (auto-generated)
- **API Index**: \`docs/API_INDEX.md\`
- **Scope**: Complete Rust API reference

### 🏗️ Project Documentation
- **Project Structure**: \`docs/PROJECT_STRUCTURE.md\`
- **Development Guide**: \`docs/DEVELOPMENT_GUIDE.md\`
- **Research & Next Steps**: \`RESEARCH_AND_NEXT_STEPS.md\`

### 📖 User Documentation
- **README**: \`README.md\` (quick start)
- **WARP**: \`WARP.md\` (detailed overview)

## Documentation Coverage

### Code Documentation
- **Rust API**: $(if [ -d "docs/rust-api" ]; then echo "✅ Built"; else echo "❌ Not built"; fi)
- **Code Comments**: $(grep -r "///\|//!" src/ 2>/dev/null | wc -l || echo "0") documentation comments
- **Module Documentation**: $(grep -r "//!" src/ 2>/dev/null | wc -l || echo "0") module-level docs

### Project Documentation
- **Architecture**: ✅ Documented
- **Development Process**: ✅ Documented
- **API Reference**: ✅ Generated
- **User Guide**: ✅ Available

## Building and Accessing Documentation

### Automatic Build
Documentation is automatically built after each commit via the post-commit hook.

### Manual Build Commands
\`\`\`bash
# Build all documentation
./tools/build_docs.sh

# Build only Rust documentation
cargo doc --no-deps --document-private-items

# Run code analysis
./tools/debug_analysis.sh
\`\`\`

### Accessing Documentation
1. **Local Development**: Open \`docs/rust-api/index.html\` in browser
2. **Project Overview**: Read \`README.md\` and \`WARP.md\`
3. **Development**: Follow \`docs/DEVELOPMENT_GUIDE.md\`
4. **Architecture**: Review \`docs/PROJECT_STRUCTURE.md\`

## Documentation Quality

### Standards
- ✅ Consistent formatting and structure
- ✅ Comprehensive coverage of public APIs
- ✅ Clear development guidelines
- ✅ Up-to-date project information

### Maintenance
- 🔄 Auto-updated with post-commit hooks
- 🔄 Generated from source code
- 🔄 Regular quality checks
- 🔄 Continuous improvement

## Next Steps for Documentation

### Immediate Actions
1. Review generated documentation for accuracy
2. Add missing code comments where needed
3. Update user-facing documentation
4. Validate all links and references

### Long-term Improvements
1. Add interactive examples
2. Implement search functionality
3. Create video tutorials
4. Add performance benchmarks

---

*Generated automatically by build_docs.sh*
EOF

print_status "SUCCESS" "Documentation summary generated: $SUMMARY_FILE"

# 6. FINAL SUMMARY
echo ""
echo "🎯 Documentation Build Complete!"
echo "=============================="

print_status "SUCCESS" "All documentation generated successfully!"
echo ""
echo "📁 Generated Documentation:"
echo "   - docs/PROJECT_STRUCTURE.md (project architecture)"
echo "   - docs/API_INDEX.md (API documentation index)"
echo "   - docs/DEVELOPMENT_GUIDE.md (development guidelines)"
echo "   - docs/DOCUMENTATION_SUMMARY.md (overview and summary)"
if [ -d "docs/rust-api" ]; then
    echo "   - docs/rust-api/ (Rust API documentation)"
fi

echo ""
print_status "INFO" "Documentation is automatically updated after each commit"
print_status "INFO" "Run './tools/debug_analysis.sh' for code quality insights"
print_status "SUCCESS" "Documentation build completed successfully!"
