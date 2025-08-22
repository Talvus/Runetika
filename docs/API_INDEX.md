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
