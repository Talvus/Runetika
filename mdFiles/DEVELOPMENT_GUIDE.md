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

