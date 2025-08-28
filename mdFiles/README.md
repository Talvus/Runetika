# Runetika

Runetika is a top-down RPG prototype built with [Bevy](https://bevyengine.org/) and the experimental [Avian2D] engine. This repository contains the first steps toward building the game world.

## 🚀 Automated Development Workflow

This project includes a comprehensive automated workflow that runs after every commit:

- **📚 Documentation Building**: Automatic generation of Rust API docs and project documentation
- **🔬 Research & Next Steps**: Continuous updates to development roadmap and research findings
- **🐛 Code Analysis**: Thorough debugging and quality analysis of the entire codebase
- **📊 Progress Tracking**: Detailed commit summaries and development insights

### Post-Commit Automation

After every commit, the system automatically:
1. Builds comprehensive documentation
2. Updates research and next steps in `RESEARCH_AND_NEXT_STEPS.md`
3. Runs debugging analysis and generates reports
4. Creates commit summaries with actionable insights

## 🛠️ Development Tools

### Automated Scripts
- **`./tools/build_docs.sh`**: Comprehensive documentation builder
- **`./tools/debug_analysis.sh`**: Code quality analysis and debugging
- **`./tools/update-deps.sh`**: Dependency management and updates

### Manual Workflow
```bash
# Build documentation
./tools/build_docs.sh

# Run code analysis
./tools/debug_analysis.sh

# Check code quality
cargo clippy -- -D warnings

# Run tests
cargo test
```

## 🏗️ Building

The project requires a recent Rust toolchain. To build the project run:

```bash
cargo build
```

Because the dependencies are fetched from `crates.io`, the build step requires an internet connection.

## 🎮 Running

Once the project compiles successfully you can run the demo with:

```bash
cargo run
```

The initial build will download Bevy and Avian2D and display an empty 10x10 map of tiles.

## 📚 Documentation

### Generated Documentation
- **`docs/rust-api/`**: Complete Rust API reference (auto-generated)
- **`docs/PROJECT_STRUCTURE.md`**: Project architecture and organization
- **`docs/DEVELOPMENT_GUIDE.md`**: Development guidelines and best practices
- **`docs/API_INDEX.md`**: API documentation index and navigation

### Project Documentation
- **`README.md`**: This file - quick start and overview
- **`WARP.md`**: Detailed project documentation and specifications
- **`RESEARCH_AND_NEXT_STEPS.md`**: Continuously evolving development roadmap

## 🎯 Overview 

Runetika is a game that is more than just a game. It is, in fact, an immersive experience.  
Overall, the game is about love and hope, and human emotion. It demonstrates how beautiful 
everyone's inner world can be, if we simply let it. 

It centers on a fallen civilization that is based on silicon, which arrived on Earth 
years ago and is now interfering with the supply chains of computing technology. 

It will be based in a mystical realism and artistic style. 

The user experience involves solving glyphs, puzzles, and mazes.  

### Research Questions
- **Puzzle Types**: E.g., ARC puzzles for pattern recognition
- **Progress Measurement**: How is user progress measured and tracked?
- **User Goals**: What are the primary objectives and how do they relate to the fallen civilization theme?
- **Barriers & Dangers**: What challenges will users face and how do they fit the game's theme?

## 🔍 Quality Assurance

### Automated Checks
- **Post-commit hooks**: Run automatically after every commit
- **Code analysis**: Comprehensive debugging and issue detection
- **Documentation generation**: Always up-to-date project documentation
- **Dependency management**: Regular updates and security checks

### Manual Quality Checks
```bash
# Run comprehensive analysis
./tools/debug_analysis.sh

# Check for common issues
cargo clippy -- -D warnings
cargo check
cargo test

# Build optimized version
cargo build --release
```

## 📁 Project Structure

```
OurRunetika/
├── src/                   # Source code
│   ├── credits/          # Credits and attribution systems
│   ├── game_state.rs     # Game state management
│   ├── main.rs           # Main application entry point
│   ├── menu/             # Menu system components
│   ├── performance/      # Performance monitoring
│   ├── settings/         # Game settings and configuration
│   └── terminal/         # Terminal/console system
├── tools/                 # Development and build tools
├── docs/                  # Generated documentation
├── assets/                # Game assets (fonts, images, audio)
└── target/                # Build artifacts
```

## 🤝 Contributing

### Development Workflow
1. **Fork and clone** the repository
2. **Make changes** following the development guide
3. **Test thoroughly** using the provided tools
4. **Commit changes** - automation will handle the rest!
5. **Submit pull request** for review

### Quality Standards
- Follow Rust coding conventions
- Add comprehensive error handling
- Document all public APIs
- Include tests for new functionality
- Run quality checks before committing

## 📊 Monitoring and Insights

### Generated Reports
- **Commit summaries**: Detailed analysis of each commit
- **Debug reports**: Comprehensive code quality analysis
- **Research updates**: Continuous development roadmap evolution
- **Documentation**: Always current project documentation

### Key Metrics
- Code quality scores
- Documentation coverage
- Test coverage
- Performance benchmarks
- Security analysis

## 🔮 Future Development

The automated workflow continuously researches and suggests next steps:

1. **Core Foundation**: Basic game loop and world rendering
2. **Gameplay Mechanics**: Puzzle systems and glyph recognition
3. **Content & Polish**: Story, audio, and visual effects
4. **Testing & Release**: Comprehensive testing and optimization

## 📄 License

This project is licensed under the terms specified in the [LICENSE](LICENSE) file.

---

*This README is automatically updated as part of the project's continuous documentation workflow.*



