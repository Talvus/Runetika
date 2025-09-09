# Runetika Variant Comparison Matrix

## Overview
Multiple game variants allow rapid prototyping and testing of different mechanics, stories, and aesthetics. Each variant lives in its own git branch for clean separation.

## Quick Launch
```bash
./variant_launcher.sh
```

## Variant Branches

| Branch | Focus | Best For Testing |
|--------|-------|------------------|
| `main` | Standard full game | Overall integration |
| `variant/terminal-minimalist` | Pure text | Story, commands, narrative flow |
| `variant/visual-novel` | Dialogue & choices | Character development, branching |
| `variant/puzzle-mechanics` | ARC puzzles | Pattern recognition, difficulty |
| `variant/art-aesthetic` | Visual beauty | Art style, atmosphere, effects |
| `creative-mechanics` | Experimental | New gameplay concepts |

## Feature Comparison

| Feature | Terminal | Visual Novel | Puzzle | Art | Creative |
|---------|----------|--------------|--------|-----|----------|
| **Story Depth** | High | Very High | Low | Low | Medium |
| **Visual Polish** | None | Medium | Low | Very High | Medium |
| **Puzzle Complexity** | Medium | Low | Very High | Low | High |
| **Performance** | Excellent | Good | Good | Poor | Variable |
| **Development Speed** | Fast | Medium | Medium | Slow | Slow |
| **Player Agency** | High | Medium | High | Low | High |
| **Replayability** | Medium | High | Very High | Low | High |

## Mechanics Emphasis

### Terminal Minimalist
- **Core**: Command parsing, text adventure
- **Unique**: ASCII art, typing effects
- **Testing**: Command system, narrative pacing
- **Data Generated**: Command sequences, text choices

### Visual Novel
- **Core**: Dialogue trees, relationship system
- **Unique**: Character portraits, backgrounds
- **Testing**: Story branches, emotional impact
- **Data Generated**: Choice patterns, relationship paths

### Puzzle Mechanics
- **Core**: ARC challenges, pattern matching
- **Unique**: Grid manipulation, rule discovery
- **Testing**: Difficulty curve, solution validation
- **Data Generated**: Solving strategies, rule inference

### Art Aesthetic
- **Core**: Visual effects, atmosphere
- **Unique**: Particle systems, shaders
- **Testing**: Art style, performance impact
- **Data Generated**: Visual preference metrics

### Creative Mechanics
- **Core**: All experimental features
- **Unique**: Type theory viz, temporal layers
- **Testing**: Complex interactions
- **Data Generated**: Advanced reasoning patterns

## Story Variations

| Variant | Story Focus | Tone |
|---------|------------|------|
| Terminal | Silicon Mind awakening | Mysterious, cerebral |
| Visual Novel | Emotional connections | Romantic, melancholic |
| Puzzle | Mind challenges | Analytical, focused |
| Art | Environmental storytelling | Atmospheric, abstract |
| Creative | Meta-narrative | Experimental, philosophical |

## Art Styles

| Variant | Visual Style | Color Palette |
|---------|--------------|---------------|
| Terminal | Monochrome text | Green/amber phosphor |
| Visual Novel | Anime-inspired | Soft pastels |
| Puzzle | Clean geometric | High contrast |
| Art | Particle effects | Neon cyberpunk |
| Creative | Mathematical viz | Dynamic spectrum |

## Performance Profiles

| Variant | RAM Usage | CPU Load | GPU Load | Build Time |
|---------|-----------|----------|----------|------------|
| Terminal | 50MB | Low | None | 10s |
| Visual Novel | 200MB | Medium | Low | 30s |
| Puzzle | 150MB | High | Low | 25s |
| Art | 500MB | Medium | High | 45s |
| Creative | 300MB | High | Medium | 60s |

## Development Workflow

### Creating New Variant
```bash
git checkout main
git checkout -b variant/new-idea
# Modify game focus
git add -A
git commit -m "feat(variant): New variant description"
```

### Switching Variants
```bash
# Manual switch
git checkout variant/terminal-minimalist
cargo run

# Or use launcher
./variant_launcher.sh
```

### Merging Good Ideas
```bash
# Cherry-pick specific features
git checkout main
git cherry-pick <commit-from-variant>

# Or merge entire variant
git merge variant/successful-experiment
```

## Testing Strategy

1. **Terminal**: Test all text commands work
2. **Visual Novel**: Test all dialogue branches
3. **Puzzle**: Verify all puzzles solvable
4. **Art**: Check performance on target hardware
5. **Creative**: Validate experimental features

## Data Collection

Each variant generates different training data:

- **Terminal**: Command sequences, text navigation
- **Visual Novel**: Choice patterns, emotional responses
- **Puzzle**: Solution strategies, pattern recognition
- **Art**: Visual attention, aesthetic preferences
- **Creative**: Complex reasoning chains

## Recommended Testing Order

1. Start with **Terminal** to nail down core narrative
2. Move to **Puzzle** to validate ARC mechanics
3. Try **Visual Novel** for story branching
4. Polish with **Art** for visual direction
5. Integrate best features in **main**

## Git Best Practices

- Keep variants rebased on main regularly
- Use descriptive commit messages
- Tag successful experiments
- Document discoveries in variant README
- Clean up stale branches

## Quick Commands

```bash
# List all variants
git branch | grep variant/

# Compare variants
git diff variant/terminal-minimalist variant/visual-novel

# Archive old variant
git tag archive/variant-name variant/branch-name
git branch -d variant/branch-name

# Restore archived variant
git checkout -b variant/restored archive/variant-name
```

## Success Metrics

Track per variant:
- Player engagement time
- Puzzle completion rate
- Story branch coverage
- Performance benchmarks
- Bug discovery rate
- Feature adoption

## Future Variants to Explore

- `variant/roguelike` - Procedural generation
- `variant/multiplayer` - Networked gameplay
- `variant/mobile` - Touch controls
- `variant/vr` - Immersive experience
- `variant/educational` - Teaching mode