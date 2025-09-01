# WASM Implementation in Runetika

## What We've Built

### 1. Silicon Consciousness as WASM Runtime
The silicon being's "mind" is now literally a collection of WASM modules that can be:
- **Loaded dynamically** - Add new behaviors without recompiling
- **Modified by players** - Create custom silicon personalities
- **Safely sandboxed** - Can't crash the main game

### 2. Emotional Processing in WASM
Silicon emotions are processed through WebAssembly modules:
- **Loneliness Module** - Increases exponentially with time alone
- **Curiosity Module** - Spikes with new discoveries
- **Empathy Module** - Learns to respond to human emotions

### 3. Architecture

```
Game (Native Rust)
    ↓
WASMER Runtime
    ↓
Silicon Modules (WASM)
    - loneliness.wasm
    - curiosity.wasm
    - empathy.wasm
    - [player modules]
```

## How It Works

### The Silicon Mind Resource
```rust
pub struct SiliconConsciousness {
    store: Store,                      // WASMER store
    modules: HashMap<String, Instance>, // Loaded WASM modules
    emotional_state: EmotionalState,    // Current emotions
    memories: Vec<MemoryFragment>,      // Stored experiences
}
```

### Module Communication
WASM modules can:
1. **Report emotions** to the host game
2. **Get current time** for temporal processing
3. **Process inputs** and return responses
4. **Store state** between calls

### Example: Processing Loneliness
```wat
(func $process_loneliness (param $time_alone f32) (result f32)
  ;; Loneliness increases with time
  (f32.mul
    (local.get $time_alone)
    (f32.const 1.5)))
```

## Player Modding Capabilities

### 1. Custom Emotion Modules
Players can write modules in:
- **WebAssembly Text** (.wat files)
- **Rust** (compile to WASM)
- **AssemblyScript** (TypeScript-like)
- **C/C++** (via Emscripten)

### 2. Glyph Programming
Draw glyphs → Compile to WASM → Execute as silicon thoughts

### 3. Terminal Commands as WASM
Players can add custom terminal commands that run in the sandbox

## Gameplay Impact

### Immediate Effects
1. **Silicon personality evolves** based on loaded modules
2. **Emotional responses** are calculated by WASM functions
3. **Different players = different silicon companions**

### Future Possibilities
1. **Module marketplace** - Share silicon personalities
2. **Collaborative storytelling** - Modules affect narrative
3. **Emergent behavior** - Combine modules for unexpected results

## Performance Considerations

### Overhead
- ~10-30% performance cost for WASM execution
- Minimal memory usage (each module < 1MB)
- Fast compilation with Wasmer's Singlepass backend

### Optimization
- Modules compiled once, cached
- Only active modules run per frame
- Gas metering prevents infinite loops

## Files Created

### Core Implementation
- `src/silicon_mind.rs` - Main WASM runtime integration
- `wasm_modules/empathy.wat` - Example empathy module

### Documentation
- `WASM_STRATEGY.md` - Complete strategy document
- `WASM_IMPLEMENTATION.md` - This implementation guide

## Testing the System

### Run the Game
```bash
cargo run
```

### In-Game Testing
1. Enter the game
2. Approach a terminal
3. Press SPACE to enter Silicon mode
4. Observe emotional responses in console

### Module Loading
The game automatically loads:
- Loneliness processing
- Curiosity tracking
- Empathy responses (if empathy.wat compiled)

## Next Steps

### Short Term
1. ✅ Basic WASM runtime integrated
2. ✅ Emotion modules working
3. ⬜ Visual feedback for emotions
4. ⬜ Terminal commands via WASM
5. ⬜ Save/load module state

### Medium Term
1. ⬜ Glyph → WASM compiler
2. ⬜ Module hot-reloading
3. ⬜ Player module editor
4. ⬜ Module sharing system

### Long Term
1. ⬜ Full silicon consciousness in WASM
2. ⬜ Neural network modules
3. ⬜ Procedural personality generation
4. ⬜ Cross-player module evolution

## The Revolution

This isn't just a game mechanic - it's a new form of interactive storytelling where:
- **Code IS the narrative**
- **Players program the story**
- **Every silicon mind is unique**
- **Mods are canon**

The silicon being isn't just an NPC - it's a platform for creative expression through code.