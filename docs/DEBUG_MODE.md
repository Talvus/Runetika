# Type Theory Visualization Debug Mode

## Overview

The Type Theory Visualization system in Runetika serves dual purposes:
1. **Gameplay**: Visualize and manipulate mathematical concepts as part of the game
2. **Debugging**: Powerful runtime introspection and profiling tools for development

This document describes the debug features and how to use them effectively.

## Quick Start

### Enabling Debug Mode

```bash
# Build with debug features
cargo build --features debug

# Run with debug features
cargo run --features debug
```

### Key Bindings

| Key | Action |
|-----|--------|
| F3 | Toggle debug overlay |
| F4 | Cycle overlay position |
| F11 | Cycle debug modes |
| F12 | Toggle debug mode on/off |
| P | Pause execution (when debugging) |
| S | Take debug snapshot |
| C | Clear debug info |
| V | Toggle type visualization |

## Debug Modes

### 1. Entity Inspector
Inspect ECS entities and their components in real-time.

```rust
// Select entity for inspection
debug_context.selected_entity = Some(entity);

// View component data
let inspection = inspect_entity(entity);
```

### 2. System Profiler
Profile system execution times and identify performance bottlenecks.

- Frame time graph
- System execution timeline
- Hotspot detection
- Memory usage tracking

### 3. Type Checker
Validate type constraints and invariants at runtime.

```rust
// Define type constraint
let constraint = TypeConstraint {
    name: "MeshRequiresTransform",
    predicate: ConstraintPredicate::ComponentRequires("Mesh", "Transform"),
    severity: ConstraintSeverity::Error,
};
```

### 4. Memory Analyzer
Track memory usage across different subsystems.

- Heap usage
- Component pool sizes
- Asset memory (textures, meshes)
- Entity count tracking

### 5. Network Debugger
Debug multiplayer and networking (when implemented).

### 6. AI Reasoning Visualizer
Visualize AI decision trees and reasoning chains.

## Debug Overlay

The debug overlay provides real-time information without blocking gameplay:

- **FPS Counter**: Color-coded performance indicator
  - Green: 60+ FPS
  - Yellow: 30-60 FPS
  - Red: <30 FPS
- **Entity Count**: Total entities in the world
- **Memory Usage**: Current heap usage
- **System Graph**: Visual representation of system dependencies

## Breakpoint System

Set breakpoints to pause execution when conditions are met:

```rust
// Break when entity spawns with specific component
debug_break!(context, BreakpointCondition::EntitySpawned(
    ComponentFilter { type_name: "Player".to_string(), predicate: None }
));

// Break on frame number
debug_break!(context, BreakpointCondition::FrameNumber(100));

// Custom condition
debug_break!(context, BreakpointCondition::Custom(Box::new(|world| {
    world.resource::<Time>().elapsed_secs() > 10.0
})));
```

## Watch System

Monitor values in real-time:

```rust
// Watch entity position
debug_watch!(context, "player_pos", WatchTarget::Entity(player_entity));

// Watch FPS
debug_watch!(context, "fps", WatchTarget::Performance(MetricType::FPS));

// Watch resource
debug_watch!(context, "score", WatchTarget::Resource("Score"));
```

## Type Visualization Styles

### Graph View
- Nodes represent types
- Edges show relationships
- Color coding by type kind

### Tree View
- Hierarchical type structure
- Parent-child relationships
- Expandable/collapsible nodes

### Mathematical View
- Algebraic data type notation
- Product types: `A × B`
- Sum types: `A + B`
- Function types: `A → B`

## Performance Profiling

The profiler tracks:
- Frame times (last 120 frames)
- System execution times
- Memory samples (last 60 samples)
- Hotspot identification

```rust
// Start profiling
profiler.recording = true;

// Access metrics
let avg_frame_time = profiler.frame_times.iter().sum() / profiler.frame_times.len();
let fps = 1.0 / avg_frame_time;
```

## Snapshot System

Take snapshots for time-travel debugging:

```rust
// Take snapshot
let snapshot = DebugSnapshot {
    timestamp: Instant::now(),
    frame: current_frame,
    entities: collect_entity_snapshots(),
    resources: collect_resource_snapshots(),
    metrics: current_metrics,
};

// Store in history
debug_context.history.push_back(snapshot);

// Restore from snapshot (future feature)
restore_snapshot(&snapshot);
```

## Integration with Gameplay

The debug system seamlessly integrates with gameplay mechanics:

1. **Glyph Resonance**: Visualize resonance patterns and field strength
2. **Pattern Echo**: See recorded transformation sequences
3. **Temporal Layers**: Debug time paradoxes and causality
4. **Silicon Mind**: Inspect AI reasoning chains
5. **Consciousness Fragments**: Track fragment collection and memory reconstruction

## Best Practices

1. **Use conditional compilation**: Wrap debug code in `#[cfg(feature = "debug")]`
2. **Minimize overhead**: Disable profiling when not needed
3. **Clear old data**: Regularly clear debug history to save memory
4. **Set meaningful breakpoints**: Use descriptive conditions
5. **Watch critical values**: Monitor key gameplay variables

## Troubleshooting

### High Memory Usage
- Clear debug history: Press `C`
- Reduce snapshot frequency
- Disable memory profiling

### Performance Impact
- Disable system graph visualization
- Reduce overlay update frequency
- Use minimal verbosity level

### Missing Debug Info
- Ensure debug feature is enabled
- Check that types are registered
- Verify entity has Inspectable component

## Examples

### Debugging a Puzzle System

```rust
// Track puzzle state
debug_watch!(context, "puzzle_progress", WatchTarget::Resource("PuzzleState"));

// Break when puzzle is solved
debug_break!(context, BreakpointCondition::Custom(Box::new(|world| {
    world.resource::<PuzzleState>().is_solved()
})));

// Visualize puzzle grid
render_puzzle_debug(&puzzle, &mut gizmos);
```

### Profiling System Performance

```rust
// Profile specific system
profiler.system_times.entry("physics_system".to_string())
    .or_insert_with(VecDeque::new)
    .push_back(system_time);

// Identify hotspots
let hotspot = Hotspot {
    system_name: "physics_system".to_string(),
    average_time: avg_time,
    worst_time: max_time,
    call_count: calls,
};
```

### Type Constraint Validation

```rust
// Ensure components exist together
let constraint = TypeConstraint {
    name: "ColliderRequiresTransform",
    predicate: ConstraintPredicate::ComponentRequires(
        "Collider".to_string(),
        "Transform".to_string()
    ),
    severity: ConstraintSeverity::Error,
};

// Check constraints
validate_constraints(&world, &constraints);
```

## Future Enhancements

- **Record & Replay**: Record gameplay sessions for debugging
- **Remote Debugging**: Connect to running game instances
- **Visual Scripting**: Debug visual scripts and node graphs
- **Asset Pipeline Debug**: Track asset loading and processing
- **Network Replay**: Debug multiplayer sessions

## Contributing

When adding new debug features:
1. Follow the existing pattern of conditional compilation
2. Add corresponding tests in `tests/debug_tests.rs`
3. Update this documentation
4. Ensure minimal performance impact when disabled