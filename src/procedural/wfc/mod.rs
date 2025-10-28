/// Wave Function Collapse maze generation system
///
/// # Conceptual Model: Quantum Collapse Metaphor
/// Each cell exists in superposition of all possible tiles until "observed".
/// Observation collapses one cell, constraining neighbors through quantum entanglement.
/// The maze emerges from cascading wave function collapse.
///
/// # ARC Integration
/// WFC embodies core ARC reasoning: inferring rules from examples, predicting
/// transformations, and abstract pattern completion.

pub mod tiles;
pub mod constraints;
pub mod algorithm;
pub mod renderer;

pub use tiles::{Tile, TileId, TileSet, TileVariant, SocketType, MazeTheme};
pub use constraints::{ConstraintGraph, Direction};
pub use algorithm::{
    WfcCell, WfcGenerationState, CellCollapsedEvent, ContradictionEvent, GenerationCompleteEvent,
};
pub use renderer::{WfcRendererPlugin, WfcTileSprite, IsometricDepthSorted};
