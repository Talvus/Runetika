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

pub use tiles::TileSet;
pub use constraints::ConstraintGraph;
pub use algorithm::{
    WfcCell, WfcGenerationState, GenerationCompleteEvent,
};
