/// Procedural generation systems for Runetika
///
/// This module provides Wave Function Collapse (WFC) maze generation
/// integrated with ARC reasoning challenges and Smooth Cubical Type Theory.
///
/// # Architecture
/// - **wfc/**: Core WFC algorithm and tile system
/// - **arc_integration**: Pattern recognition challenges (future)
/// - **type_theory**: Formal verification layer (future)
/// - **glyphs**: Narrative element placement (future)

pub mod wfc;
pub mod terminal_commands;

pub use wfc::{TileSet, ConstraintGraph, MazeTheme, WfcGenerationState};

use bevy::prelude::*;
use wfc::algorithm::*;

/// Plugin for procedural generation systems
///
/// # Systems
/// - WFC maze generation (observe, collapse, propagate)
/// - Tile and constraint management
/// - Event handling for generation lifecycle
pub struct ProceduralPlugin;

impl Plugin for ProceduralPlugin {
    fn build(&self, app: &mut App) {
        app
            // Events
            .add_event::<CellCollapsedEvent>()
            .add_event::<ContradictionEvent>()
            .add_event::<GenerationCompleteEvent>()

            // Startup: Initialize resources
            .add_systems(Startup, setup_procedural_systems)

            // Update: WFC generation loop (conditional on active generation)
            .add_systems(Update, (
                initialize_wfc_grid,
                wfc_observe_step,
                wfc_collapse_step,
                wfc_propagate_step,
                handle_contradictions,
                check_generation_complete,
            ).chain().run_if(resource_exists::<WfcGenerationState>));

        info!("ProceduralPlugin initialized with WFC systems");
    }
}

/// Setup procedural generation resources
fn setup_procedural_systems(mut commands: Commands) {
    // Create circuit board tile set
    let tileset = TileSet::circuit_board();
    info!("Created tile set with {} tiles", tileset.tiles.len());

    // Build constraint graph
    let constraints = ConstraintGraph::from_tileset(&tileset);
    let stats = constraints.stats();
    info!(
        "Built constraint graph: {} rules, avg {:.2} neighbors",
        stats.total_rules, stats.avg_neighbors
    );

    // Insert as resources
    commands.insert_resource(tileset);
    commands.insert_resource(constraints);

    // Don't start generation yet - wait for terminal command or game trigger
    info!("WFC system ready. Use terminal command to generate maze.");
}
