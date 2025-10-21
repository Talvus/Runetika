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
pub use terminal_commands::GenerateWfcMazeCommand;

use bevy::prelude::*;
use wfc::algorithm::*;
use crate::game_state::GameState;

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

            // Terminal command registration (when entering InGame state)
            .add_systems(OnEnter(GameState::InGame), terminal_commands::register_wfc_commands)

            // Update: Handle pending requests and WFC loop
            .add_systems(Update, (
                handle_pending_requests,
                terminal_commands::log_generation_complete,
            ))
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

/// Handle pending WFC generation requests from terminal
///
/// Monitors terminal history for WFC request markers and triggers generation
fn handle_pending_requests(
    mut commands: Commands,
    mut terminal_history: ResMut<crate::terminal::TerminalHistory>,
) {
    // Look for WFC request markers in terminal history
    let mut request_indices = Vec::new();

    for (index, line) in terminal_history.lines.iter().enumerate() {
        if line.text.starts_with("__WFC_REQUEST__:") {
            request_indices.push(index);
        }
    }

    // Process requests and remove markers
    for &index in request_indices.iter().rev() {
        if let Some(line) = terminal_history.lines.get(index) {
            let parts: Vec<&str> = line.text.split(':').collect();
            if parts.len() == 4 {
                if let (Ok(width), Ok(height), Ok(seed)) = (
                    parts[1].parse::<usize>(),
                    parts[2].parse::<usize>(),
                    parts[3].parse::<u64>(),
                ) {
                    info!(
                        "Starting WFC generation: {}x{} seed={}",
                        width, height, seed
                    );
                    let gen_state = WfcGenerationState::new(width, height, seed);
                    commands.insert_resource(gen_state);
                }
            }
        }
        // Remove the marker line
        terminal_history.lines.remove(index);
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
