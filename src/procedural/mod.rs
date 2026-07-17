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

pub use wfc::{TileSet, ConstraintGraph, WfcGenerationState};

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
            // Sub-plugins
            .add_plugins(wfc::renderer::WfcRendererPlugin)

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

        info!("ProceduralPlugin initialized with WFC systems and isometric renderer");
    }
}

/// Drain WFC generation requests queued by terminal commands and kick
/// off generation by inserting a `WfcGenerationState` resource.
///
/// Previously this scanned `TerminalHistory.lines` for a stringly-typed
/// `__WFC_REQUEST__:w:h:seed` marker, which was fragile: history
/// navigation or replay could silently re-trigger generation. The
/// structured `pending_wfc_requests` queue on `TerminalHistory` avoids
/// that class of bug.
fn handle_pending_requests(
    mut commands: Commands,
    mut terminal_history: ResMut<crate::terminal::TerminalHistory>,
) {
    if terminal_history.pending_wfc_requests.is_empty() {
        return;
    }
    // If the player rapidly fires multiple `generate_wfc_maze` commands
    // in one frame, honour only the most recent request — earlier ones
    // are discarded to avoid stomping a generation that is about to start.
    let last = terminal_history.pending_wfc_requests.drain(..).last();
    if let Some(req) = last {
        info!(
            "Starting WFC generation: {}x{} seed={}",
            req.width, req.height, req.seed
        );
        commands.insert_resource(WfcGenerationState::new(req.width, req.height, req.seed));
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
