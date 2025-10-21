/// Terminal commands for WFC maze generation
///
/// Provides player control over procedural generation through the terminal interface.

use bevy::prelude::*;
use super::wfc::{WfcGenerationState, GenerationCompleteEvent};

/// Command: /generate_wfc_maze [width] [height] [seed]
///
/// Generates a new WFC maze with specified parameters.
///
/// # Arguments
/// - width: Grid width (default: 16)
/// - height: Grid height (default: 16)
/// - seed: Random seed (default: current timestamp)
///
/// # Examples
/// - `/generate_wfc_maze` - 16x16 with random seed
/// - `/generate_wfc_maze 32 32` - 32x32 with random seed
/// - `/generate_wfc_maze 20 20 12345` - 20x20 with seed 12345
pub fn cmd_generate_wfc_maze(
    args: &[String],
    commands: &mut Commands,
) -> String {
    // Parse arguments
    let width = args
        .get(0)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(16)
        .clamp(8, 64);

    let height = args
        .get(1)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(16)
        .clamp(8, 64);

    let seed = args
        .get(2)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or_else(|| {
            use std::time::SystemTime;
            SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_secs()
        });

    // Create generation state resource
    let gen_state = WfcGenerationState::new(width, height, seed);
    commands.insert_resource(gen_state);

    format!(
        "🌀 Initiating WFC maze generation...\n\
         Size: {}x{}\n\
         Seed: {}\n\
         Watch the quantum collapse unfold...",
        width, height, seed
    )
}

/// System: Log generation completion to console
pub fn log_generation_complete(
    mut complete_events: EventReader<GenerationCompleteEvent>,
) {
    for event in complete_events.read() {
        info!(
            "✨ Maze generation complete! {}x{} in {} steps",
            event.width, event.height, event.steps
        );
    }
}

/// Register WFC commands with terminal system
pub fn register_wfc_commands() {
    // This would integrate with the existing terminal command registry
    // For now, this is a placeholder showing the intended structure
    info!("WFC terminal commands registered");
}
