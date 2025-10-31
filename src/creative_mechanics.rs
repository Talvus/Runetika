/// Creative Mechanics Module - Integration point for all innovative game systems
/// 
/// This module brings together all the creative gameplay mechanics that make
/// Runetika unique: pattern recognition, temporal manipulation, consciousness
/// reconstruction, and mathematical visualization.

pub mod glyph_resonance;
pub mod pattern_echo;
pub mod temporal_layers;
pub mod consciousness_fragments;
pub mod type_theory_viz;

use bevy::prelude::*;

/// Master plugin that includes all creative mechanics
pub struct CreativeMechanicsPlugin;

impl Plugin for CreativeMechanicsPlugin {
    fn build(&self, app: &mut App) {
        app
            // Core mechanics
            .add_plugins(glyph_resonance::GlyphResonancePlugin)
            .add_plugins(pattern_echo::PatternEchoPlugin)
            .add_plugins(temporal_layers::TemporalLayerPlugin)
            .add_plugins(consciousness_fragments::ConsciousnessFragmentsPlugin)
            .add_plugins(type_theory_viz::TypeTheoryVizPlugin)
            
            // Integration systems
            .add_systems(Update, (
                integrate_mechanics,
                sync_consciousness_levels,
                update_puzzle_complexity,
            ));
    }
}

/// Integrate different mechanics to create emergent gameplay
fn integrate_mechanics(
    glyph_query: Query<&glyph_resonance::Glyph>,
    echo_recorder: Res<pattern_echo::EchoRecorder>,
    temporal_field: Res<temporal_layers::TemporalField>,
    fragments: Res<consciousness_fragments::FragmentCollection>,
    type_space: Res<type_theory_viz::TypeSpace>,
) {
    // Cross-mechanic interactions
    
    // Glyphs resonate stronger in certain temporal layers
    let temporal_resonance = temporal_field.chrono_stability;
    
    // Pattern echoes become more powerful with more consciousness fragments
    let echo_power = fragments.total_consciousness * 0.1;
    
    // Type theory visualization unlocks based on glyph discoveries
    let viz_complexity = glyph_query.iter().filter(|g| g.discovered).count() as f32;
    
    // Log integration status
    if viz_complexity > 5.0 {
        info!("Advanced mechanics unlocked: {} glyphs discovered", viz_complexity);
    }
}

/// Synchronize consciousness levels across all systems
fn sync_consciousness_levels(
    mut silicon_mind: ResMut<crate::silicon_mind::SiliconMindState>,
    fragments: Res<consciousness_fragments::FragmentCollection>,
    temporal_field: Res<temporal_layers::TemporalField>,
) {
    // Unified consciousness calculation
    let fragment_consciousness = fragments.total_consciousness * 0.3;
    let temporal_consciousness = temporal_field.chrono_stability * 0.2;
    let base_consciousness = silicon_mind.consciousness_level;
    
    // Update Silicon Mind with combined consciousness
    silicon_mind.consciousness_level = (base_consciousness + fragment_consciousness + temporal_consciousness)
        .min(1.0);
}

/// Dynamically adjust puzzle complexity based on player progress
fn update_puzzle_complexity(
    echo_recorder: Res<pattern_echo::EchoRecorder>,
    mut pattern_library: ResMut<pattern_echo::PatternLibrary>,
    fragments: Res<consciousness_fragments::FragmentCollection>,
) {
    // Calculate player skill level
    let echoes_mastered = echo_recorder.saved_echoes.len() as f32;
    let fragments_collected = fragments.collected.len() as f32;
    let skill_level = (echoes_mastered * 0.5 + fragments_collected * 0.5) / 10.0;
    
    // Adjust ARC challenge difficulty
    for challenge in &mut pattern_library.arc_challenges {
        if !challenge.solved {
            challenge.difficulty = (challenge.difficulty + skill_level * 0.1).min(1.0);
        }
    }
}