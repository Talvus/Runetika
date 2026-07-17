//! Lemma Bridge — Connects Runetika's gameplay to Lemma's proof kernel.
//!
//! This module implements the Three-Level Identity:
//! 1. Rust tile function (lemma-geometry)
//! 2. ALIEN expression (lemma-alien)
//! 3. Runetika player action (this module)
//!
//! The bridge wraps Lemma's library types as Bevy Resources and Events,
//! enabling proof-as-gameplay without exposing formal syntax to the player.

pub mod resources;
pub mod events;
pub mod systems;
pub mod commands;

use bevy::prelude::*;
use crate::game_state::GameState;

use self::resources::ProofWorkspace;
use self::events::*;
use self::systems::*;
use self::commands::register_lemma_commands;

/// Plugin that integrates Lemma's proof kernel into Runetika.
///
/// Adds proof workspace resources, ALIEN parsing events,
/// and terminal commands for interacting with the proof system.
pub struct LemmaBridgePlugin;

impl Plugin for LemmaBridgePlugin {
    fn build(&self, app: &mut App) {
        app
            // Resources
            .insert_resource(ProofWorkspace::new())
            .insert_resource(resources::ProofCertificates::default())
            // Events
            .add_event::<ProofVerifiedEvent>()
            // Systems
            .add_systems(OnEnter(GameState::InGame), register_lemma_commands)
            .add_systems(Update, (
                check_proof_completion,
            ).run_if(in_state(GameState::InGame)));
    }
}
