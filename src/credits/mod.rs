//! Credits screen module for displaying game credits and acknowledgments.
//!
//! This module provides a beautifully animated credits screen that showcases
//! the development team, contributors, and technologies used in creating Runetika.

use bevy::prelude::*;
use crate::game_state::GameState;

pub mod ui;
pub mod systems;

use self::ui::*;
use self::systems::*;

/// Plugin responsible for managing the credits screen functionality
pub struct CreditsPlugin;

impl Plugin for CreditsPlugin {
    fn build(&self, app: &mut App) {
        app
            .init_resource::<CreditsState>()
            .add_systems(OnEnter(GameState::Credits), setup_credits_screen)
            .add_systems(OnExit(GameState::Credits), cleanup_credits_screen)
            .add_systems(Update, (
                handle_credits_input,
                animate_credits_scroll,
                animate_credits_elements,
            ).run_if(in_state(GameState::Credits)));
    }
}

/// Resource tracking the state of the credits screen
#[derive(Resource, Default)]
pub struct CreditsState {
    /// Current scroll position for animated credits
    pub scroll_position: f32,
    
    /// Speed of automatic scrolling
    pub scroll_speed: f32,
    
    /// Whether credits are auto-scrolling
    pub is_auto_scrolling: bool,
    
    /// Total height of credits content
    pub content_height: f32,
}

impl CreditsState {
    /// Creates a new credits state with default values
    pub fn new() -> Self {
        Self {
            scroll_position: 0.0,
            scroll_speed: 30.0,  // Pixels per second
            is_auto_scrolling: true,
            content_height: 0.0,
        }
    }
}

/// Marker component for the credits screen root entity
#[derive(Component)]
pub struct CreditsScreen;

/// Marker component for scrollable credits content
#[derive(Component)]
pub struct CreditsContent;

/// Component for animated credit entries
#[derive(Component)]
pub struct CreditEntry {
    pub delay: f32,
    pub animation_timer: f32,
}