//! Main Menu Module - The Gateway to the Game
//! 
//! # Design Philosophy
//! The menu is the player's first impression. It sets the tone (cosmic, mysterious)
//! and provides clear navigation. Every animation and color choice reinforces
//! the space exploration theme.
//! 
//! # Module Architecture
//! - `components`: Data structures for menu elements (buttons, backgrounds)
//! - `systems`: Logic for navigation, selection, and transitions
//! - `ui`: Visual design, layout, and animations
//! 
//! # User Experience Flow
//! 1. Player sees animated title and starfield
//! 2. Navigates options with keyboard or mouse
//! 3. Selects action (start game, settings, etc.)
//! 4. Smooth transition to next state

pub mod components;
pub mod systems;
pub mod ui;

use bevy::prelude::*;
use crate::game_state::GameState;
use self::systems::*;
use self::ui::*;

/// Main menu plugin - Orchestrates all menu functionality
/// 
/// # Integration
/// This plugin manages the complete menu lifecycle:
/// - Setup when entering MainMenu state
/// - Update during menu interaction
/// - Cleanup when leaving to another state
pub struct MainMenuPlugin;

impl Plugin for MainMenuPlugin {
    fn build(&self, app: &mut App) {
        app
            .init_resource::<MenuState>()
            .add_systems(OnEnter(GameState::MainMenu), setup_main_menu)
            .add_systems(OnExit(GameState::MainMenu), cleanup_main_menu)
            .add_systems(Update, (
                handle_menu_navigation,
                update_menu_buttons,
                animate_menu_elements,
                handle_button_interactions,
            ).run_if(in_state(GameState::MainMenu)));
    }
}

/// Menu state - Tracks current menu status and selection
/// 
/// # State Management
/// This resource maintains the menu's runtime state:
/// - Which button is currently selected
/// - References to all menu buttons for updates
/// - Whether we're transitioning (prevents input during animations)
/// 
/// # Why Vec<Entity>?
/// We need to track button entities to update their appearance
/// when selection changes. Entities are Bevy's way of referencing game objects.
#[derive(Resource, Default)]
pub struct MenuState {
    pub selected_index: usize,
    pub menu_items: Vec<Entity>,
    pub is_transitioning: bool,
}