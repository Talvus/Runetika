mod terminal;
mod menu;
mod game_state;
mod credits;
mod settings;
mod spaceship;
mod spaceship_2d;
mod main_room;
mod maze;
mod player;
mod perspective;
mod puzzle;
mod silicon_mind;
mod terminal_interface;
mod terminal_commands;
mod creative_mechanics;

// New creative mechanics modules
mod glyph_resonance;
mod pattern_echo;
mod temporal_layers;
mod consciousness_fragments;
mod type_theory_viz;

use bevy::prelude::*;
use game_state::{GameStatePlugin, GameState};

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window { 
                title: "Runetika - Silicon Mind Odyssey".into(), 
                resolution: (1280., 800.).into(), 
                ..default() 
            }),
            ..default()
        }))
        .add_plugins((
            // Core systems
            GameStatePlugin,
            menu::MainMenuPlugin,
            terminal::TerminalPlugin,
            credits::CreditsPlugin,
            settings::SettingsPlugin,
            
            // Game rooms and spaces
            main_room::MainRoomPlugin,
            maze::MazePlugin,
            
            // Core gameplay
            perspective::PerspectivePlugin,
            puzzle::PuzzlePlugin,
            silicon_mind::SiliconMindPlugin,
            terminal_interface::TerminalInterfacePlugin,
            
            // Creative mechanics
            creative_mechanics::CreativeMechanicsPlugin,
        ))
        .add_systems(Update, handle_pause_input.run_if(in_state(GameState::InGame)))
        .run();
}

fn handle_pause_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    current_state: Res<State<GameState>>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    if keyboard.just_pressed(KeyCode::Escape) && current_state.get() == &GameState::InGame {
        next_state.set(GameState::MainMenu);
    }
}