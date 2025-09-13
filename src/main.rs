// Core game systems
mod game_state;
mod menu;
mod credits;
mod settings;
mod terminal;

// Game content systems
mod arc_engine;
mod silicon_mind_mvp;
mod pattern_echo_mvp;

use bevy::prelude::*;
use game_state::{GameStatePlugin, GameState};

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window { 
                title: "Runetika - Unified Architecture".into(), 
                resolution: (1280., 800.).into(), 
                ..default() 
            }),
            ..default()
        }))
        .add_plugins((
            // Core plugins
            GameStatePlugin,
            
            // UI plugins
            menu::MainMenuPlugin,
            terminal::TerminalPlugin,
            credits::CreditsPlugin,
            settings::SettingsPlugin,
            
            // Game content plugins
            arc_engine::ARCEnginePlugin,
            silicon_mind_mvp::SiliconMindMVPPlugin,
            pattern_echo_mvp::PatternEchoPlugin,
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