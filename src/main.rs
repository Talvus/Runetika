// Core game systems
use bevy::prelude::*;
use bevy::window::{PresentMode, WindowTheme};

mod menu;
mod settings;
mod credits;
mod silicon_mind;
mod terminal_interface;
mod terminal_commands;
mod perspective;
mod player;
mod spaceship;
mod puzzle;
mod arc_engine;
mod papilio;

use menu::MainMenuPlugin;
use settings::SettingsPlugin;
use credits::CreditsPlugin;
use silicon_mind::SiliconMindPlugin;
use terminal_interface::TerminalInterfacePlugin;
use arc_engine::ARCEnginePlugin;
use papilio::PapilioPlugin;

/// Core game state management
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash, States)]
pub enum GameState {
    #[default]
    MainMenu,
    InGame,
    Settings,
    Credits,
    Terminal,
}

fn main() {
    App::new()
        .add_plugins(
            DefaultPlugins
                .set(WindowPlugin {
                    primary_window: Some(Window {
                        title: "Runetika".to_string(),
                        resolution: (1280.0, 720.0).into(),
                        present_mode: PresentMode::AutoVsync,
                        window_theme: Some(WindowTheme::Dark),
                        ..default()
                    }),
                    ..default()
                })
                .set(ImagePlugin::default_nearest()),
        )
        .init_state::<GameState>()
        .add_plugins((
            MainMenuPlugin,
            SettingsPlugin,
            CreditsPlugin,
            SiliconMindPlugin,
            TerminalInterfacePlugin,
            ARCEnginePlugin,
            PapilioPlugin,
        ))
        .run();
}