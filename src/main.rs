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

// iOS FFI bridge - only compile for iOS targets
#[cfg(any(target_os = "ios", feature = "ios-ffi"))]
pub mod ios_ffi;

// iOS-specific optimizations
#[cfg(any(target_os = "ios", feature = "ios-ffi"))]
pub mod ios_metal_renderer;
#[cfg(any(target_os = "ios", feature = "ios-ffi"))]
pub mod ios_touch_predictor;
#[cfg(any(target_os = "ios", feature = "ios-ffi"))]
pub mod ios_asset_optimizer;

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
    let mut app = App::new();
    
    // Configure for iOS if running on iOS
    #[cfg(target_os = "ios")]
    let window_plugin = WindowPlugin {
        primary_window: Some(Window {
            title: "Runetika".to_string(),
            // iOS-optimized resolution
            resolution: (2556.0, 1179.0).into(), // iPhone 15 Pro
            present_mode: PresentMode::Mailbox, // Lower latency for 120Hz
            window_theme: Some(WindowTheme::Dark),
            ..default()
        }),
        ..default()
    };
    
    #[cfg(not(target_os = "ios"))]
    let window_plugin = WindowPlugin {
        primary_window: Some(Window {
            title: "Runetika".to_string(),
            resolution: (1280.0, 720.0).into(),
            present_mode: PresentMode::AutoVsync,
            window_theme: Some(WindowTheme::Dark),
            ..default()
        }),
        ..default()
    };
    
    app.add_plugins(
        DefaultPlugins
            .set(window_plugin)
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
    ));
    
    // Add iOS-specific optimization plugins
    #[cfg(any(target_os = "ios", feature = "ios-ffi"))]
    {
        use ios_metal_renderer::IOSMetalPlugin;
        use ios_touch_predictor::IOSTouchPredictionPlugin;
        use ios_asset_optimizer::IOSAssetOptimizationPlugin;
        
        app.add_plugins((
            IOSMetalPlugin,
            IOSTouchPredictionPlugin,
            IOSAssetOptimizationPlugin,
        ));
    }
    
    app.run();
}