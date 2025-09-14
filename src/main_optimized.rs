// Optimized Runetika main entry point
// Minimal dependencies for fastest compilation

use bevy::prelude::*;
use bevy::window::{PresentMode, WindowTheme};
use bevy::diagnostic::{FrameTimeDiagnosticsPlugin, LogDiagnosticsPlugin};

/// Core game state management
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash, States)]
pub enum GameState {
    #[default]
    MainMenu,
    InGame,
    Settings,
}

fn main() {
    let mut app = App::new();
    
    // Configure for optimal performance
    app.add_plugins(
        DefaultPlugins
            .set(WindowPlugin {
                primary_window: Some(Window {
                    title: "Runetika - Optimized".to_string(),
                    resolution: (1280.0, 720.0).into(),
                    present_mode: PresentMode::AutoVsync,
                    window_theme: Some(WindowTheme::Dark),
                    // Reduce input latency
                    focused: true,
                    ..default()
                }),
                ..default()
            })
            .set(ImagePlugin::default_nearest())
            // Disable unnecessary plugins for faster compile
            .disable::<bevy::audio::AudioPlugin>()
            .disable::<bevy::gilrs::GilrsPlugin>()
    );
    
    // Add performance monitoring
    app.add_plugins((
        FrameTimeDiagnosticsPlugin,
        LogDiagnosticsPlugin::default(),
    ));
    
    // Initialize game state
    app.init_state::<GameState>();
    
    // Add optimized systems
    app.add_systems(Startup, setup_game);
    app.add_systems(Update, (
        handle_input.run_if(in_state(GameState::MainMenu)),
        update_game.run_if(in_state(GameState::InGame)),
    ));
    
    // Enable multi-threading for ECS
    app.insert_resource(bevy::ecs::schedule::ScheduleBuildSettings {
        ambiguity_detection: false, // Disable for performance
        ..default()
    });
    
    app.run();
}

fn setup_game(mut commands: Commands) {
    // Camera
    commands.spawn(Camera2dBundle::default());
    
    // Simple UI
    commands
        .spawn(NodeBundle {
            style: Style {
                width: Val::Percent(100.0),
                height: Val::Percent(100.0),
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                ..default()
            },
            background_color: BackgroundColor(Color::srgb(0.1, 0.1, 0.15)),
            ..default()
        })
        .with_children(|parent| {
            parent.spawn(TextBundle::from_section(
                "Runetika - Optimized Build",
                TextStyle {
                    font_size: 60.0,
                    color: Color::WHITE,
                    ..default()
                },
            ));
        });
    
    info!("Game setup complete - optimized version");
}

fn handle_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    if keyboard.just_pressed(KeyCode::Space) {
        next_state.set(GameState::InGame);
        info!("Transitioning to InGame state");
    }
    
    if keyboard.just_pressed(KeyCode::Escape) {
        info!("Exit requested");
        std::process::exit(0);
    }
}

fn update_game(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut next_state: ResMut<NextState<GameState>>,
    time: Res<Time>,
) {
    // Simple game update
    if keyboard.just_pressed(KeyCode::Escape) {
        next_state.set(GameState::MainMenu);
    }
    
    // Performance-optimized update
    let _delta = time.delta_seconds();
    // Game logic here
}