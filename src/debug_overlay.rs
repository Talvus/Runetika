use bevy::prelude::*;
use std::collections::VecDeque;

/// Debug Overlay UI System
/// 
/// Provides a non-intrusive overlay for real-time debugging information
/// that can be toggled during both development and gameplay.

pub struct DebugOverlayPlugin;

impl Plugin for DebugOverlayPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(OverlayState::default())
            .add_systems(Startup, setup_debug_overlay)
            .add_systems(Update, (
                update_overlay_metrics,
                render_overlay_ui,
                handle_overlay_input,
            ).chain());
    }
}

#[derive(Resource)]
pub struct OverlayState {
    pub visible: bool,
    pub position: OverlayPosition,
    pub panels: Vec<DebugPanel>,
    pub transparency: f32,
    pub font_size: f32,
}

impl Default for OverlayState {
    fn default() -> Self {
        Self {
            visible: false,
            position: OverlayPosition::TopRight,
            panels: vec![
                DebugPanel::Performance,
                DebugPanel::EntityInfo,
                DebugPanel::SystemGraph,
            ],
            transparency: 0.8,
            font_size: 12.0,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum OverlayPosition {
    TopLeft,
    TopRight,
    BottomLeft,
    BottomRight,
    Center,
}

#[derive(Clone, Debug, PartialEq)]
pub enum DebugPanel {
    Performance,
    EntityInfo,
    SystemGraph,
    Console,
    TypeInspector,
    MemoryProfile,
    Custom(String),
}

/// UI components for the overlay
#[derive(Component)]
pub struct DebugOverlayRoot;

#[derive(Component)]
pub struct FpsDisplay;

#[derive(Component)]
pub struct EntityCountDisplay;

#[derive(Component)]
pub struct MemoryDisplay;

#[derive(Component)]
pub struct ConsoleOutput {
    pub lines: VecDeque<ConsoleLine>,
    pub max_lines: usize,
}

#[derive(Clone)]
pub struct ConsoleLine {
    pub text: String,
    pub level: LogLevel,
    pub timestamp: f32,
}

#[derive(Clone, Copy)]
pub enum LogLevel {
    Info,
    Warning,
    Error,
    Debug,
}

/// Setup the debug overlay UI
fn setup_debug_overlay(
    mut commands: Commands,
) {
    // Root overlay container
    commands.spawn((
        DebugOverlayRoot,
        NodeBundle {
            style: Style {
                position_type: PositionType::Absolute,
                right: Val::Px(10.0),
                top: Val::Px(10.0),
                flex_direction: FlexDirection::Column,
                padding: UiRect::all(Val::Px(10.0)),
                ..default()
            },
            background_color: BackgroundColor(Color::srgba(0.0, 0.0, 0.0, 0.8)),
            visibility: Visibility::Hidden,
            ..default()
        },
    )).with_children(|parent| {
        // FPS Display
        parent.spawn((
            FpsDisplay,
            TextBundle::from_section(
                "FPS: --",
                TextStyle {
                    font_size: 14.0,
                    color: Color::srgb(0.0, 1.0, 0.0),
                    ..default()
                },
            ),
        ));
        
        // Entity Count Display
        parent.spawn((
            EntityCountDisplay,
            TextBundle::from_section(
                "Entities: --",
                TextStyle {
                    font_size: 14.0,
                    color: Color::srgb(0.8, 0.8, 0.8),
                    ..default()
                },
            ),
        ));
        
        // Memory Display
        parent.spawn((
            MemoryDisplay,
            TextBundle::from_section(
                "Memory: -- MB",
                TextStyle {
                    font_size: 14.0,
                    color: Color::srgb(0.8, 0.8, 0.8),
                    ..default()
                },
            ),
        ));
    });
}

/// Update overlay metrics
fn update_overlay_metrics(
    time: Res<Time>,
    mut fps_query: Query<&mut Text, With<FpsDisplay>>,
    mut entity_query: Query<&mut Text, (With<EntityCountDisplay>, Without<FpsDisplay>)>,
    all_entities: Query<Entity>,
) {
    // Update FPS
    if let Ok(mut text) = fps_query.get_single_mut() {
        let fps = 1.0 / time.delta_secs();
        text.sections[0].value = format!("FPS: {:.0}", fps);
        
        // Color code based on performance
        text.sections[0].style.color = if fps >= 60.0 {
            Color::srgb(0.0, 1.0, 0.0) // Green
        } else if fps >= 30.0 {
            Color::srgb(1.0, 1.0, 0.0) // Yellow
        } else {
            Color::srgb(1.0, 0.0, 0.0) // Red
        };
    }
    
    // Update entity count
    if let Ok(mut text) = entity_query.get_single_mut() {
        let count = all_entities.iter().count();
        text.sections[0].value = format!("Entities: {}", count);
    }
}

/// Render the overlay UI
fn render_overlay_ui(
    overlay_state: Res<OverlayState>,
    mut visibility_query: Query<&mut Visibility, With<DebugOverlayRoot>>,
) {
    if let Ok(mut visibility) = visibility_query.get_single_mut() {
        *visibility = if overlay_state.visible {
            Visibility::Visible
        } else {
            Visibility::Hidden
        };
    }
}

/// Handle overlay input
fn handle_overlay_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut overlay_state: ResMut<OverlayState>,
) {
    // Toggle with F3
    if keyboard.just_pressed(KeyCode::F3) {
        overlay_state.visible = !overlay_state.visible;
        info!("Debug overlay: {}", if overlay_state.visible { "ON" } else { "OFF" });
    }
    
    // Change position with F4
    if keyboard.just_pressed(KeyCode::F4) && overlay_state.visible {
        overlay_state.position = match overlay_state.position {
            OverlayPosition::TopRight => OverlayPosition::TopLeft,
            OverlayPosition::TopLeft => OverlayPosition::BottomLeft,
            OverlayPosition::BottomLeft => OverlayPosition::BottomRight,
            OverlayPosition::BottomRight => OverlayPosition::TopRight,
            OverlayPosition::Center => OverlayPosition::TopRight,
        };
    }
}