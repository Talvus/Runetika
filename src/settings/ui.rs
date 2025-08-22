/// Settings UI - Visual interface for configuration
/// 
/// # Design Philosophy
/// The settings screen continues the space theme while prioritizing clarity.
/// Complex options are presented simply, with tooltips for deeper understanding.

use bevy::prelude::*;
use bevy::hierarchy::ChildBuilder;
use super::components::*;
use crate::game_state::GameState;

/// Color scheme for settings UI
mod colors {
    use bevy::prelude::Color;
    
    pub const BACKGROUND: Color = Color::srgba(0.02, 0.0, 0.05, 0.98);
    pub const TAB_ACTIVE: Color = Color::srgba(0.3, 0.1, 0.5, 0.9);
    pub const TAB_INACTIVE: Color = Color::srgba(0.1, 0.05, 0.2, 0.7);
    pub const SLIDER_TRACK: Color = Color::srgba(0.2, 0.1, 0.3, 0.8);
    pub const SLIDER_FILL: Color = Color::srgb(0.6, 0.3, 0.9);
    pub const TEXT_PRIMARY: Color = Color::srgb(0.9, 0.85, 0.95);
    pub const TEXT_SECONDARY: Color = Color::srgb(0.7, 0.65, 0.8);
}

/// Set up the settings screen UI
/// 
/// # Layout Strategy
/// - Tab bar at top for categories
/// - Content area with scrollable options
/// - Apply/Cancel buttons at bottom
pub fn setup_settings_screen(
    mut commands: Commands,
    settings: Res<SettingsData>,
) {
    // Root container
    commands.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            flex_direction: FlexDirection::Column,
            ..default()
        },
        BackgroundColor(colors::BACKGROUND),
        SettingsScreen,
    ))
    .with_children(|parent| {
        // Header with title
        spawn_header(parent);
        
        // Tab bar
        spawn_tab_bar(parent);
        
        // Content area (changes based on selected tab)
        spawn_content_area(parent, &settings);
        
        // Footer with action buttons
        spawn_footer(parent);
    });
}

/// Create the settings header
fn spawn_header(parent: &mut ChildBuilder) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Px(80.0),
            justify_content: JustifyContent::Center,
            align_items: AlignItems::Center,
            padding: UiRect::all(Val::Px(20.0)),
            ..default()
        },
        BackgroundColor(Color::srgba(0.1, 0.05, 0.2, 0.5)),
    ))
    .with_children(|header| {
        header.spawn((
            Text::new("⚙️ SETTINGS"),
            TextFont {
                font_size: 48.0,
                ..default()
            },
            TextColor(colors::TEXT_PRIMARY),
        ));
    });
}

/// Create the tab navigation bar
fn spawn_tab_bar(parent: &mut ChildBuilder) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Px(60.0),
            flex_direction: FlexDirection::Row,
            justify_content: JustifyContent::Center,
            column_gap: Val::Px(10.0),
            padding: UiRect::all(Val::Px(10.0)),
            ..default()
        },
    ))
    .with_children(|tabs| {
        // Graphics tab
        spawn_tab(tabs, "🎨 Graphics", SettingsTabType::Graphics, true);
        
        // Audio tab
        spawn_tab(tabs, "🔊 Audio", SettingsTabType::Audio, false);
        
        // Controls tab
        spawn_tab(tabs, "🎮 Controls", SettingsTabType::Controls, false);
        
        // Gameplay tab
        spawn_tab(tabs, "🎯 Gameplay", SettingsTabType::Gameplay, false);
    });
}

/// Create an individual tab button
fn spawn_tab(
    parent: &mut ChildBuilder,
    label: &str,
    tab_type: SettingsTabType,
    is_active: bool,
) {
    let bg_color = if is_active {
        colors::TAB_ACTIVE
    } else {
        colors::TAB_INACTIVE
    };
    
    parent.spawn((
        Node {
            padding: UiRect::axes(Val::Px(20.0), Val::Px(10.0)),
            justify_content: JustifyContent::Center,
            align_items: AlignItems::Center,
            ..default()
        },
        BackgroundColor(bg_color),
        BorderRadius::all(Val::Px(8.0)),
        Button,
        SettingsTab { tab_type },
    ))
    .with_children(|tab| {
        tab.spawn((
            Text::new(label),
            TextFont {
                font_size: 20.0,
                ..default()
            },
            TextColor(colors::TEXT_PRIMARY),
        ));
    });
}

/// Create the main content area
fn spawn_content_area(parent: &mut ChildBuilder, settings: &Res<SettingsData>) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            flex_grow: 1.0,
            padding: UiRect::all(Val::Px(30.0)),
            flex_direction: FlexDirection::Column,
            row_gap: Val::Px(20.0),
            overflow: Overflow::scroll_y(),
            ..default()
        },
    ))
    .with_children(|content| {
        // Show graphics settings by default
        spawn_graphics_settings(content, &settings.graphics);
    });
}

/// Create graphics settings controls
fn spawn_graphics_settings(parent: &mut ChildBuilder, graphics: &GraphicsSettings) {
    // Resolution Scale
    spawn_slider_control(
        parent,
        "Resolution Scale",
        "Render at lower resolution for performance",
        graphics.resolution_scale,
        0.5,
        2.0,
    );
    
    // VSync Mode
    spawn_dropdown_control(
        parent,
        "VSync Mode",
        "Synchronize with display refresh rate",
        &format!("{:?}", graphics.vsync),
        vec!["Off", "On", "Adaptive", "Fast"],
    );
    
    // Shadow Quality
    spawn_slider_control(
        parent,
        "Shadow Quality",
        "Higher quality shadows impact performance",
        graphics.shadow_quality as f32,
        0.0,
        3.0,
    );
    
    // Anti-aliasing
    spawn_dropdown_control(
        parent,
        "Anti-Aliasing",
        "Smooths jagged edges",
        &format!("{:?}", graphics.antialiasing),
        vec!["Off", "FXAA", "TAA", "MSAA 2x", "MSAA 4x", "MSAA 8x"],
    );
    
    // Particle Density
    spawn_slider_control(
        parent,
        "Particle Density",
        "Number of particle effects",
        graphics.particle_density,
        0.1,
        2.0,
    );
}

/// Create a slider control
fn spawn_slider_control(
    parent: &mut ChildBuilder,
    label: &str,
    tooltip: &str,
    value: f32,
    min: f32,
    max: f32,
) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            flex_direction: FlexDirection::Column,
            row_gap: Val::Px(5.0),
            ..default()
        },
    ))
    .with_children(|control| {
        // Label and value
        control.spawn((
            Node {
                flex_direction: FlexDirection::Row,
                justify_content: JustifyContent::SpaceBetween,
                ..default()
            },
        ))
        .with_children(|header| {
            // Label
            header.spawn((
                Text::new(label),
                TextFont {
                    font_size: 18.0,
                    ..default()
                },
                TextColor(colors::TEXT_PRIMARY),
            ));
            
            // Current value
            header.spawn((
                Text::new(format!("{:.1}", value)),
                TextFont {
                    font_size: 18.0,
                    ..default()
                },
                TextColor(colors::TEXT_SECONDARY),
            ));
        });
        
        // Tooltip
        control.spawn((
            Text::new(tooltip),
            TextFont {
                font_size: 14.0,
                ..default()
            },
            TextColor(colors::TEXT_SECONDARY.with_alpha(0.7)),
        ));
        
        // Slider track
        control.spawn((
            Node {
                width: Val::Percent(100.0),
                height: Val::Px(8.0),
                ..default()
            },
            BackgroundColor(colors::SLIDER_TRACK),
            BorderRadius::all(Val::Px(4.0)),
        ))
        .with_children(|track| {
            // Slider fill
            let fill_percent = ((value - min) / (max - min) * 100.0).clamp(0.0, 100.0);
            track.spawn((
                Node {
                    width: Val::Percent(fill_percent),
                    height: Val::Percent(100.0),
                    ..default()
                },
                BackgroundColor(colors::SLIDER_FILL),
                BorderRadius::all(Val::Px(4.0)),
            ));
        });
    });
}

/// Create a dropdown control
fn spawn_dropdown_control(
    parent: &mut ChildBuilder,
    label: &str,
    tooltip: &str,
    current: &str,
    _options: Vec<&str>,
) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            flex_direction: FlexDirection::Column,
            row_gap: Val::Px(5.0),
            ..default()
        },
    ))
    .with_children(|control| {
        // Label
        control.spawn((
            Text::new(label),
            TextFont {
                font_size: 18.0,
                ..default()
            },
            TextColor(colors::TEXT_PRIMARY),
        ));
        
        // Tooltip
        control.spawn((
            Text::new(tooltip),
            TextFont {
                font_size: 14.0,
                ..default()
            },
            TextColor(colors::TEXT_SECONDARY.with_alpha(0.7)),
        ));
        
        // Dropdown button
        control.spawn((
            Node {
                width: Val::Percent(100.0),
                padding: UiRect::all(Val::Px(10.0)),
                justify_content: JustifyContent::SpaceBetween,
                align_items: AlignItems::Center,
                flex_direction: FlexDirection::Row,
                ..default()
            },
            BackgroundColor(colors::SLIDER_TRACK),
            BorderRadius::all(Val::Px(4.0)),
            Button,
        ))
        .with_children(|dropdown| {
            dropdown.spawn((
                Text::new(current),
                TextFont {
                    font_size: 16.0,
                    ..default()
                },
                TextColor(colors::TEXT_PRIMARY),
            ));
            
            dropdown.spawn((
                Text::new("▼"),
                TextFont {
                    font_size: 16.0,
                    ..default()
                },
                TextColor(colors::TEXT_SECONDARY),
            ));
        });
    });
}

/// Create the footer with action buttons
fn spawn_footer(parent: &mut ChildBuilder) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Px(80.0),
            justify_content: JustifyContent::Center,
            align_items: AlignItems::Center,
            column_gap: Val::Px(20.0),
            flex_direction: FlexDirection::Row,
            padding: UiRect::all(Val::Px(20.0)),
            ..default()
        },
    ))
    .with_children(|footer| {
        // Apply button
        footer.spawn((
            Node {
                padding: UiRect::axes(Val::Px(30.0), Val::Px(15.0)),
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                ..default()
            },
            BackgroundColor(Color::srgba(0.2, 0.6, 0.3, 0.9)),
            BorderRadius::all(Val::Px(8.0)),
            Button,
        ))
        .with_children(|btn| {
            btn.spawn((
                Text::new("Apply"),
                TextFont {
                    font_size: 20.0,
                    ..default()
                },
                TextColor(colors::TEXT_PRIMARY),
            ));
        });
        
        // Cancel button
        footer.spawn((
            Node {
                padding: UiRect::axes(Val::Px(30.0), Val::Px(15.0)),
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                ..default()
            },
            BackgroundColor(Color::srgba(0.6, 0.2, 0.2, 0.9)),
            BorderRadius::all(Val::Px(8.0)),
            Button,
        ))
        .with_children(|btn| {
            btn.spawn((
                Text::new("Cancel"),
                TextFont {
                    font_size: 20.0,
                    ..default()
                },
                TextColor(colors::TEXT_PRIMARY),
            ));
        });
    });
}

/// Clean up settings screen when exiting
pub fn cleanup_settings_screen(
    mut commands: Commands,
    query: Query<Entity, With<SettingsScreen>>,
) {
    for entity in query.iter() {
        commands.entity(entity).despawn_recursive();
    }
}