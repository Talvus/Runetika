//! UI module for the main menu system.
//!
//! This module handles the visual presentation and layout of the game's main menu,
//! including animations, styling, and responsive design elements.

use bevy::prelude::*;
use super::components::*;
use super::MenuState;
use crate::common::colors::{background, text, button, effects};

/// Typography settings for consistent text rendering
pub mod typography {
    pub const TITLE_SIZE: f32 = 96.0;
    pub const SUBTITLE_SIZE: f32 = 24.0;
    pub const BUTTON_TEXT_SIZE: f32 = 28.0;
    pub const FOOTER_SIZE: f32 = 16.0;
    pub const VERSION_SIZE: f32 = 14.0;
}

/// Animation parameters for smooth transitions
pub mod animations {
    pub const GLOW_PULSE_SPEED: f32 = 1.5;
}

/// Re-export colors from common module for backward compatibility
pub mod colors {
    use crate::common::colors::{background, text, button, effects};

    pub const MENU_BG: bevy::prelude::Color = background::DEEP_SPACE;
    pub const TITLE_PRIMARY: bevy::prelude::Color = text::TITLE;
    pub const TITLE_GLOW: bevy::prelude::Color = text::TITLE_GLOW;
    pub const BUTTON_NORMAL: bevy::prelude::Color = button::NORMAL;
    pub const BUTTON_HOVER: bevy::prelude::Color = button::HOVER;
    pub const BUTTON_SELECTED: bevy::prelude::Color = button::SELECTED;
    pub const TEXT_PRIMARY: bevy::prelude::Color = text::PRIMARY;
    pub const TEXT_SECONDARY: bevy::prelude::Color = text::SECONDARY;
    pub const TEXT_ACCENT: bevy::prelude::Color = text::ACCENT;
    pub const STAR_COLOR: bevy::prelude::Color = effects::STAR;
    pub const NEBULA_COLOR: bevy::prelude::Color = effects::NEBULA;
}

/// Sets up the main menu UI hierarchy and visual elements.
pub fn setup_main_menu(
    mut commands: Commands,
    mut menu_state: ResMut<MenuState>,
) {
    menu_state.selected_index = 0;
    menu_state.menu_items.clear();

    // Root container with gradient background
    commands
        .spawn((
            Node {
                width: Val::Percent(100.0),
                height: Val::Percent(100.0),
                position_type: PositionType::Absolute,
                flex_direction: FlexDirection::Column,
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                ..default()
            },
            BackgroundColor(background::DEEP_SPACE),
            MainMenu,
            MenuBackground,
        ))
        .with_children(|parent| {
            // Animated starfield layer
            spawn_enhanced_starfield(parent);

            // Nebula clouds for atmosphere
            spawn_nebula_effects(parent);

            // Main title with enhanced effects
            spawn_title_section(parent);

            // Menu buttons with improved styling
            spawn_menu_buttons(parent, &mut menu_state);

            // Footer with version and instructions
            spawn_footer_section(parent);

            // Decorative elements
            spawn_decorative_elements(parent);
        });
}

/// Creates an enhanced starfield with multiple layers and varied animations
fn spawn_enhanced_starfield(parent: &mut ChildSpawnerCommands<'_>) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            ..default()
        },
        MenuStarfield,
        ZIndex(-10),
    ))
    .with_children(|starfield| {
        // Three layers of stars for depth
        for layer in 0..3 {
            let star_count = 50 - (layer * 15);
            let base_size = 1.0 + (layer as f32 * 0.5);
            let speed_multiplier = 1.0 - (layer as f32 * 0.3);

            for i in 0..star_count {
                let x = ((i as f32 * 17.3) + (layer as f32 * 100.0)) % 100.0;
                let y = ((i as f32 * 23.7) + (layer as f32 * 50.0)) % 100.0;
                let size = base_size + (i as f32 * 0.05) % 2.0;
                let opacity = 0.3 + (layer as f32 * 0.2) + (i as f32 * 0.01) % 0.4;

                starfield.spawn((
                    Node {
                        width: Val::Px(size),
                        height: Val::Px(size),
                        position_type: PositionType::Absolute,
                        left: Val::Percent(x),
                        top: Val::Percent(y),
                        ..default()
                    },
                    BackgroundColor(effects::STAR.with_alpha(opacity)),
                    BorderRadius::all(Val::Percent(50.0)),
                    MenuParticle {
                        velocity: Vec2::new(
                            (i as f32 * 0.1) % 0.3 - 0.15,
                            0.05
                        ) * speed_multiplier,
                        lifetime: 10.0 + (i as f32),
                    },
                ));
            }
        }
    });
}

/// Creates nebula cloud effects for atmospheric depth
fn spawn_nebula_effects(parent: &mut ChildSpawnerCommands<'_>) {
    for i in 0..5 {
        let x = 10.0 + (i as f32 * 20.0);
        let y = 10.0 + ((i as f32 * 30.0) % 80.0);
        let size = 200.0 + (i as f32 * 50.0);

        parent.spawn((
            Node {
                width: Val::Px(size),
                height: Val::Px(size),
                position_type: PositionType::Absolute,
                left: Val::Percent(x),
                top: Val::Percent(y),
                ..default()
            },
            BackgroundColor(effects::NEBULA),
            BorderRadius::all(Val::Percent(50.0)),
            ZIndex(-5),
        ));
    }
}

/// Creates the main title section with logo and subtitle
fn spawn_title_section(parent: &mut ChildSpawnerCommands<'_>) {
    parent.spawn((
        Node {
            flex_direction: FlexDirection::Column,
            align_items: AlignItems::Center,
            margin: UiRect::bottom(Val::Px(60.0)),
            ..default()
        },
        MenuTitle,
    ))
    .with_children(|title_parent| {
        // Main title with glow effect layers
        title_parent.spawn((
            Node {
                position_type: PositionType::Relative,
                ..default()
            },
        ))
        .with_children(|title_container| {
            // Glow layer
            title_container.spawn((
                Text::new("RUNETIKA"),
                TextFont {
                    font_size: typography::TITLE_SIZE,
                    ..default()
                },
                TextColor(text::TITLE_GLOW),
                Node {
                    position_type: PositionType::Absolute,
                    ..default()
                },
                Transform::from_xyz(0.0, 0.0, -1.0).with_scale(Vec3::splat(1.02)),
            ));

            // Main text
            title_container.spawn((
                Text::new("RUNETIKA"),
                TextFont {
                    font_size: typography::TITLE_SIZE,
                    ..default()
                },
                TextColor(text::TITLE),
                MenuGlow {
                    intensity: 1.0,
                    speed: animations::GLOW_PULSE_SPEED,
                },
            ));
        });

        // Animated subtitle
        title_parent.spawn((
            Text::new("═══ COSMIC ODYSSEY ═══"),
            TextFont {
                font_size: typography::SUBTITLE_SIZE,
                ..default()
            },
            TextColor(text::SECONDARY),
            Node {
                margin: UiRect::top(Val::Px(10.0)),
                ..default()
            },
        ));

        // Version badge
        title_parent.spawn((
            Text::new("ALPHA v0.1.0"),
            TextFont {
                font_size: typography::VERSION_SIZE,
                ..default()
            },
            TextColor(text::SECONDARY.with_alpha(0.6)),
            Node {
                margin: UiRect::top(Val::Px(5.0)),
                ..default()
            },
        ));
    });
}

/// Creates the menu button section with enhanced interactions
fn spawn_menu_buttons(parent: &mut ChildSpawnerCommands<'_>, menu_state: &mut ResMut<MenuState>) {
    parent.spawn((
        Node {
            flex_direction: FlexDirection::Column,
            align_items: AlignItems::Center,
            row_gap: Val::Px(15.0),
            padding: UiRect::all(Val::Px(20.0)),
            ..default()
        },
    ))
    .with_children(|buttons_parent| {
        let button_configs = vec![
            ("⚡ NEW GAME", MenuAction::StartGame),
            ("💻 TERMINAL", MenuAction::OpenTerminal),
            ("⚙️ SETTINGS", MenuAction::Settings),
            ("👥 CREDITS", MenuAction::Credits),
            ("🚪 EXIT", MenuAction::Exit),
        ];

        for (index, (label, action)) in button_configs.iter().enumerate() {
            let button_entity = spawn_enhanced_button(
                buttons_parent,
                label,
                *action,
                index,
                index == 0,
            );
            menu_state.menu_items.push(button_entity);
        }
    });
}

/// Creates an individual enhanced button with hover effects
fn spawn_enhanced_button(
    parent: &mut ChildSpawnerCommands<'_>,
    label: &str,
    action: MenuAction,
    index: usize,
    is_selected: bool,
) -> Entity {
    let button_color = if is_selected {
        button::SELECTED
    } else {
        button::NORMAL
    };

    parent.spawn((
        Node {
            width: Val::Px(320.0),
            height: Val::Px(65.0),
            justify_content: JustifyContent::Center,
            align_items: AlignItems::Center,
            border: UiRect::all(Val::Px(2.0)),
            padding: UiRect::horizontal(Val::Px(25.0)),
            ..default()
        },
        BackgroundColor(button_color),
        BorderColor(Color::srgba(0.7, 0.4, 0.95, 0.4)),
        BorderRadius::all(Val::Px(10.0)),
        Button,
        MenuButton { index, action },
    ))
    .with_children(|btn| {
        // Selection indicator
        if is_selected {
            btn.spawn((
                Text::new("▸"),
                TextFont {
                    font_size: 24.0,
                    ..default()
                },
                TextColor(text::ACCENT),
                Node {
                    position_type: PositionType::Absolute,
                    left: Val::Px(15.0),
                    ..default()
                },
                SelectedMarker,
            ));
        }

        // Button text
        btn.spawn((
            Text::new(label),
            TextFont {
                font_size: typography::BUTTON_TEXT_SIZE,
                ..default()
            },
            TextColor(text::PRIMARY),
        ));
    }).id()
}

/// Creates the footer section with instructions and credits
fn spawn_footer_section(parent: &mut ChildSpawnerCommands<'_>) {
    parent.spawn((
        Node {
            position_type: PositionType::Absolute,
            bottom: Val::Px(30.0),
            flex_direction: FlexDirection::Column,
            align_items: AlignItems::Center,
            row_gap: Val::Px(5.0),
            ..default()
        },
    ))
    .with_children(|footer| {
        footer.spawn((
            Text::new("Navigate: ↑↓ or Mouse • Select: Enter • Back: ESC"),
            TextFont {
                font_size: typography::FOOTER_SIZE,
                ..default()
            },
            TextColor(text::SECONDARY.with_alpha(0.7)),
        ));

        footer.spawn((
            Text::new("© 2024 Cosmic Studios • Made with Bevy & Rust"),
            TextFont {
                font_size: typography::VERSION_SIZE,
                ..default()
            },
            TextColor(text::SECONDARY.with_alpha(0.5)),
        ));
    });
}

/// Adds decorative elements to enhance visual appeal
fn spawn_decorative_elements(parent: &mut ChildSpawnerCommands<'_>) {
    // Top corner decoration
    parent.spawn((
        Text::new("◆ ◇ ◆"),
        TextFont {
            font_size: 20.0,
            ..default()
        },
        TextColor(text::ACCENT.with_alpha(0.3)),
        Node {
            position_type: PositionType::Absolute,
            top: Val::Px(20.0),
            left: Val::Px(20.0),
            ..default()
        },
    ));

    // Bottom corner decoration
    parent.spawn((
        Text::new("◆ ◇ ◆"),
        TextFont {
            font_size: 20.0,
            ..default()
        },
        TextColor(text::ACCENT.with_alpha(0.3)),
        Node {
            position_type: PositionType::Absolute,
            bottom: Val::Px(20.0),
            right: Val::Px(20.0),
            ..default()
        },
    ));
}

/// Cleans up all menu UI elements when transitioning away from the main menu
pub fn cleanup_main_menu(
    mut commands: Commands,
    menu_query: Query<Entity, With<MainMenu>>,
) {
    for entity in menu_query.iter() {
        commands.entity(entity).despawn();
    }
}
