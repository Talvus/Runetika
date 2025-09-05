//! UI components and layout for the credits screen.

use bevy::prelude::*;
// Commands is now in bevy::prelude
use super::{CreditsScreen, CreditsContent, CreditEntry, CreditsState};

/// Color scheme for credits screen
pub mod colors {
    use bevy::prelude::Color;
    
    pub const BACKGROUND: Color = Color::srgba(0.02, 0.0, 0.06, 0.98);
    pub const TITLE: Color = Color::srgb(0.9, 0.7, 1.0);
    pub const ROLE: Color = Color::srgb(0.7, 0.5, 0.9);
    pub const NAME: Color = Color::srgb(0.95, 0.9, 1.0);
    pub const SECTION: Color = Color::srgb(0.6, 0.8, 1.0);
    pub const TEXT: Color = Color::srgb(0.85, 0.8, 0.9);
}

/// Sets up the credits screen UI
pub fn setup_credits_screen(
    mut commands: Commands,
    mut credits_state: ResMut<CreditsState>,
) {
    credits_state.scroll_position = 0.0;
    credits_state.is_auto_scrolling = true;
    
    // Main container
    commands.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            flex_direction: FlexDirection::Column,
            align_items: AlignItems::Center,
            ..default()
        },
        BackgroundColor(colors::BACKGROUND),
        CreditsScreen,
    ))
    .with_children(|parent| {
        // Starfield background (reuse from menu)
        spawn_credits_starfield(parent);
        
        // Header
        parent.spawn((
            Node {
                width: Val::Percent(100.0),
                height: Val::Px(100.0),
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                border: UiRect::bottom(Val::Px(2.0)),
                ..default()
            },
            BorderColor(Color::srgba(0.6, 0.3, 0.9, 0.5)),
            ZIndex(10),
        ))
        .with_children(|header| {
            header.spawn((
                Text::new("CREDITS"),
                TextFont {
                    font_size: 48.0,
                    ..default()
                },
                TextColor(colors::TITLE),
            ));
        });
        
        // Scrollable content area
        parent.spawn((
            Node {
                width: Val::Percent(100.0),
                flex_grow: 1.0,
                overflow: Overflow::clip(),
                padding: UiRect::all(Val::Px(50.0)),
                ..default()
            },
        ))
        .with_children(|scroll_parent| {
            scroll_parent.spawn((
                Node {
                    flex_direction: FlexDirection::Column,
                    align_items: AlignItems::Center,
                    row_gap: Val::Px(40.0),
                    ..default()
                },
                CreditsContent,
            ))
            .with_children(|content| {
                let mut delay = 0.0;
                
                // Game title
                spawn_credit_section(content, "RUNETIKA", "A Cosmic Odyssey", delay);
                delay += 0.5;
                
                // Development Team
                spawn_credit_title(content, "═══ DEVELOPMENT TEAM ═══", delay);
                delay += 0.3;
                
                spawn_credit_entry(content, "Game Design & Direction", "Your Name Here", delay);
                delay += 0.2;
                
                spawn_credit_entry(content, "Lead Programming", "Rust Enthusiast", delay);
                delay += 0.2;
                
                spawn_credit_entry(content, "Terminal Systems", "CLI Wizard", delay);
                delay += 0.2;
                
                spawn_credit_entry(content, "UI/UX Design", "Interface Artist", delay);
                delay += 0.2;
                
                // Special Thanks
                spawn_credit_title(content, "═══ SPECIAL THANKS ═══", delay);
                delay += 0.3;
                
                spawn_credit_text(content, "The Bevy Community", delay);
                delay += 0.2;
                
                spawn_credit_text(content, "Rust Programming Language Team", delay);
                delay += 0.2;
                
                spawn_credit_text(content, "All Our Early Testers", delay);
                delay += 0.2;
                
                // Technologies
                spawn_credit_title(content, "═══ POWERED BY ═══", delay);
                delay += 0.3;
                
                spawn_technology_credit(content, "Bevy Engine", "v0.16", delay);
                delay += 0.2;
                
                spawn_technology_credit(content, "Rust", "2024 Edition", delay);
                delay += 0.2;
                
                spawn_technology_credit(content, "Avian2D", "Physics Engine", delay);
                delay += 0.2;
                
                // Music & Sound (placeholder)
                spawn_credit_title(content, "═══ AUDIO ═══", delay);
                delay += 0.3;
                
                spawn_credit_entry(content, "Music Composition", "Space Composer", delay);
                delay += 0.2;
                
                spawn_credit_entry(content, "Sound Effects", "Audio Engineer", delay);
                delay += 0.2;
                
                // Legal
                spawn_credit_title(content, "═══ LEGAL ═══", delay);
                delay += 0.3;
                
                spawn_credit_text(content, "© 2024 Cosmic Studios", delay);
                delay += 0.2;
                
                spawn_credit_text(content, "All Rights Reserved", delay);
                delay += 0.2;
                
                spawn_credit_text(content, "Made with ❤️ and Rust", delay);
                delay += 0.5;
                
                // End message
                spawn_credit_title(content, "Thank You for Playing!", delay);
            });
        });
        
        // Footer with back button hint
        parent.spawn((
            Node {
                position_type: PositionType::Absolute,
                bottom: Val::Px(20.0),
                width: Val::Percent(100.0),
                justify_content: JustifyContent::Center,
                ..default()
            },
            ZIndex(10),
        ))
        .with_children(|footer| {
            footer.spawn((
                Text::new("Press ESC to return to menu • SPACE to pause scrolling"),
                TextFont {
                    font_size: 16.0,
                    ..default()
                },
                TextColor(Color::srgba(0.7, 0.6, 0.8, 0.7)),
            ));
        });
    });
}

/// Spawns a section title in the credits
fn spawn_credit_title(parent: &mut _, text: &str, delay: f32) {
    parent.spawn((
        Text::new(text),
        TextFont {
            font_size: 32.0,
            ..default()
        },
        TextColor(colors::SECTION),
        Node {
            margin: UiRect::vertical(Val::Px(20.0)),
            ..default()
        },
        CreditEntry {
            delay,
            animation_timer: 0.0,
        },
    ));
}

/// Spawns a credit entry with role and name
fn spawn_credit_entry(parent: &mut _, role: &str, name: &str, delay: f32) {
    parent.spawn((
        Node {
            flex_direction: FlexDirection::Column,
            align_items: AlignItems::Center,
            row_gap: Val::Px(5.0),
            ..default()
        },
        CreditEntry {
            delay,
            animation_timer: 0.0,
        },
    ))
    .with_children(|entry| {
        entry.spawn((
            Text::new(role),
            TextFont {
                font_size: 18.0,
                ..default()
            },
            TextColor(colors::ROLE),
        ));
        
        entry.spawn((
            Text::new(name),
            TextFont {
                font_size: 24.0,
                ..default()
            },
            TextColor(colors::NAME),
        ));
    });
}

/// Spawns a simple text credit
fn spawn_credit_text(parent: &mut _, text: &str, delay: f32) {
    parent.spawn((
        Text::new(text),
        TextFont {
            font_size: 20.0,
            ..default()
        },
        TextColor(colors::TEXT),
        CreditEntry {
            delay,
            animation_timer: 0.0,
        },
    ));
}

/// Spawns a technology credit
fn spawn_technology_credit(parent: &mut _, tech: &str, version: &str, delay: f32) {
    parent.spawn((
        Node {
            flex_direction: FlexDirection::Row,
            column_gap: Val::Px(10.0),
            ..default()
        },
        CreditEntry {
            delay,
            animation_timer: 0.0,
        },
    ))
    .with_children(|tech_entry| {
        tech_entry.spawn((
            Text::new(tech),
            TextFont {
                font_size: 22.0,
                ..default()
            },
            TextColor(colors::NAME),
        ));
        
        tech_entry.spawn((
            Text::new(format!("• {}", version)),
            TextFont {
                font_size: 18.0,
                ..default()
            },
            TextColor(colors::ROLE),
        ));
    });
}

/// Spawns the main game title section
fn spawn_credit_section(parent: &mut _, title: &str, subtitle: &str, delay: f32) {
    parent.spawn((
        Node {
            flex_direction: FlexDirection::Column,
            align_items: AlignItems::Center,
            margin: UiRect::bottom(Val::Px(40.0)),
            ..default()
        },
        CreditEntry {
            delay,
            animation_timer: 0.0,
        },
    ))
    .with_children(|section| {
        section.spawn((
            Text::new(title),
            TextFont {
                font_size: 64.0,
                ..default()
            },
            TextColor(colors::TITLE),
        ));
        
        section.spawn((
            Text::new(subtitle),
            TextFont {
                font_size: 24.0,
                ..default()
            },
            TextColor(colors::ROLE),
        ));
    });
}

/// Creates animated starfield background for credits
fn spawn_credits_starfield(parent: &mut _) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            ..default()
        },
        ZIndex(-10),
    ))
    .with_children(|starfield| {
        for i in 0..75 {
            let x = (i as f32 * 13.7) % 100.0;
            let y = (i as f32 * 17.3) % 100.0;
            let size = 1.0 + (i as f32 * 0.03) % 2.0;
            
            starfield.spawn((
                Node {
                    width: Val::Px(size),
                    height: Val::Px(size),
                    position_type: PositionType::Absolute,
                    left: Val::Percent(x),
                    top: Val::Percent(y),
                    ..default()
                },
                BackgroundColor(Color::srgba(0.9, 0.85, 1.0, 0.6)),
                BorderRadius::all(Val::Percent(50.0)),
            ));
        }
    });
}

/// Cleanup function for credits screen
pub fn cleanup_credits_screen(
    mut commands: Commands,
    credits_query: Query<Entity, With<CreditsScreen>>,
) {
    for entity in credits_query.iter() {
        commands.entity(entity).despawn();
    }
}