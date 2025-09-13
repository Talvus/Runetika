/// UI components for the Papilio credit system
/// 
/// Handles visual display of credits, notifications, and statistics.

use bevy::prelude::*;
use crate::papilio::{PapilioCredits, CreditNotificationEvent, NotificationType};

/// Marker component for credit display UI
#[derive(Component)]
pub struct CreditDisplay;

/// Marker component for credit notifications
#[derive(Component)]
pub struct CreditNotification {
    pub lifetime: f32,
    pub fade_time: f32,
}

/// Marker component for credit statistics panel
#[derive(Component)]
pub struct CreditStatsPanel;

/// Setup credit display UI
pub fn setup_credit_ui(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
) {
    // Main credit display (top-right corner)
    commands
        .spawn(NodeBundle {
            style: Style {
                position_type: PositionType::Absolute,
                top: Val::Px(20.0),
                right: Val::Px(20.0),
                padding: UiRect::all(Val::Px(10.0)),
                ..default()
            },
            background_color: BackgroundColor(Color::rgba(0.1, 0.1, 0.2, 0.9)),
            ..default()
        })
        .with_children(|parent| {
            // Credit icon
            parent.spawn(ImageBundle {
                style: Style {
                    width: Val::Px(24.0),
                    height: Val::Px(24.0),
                    margin: UiRect::right(Val::Px(8.0)),
                    ..default()
                },
                image: UiImage::new(asset_server.load("icons/papilio_credit.png")),
                ..default()
            });
            
            // Credit text
            parent.spawn((
                TextBundle::from_section(
                    "0 Papilio Credits",
                    TextStyle {
                        font: asset_server.load("fonts/space_mono.ttf"),
                        font_size: 20.0,
                        color: Color::rgb(0.9, 0.8, 0.3),
                    },
                ),
                CreditDisplay,
            ));
        });
}

/// Spawn a credit notification
pub fn spawn_credit_notification(
    commands: &mut Commands,
    asset_server: &AssetServer,
    event: CreditNotificationEvent,
) {
    let (bg_color, text_color) = match event.notification_type {
        NotificationType::Earned => (Color::rgba(0.1, 0.3, 0.1, 0.95), Color::rgb(0.3, 0.9, 0.3)),
        NotificationType::Milestone => (Color::rgba(0.3, 0.2, 0.1, 0.95), Color::rgb(0.9, 0.8, 0.3)),
        NotificationType::Bonus => (Color::rgba(0.2, 0.1, 0.3, 0.95), Color::rgb(0.8, 0.3, 0.9)),
        NotificationType::Sync => (Color::rgba(0.1, 0.2, 0.3, 0.95), Color::rgb(0.3, 0.7, 0.9)),
    };
    
    commands
        .spawn((
            NodeBundle {
                style: Style {
                    position_type: PositionType::Absolute,
                    top: Val::Px(100.0),
                    right: Val::Px(20.0),
                    padding: UiRect::all(Val::Px(15.0)),
                    border: UiRect::all(Val::Px(2.0)),
                    ..default()
                },
                background_color: BackgroundColor(bg_color),
                ..default()
            },
            CreditNotification {
                lifetime: 5.0,
                fade_time: 1.0,
            },
        ))
        .with_children(|parent| {
            // Title
            parent.spawn(TextBundle::from_section(
                event.title,
                TextStyle {
                    font: asset_server.load("fonts/space_mono_bold.ttf"),
                    font_size: 18.0,
                    color: text_color,
                },
            ));
            
            // Message
            parent.spawn(TextBundle::from_section(
                event.message,
                TextStyle {
                    font: asset_server.load("fonts/space_mono.ttf"),
                    font_size: 14.0,
                    color: Color::rgb(0.8, 0.8, 0.8),
                },
            ).with_style(Style {
                margin: UiRect::top(Val::Px(5.0)),
                ..default()
            }));
            
            // Credit amount (if significant)
            if event.credit_amount > 0 {
                parent.spawn(TextBundle::from_section(
                    format!("+{} Credits", event.credit_amount),
                    TextStyle {
                        font: asset_server.load("fonts/space_mono_bold.ttf"),
                        font_size: 22.0,
                        color: Color::rgb(0.9, 0.8, 0.3),
                    },
                ).with_style(Style {
                    margin: UiRect::top(Val::Px(10.0)),
                    ..default()
                }));
            }
        });
}

/// Update notification lifetimes and fade them out
pub fn update_credit_notifications(
    mut commands: Commands,
    time: Res<Time>,
    mut query: Query<(Entity, &mut CreditNotification, &mut BackgroundColor, &Children)>,
    mut text_query: Query<&mut Text>,
) {
    for (entity, mut notification, mut bg_color, children) in &mut query {
        notification.lifetime -= time.delta_seconds();
        
        if notification.lifetime <= 0.0 {
            // Remove expired notifications
            commands.entity(entity).despawn_recursive();
        } else if notification.lifetime < notification.fade_time {
            // Fade out
            let alpha = notification.lifetime / notification.fade_time;
            bg_color.0.set_a(bg_color.0.a() * alpha);
            
            // Fade text as well
            for child in children {
                if let Ok(mut text) = text_query.get_mut(*child) {
                    for section in &mut text.sections {
                        section.style.color.set_a(section.style.color.a() * alpha);
                    }
                }
            }
        }
    }
}

/// Create credit statistics panel
pub fn create_stats_panel(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
    credits: Res<PapilioCredits>,
) {
    let stats = credits.statistics();
    
    commands
        .spawn((
            NodeBundle {
                style: Style {
                    position_type: PositionType::Absolute,
                    width: Val::Px(300.0),
                    top: Val::Px(100.0),
                    right: Val::Px(20.0),
                    padding: UiRect::all(Val::Px(20.0)),
                    flex_direction: FlexDirection::Column,
                    ..default()
                },
                background_color: BackgroundColor(Color::rgba(0.1, 0.1, 0.2, 0.95)),
                ..default()
            },
            CreditStatsPanel,
        ))
        .with_children(|parent| {
            // Title
            parent.spawn(TextBundle::from_section(
                "Credit Statistics",
                TextStyle {
                    font: asset_server.load("fonts/space_mono_bold.ttf"),
                    font_size: 22.0,
                    color: Color::rgb(0.9, 0.8, 0.3),
                },
            ));
            
            // Stats entries
            spawn_stat_row(parent, &asset_server, "Total Balance", &credits.total_balance().to_string());
            spawn_stat_row(parent, &asset_server, "Lifetime Earned", &credits.lifetime_earnings().to_string());
            spawn_stat_row(parent, &asset_server, "Puzzles Solved", &stats.puzzles_solved.to_string());
            spawn_stat_row(parent, &asset_server, "Perfect Solves", &stats.perfect_solves.to_string());
            spawn_stat_row(parent, &asset_server, "Current Streak", &format!("{} days", stats.current_streak));
            spawn_stat_row(parent, &asset_server, "Best Streak", &format!("{} days", stats.best_streak));
            spawn_stat_row(parent, &asset_server, "Avg Puzzle Reward", &format!("{:.1}", stats.average_puzzle_reward));
            spawn_stat_row(parent, &asset_server, "Highest Reward", &stats.highest_single_reward.to_string());
        });
}

/// Helper to spawn a stat row
fn spawn_stat_row(
    parent: &mut ChildBuilder,
    asset_server: &AssetServer,
    label: &str,
    value: &str,
) {
    parent
        .spawn(NodeBundle {
            style: Style {
                width: Val::Percent(100.0),
                justify_content: JustifyContent::SpaceBetween,
                margin: UiRect::top(Val::Px(10.0)),
                ..default()
            },
            ..default()
        })
        .with_children(|row| {
            // Label
            row.spawn(TextBundle::from_section(
                label,
                TextStyle {
                    font: asset_server.load("fonts/space_mono.ttf"),
                    font_size: 14.0,
                    color: Color::rgb(0.6, 0.6, 0.7),
                },
            ));
            
            // Value
            row.spawn(TextBundle::from_section(
                value,
                TextStyle {
                    font: asset_server.load("fonts/space_mono_bold.ttf"),
                    font_size: 14.0,
                    color: Color::rgb(0.9, 0.9, 0.9),
                },
            ));
        });
}

/// Create a credit reward animation
pub fn spawn_reward_animation(
    commands: &mut Commands,
    position: Vec2,
    amount: u64,
    asset_server: &AssetServer,
) {
    // Spawn floating text that rises and fades
    commands.spawn((
        Text2dBundle {
            text: Text::from_section(
                format!("+{}", amount),
                TextStyle {
                    font: asset_server.load("fonts/space_mono_bold.ttf"),
                    font_size: 32.0,
                    color: Color::rgb(0.9, 0.8, 0.3),
                },
            ),
            transform: Transform::from_xyz(position.x, position.y, 100.0),
            ..default()
        },
        RewardAnimation {
            velocity: Vec2::new(0.0, 50.0),
            lifetime: 2.0,
            fade_start: 1.0,
        },
    ));
    
    // Spawn particle burst
    for i in 0..10 {
        let angle = (i as f32 / 10.0) * std::f32::consts::TAU;
        let velocity = Vec2::new(angle.cos(), angle.sin()) * 100.0;
        
        commands.spawn((
            SpriteBundle {
                sprite: Sprite {
                    color: Color::rgb(0.9, 0.8, 0.3),
                    custom_size: Some(Vec2::splat(4.0)),
                    ..default()
                },
                transform: Transform::from_xyz(position.x, position.y, 99.0),
                ..default()
            },
            CreditParticle {
                velocity,
                lifetime: 1.0,
                size: 4.0,
            },
        ));
    }
}

/// Component for reward animation
#[derive(Component)]
struct RewardAnimation {
    velocity: Vec2,
    lifetime: f32,
    fade_start: f32,
}

/// Component for credit particles
#[derive(Component)]
struct CreditParticle {
    velocity: Vec2,
    lifetime: f32,
    size: f32,
}

/// Update reward animations
pub fn update_reward_animations(
    mut commands: Commands,
    time: Res<Time>,
    mut query: Query<(Entity, &mut Transform, &mut Text, &mut RewardAnimation)>,
) {
    for (entity, mut transform, mut text, mut animation) in &mut query {
        animation.lifetime -= time.delta_seconds();
        
        if animation.lifetime <= 0.0 {
            commands.entity(entity).despawn();
        } else {
            // Move upward
            transform.translation.x += animation.velocity.x * time.delta_seconds();
            transform.translation.y += animation.velocity.y * time.delta_seconds();
            
            // Fade out
            if animation.lifetime < animation.fade_start {
                let alpha = animation.lifetime / animation.fade_start;
                for section in &mut text.sections {
                    section.style.color.set_a(alpha);
                }
            }
        }
    }
}

/// Update credit particles
pub fn update_credit_particles(
    mut commands: Commands,
    time: Res<Time>,
    mut query: Query<(Entity, &mut Transform, &mut Sprite, &mut CreditParticle)>,
) {
    for (entity, mut transform, mut sprite, mut particle) in &mut query {
        particle.lifetime -= time.delta_seconds();
        
        if particle.lifetime <= 0.0 {
            commands.entity(entity).despawn();
        } else {
            // Move with velocity
            transform.translation.x += particle.velocity.x * time.delta_seconds();
            transform.translation.y += particle.velocity.y * time.delta_seconds();
            
            // Apply gravity
            particle.velocity.y -= 200.0 * time.delta_seconds();
            
            // Shrink and fade
            let progress = particle.lifetime;
            sprite.custom_size = Some(Vec2::splat(particle.size * progress));
            sprite.color.set_a(progress);
        }
    }
}