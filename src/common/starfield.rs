//! Shared starfield creation utilities.
//!
//! This module provides reusable starfield and nebula effects for
//! background decoration across different screens.

use bevy::prelude::*;

/// Component for individual stars
#[derive(Component)]
pub struct Star {
    /// Horizontal drift speed
    pub speed: f32,
    /// Base brightness (0.0-1.0)
    pub brightness: f32,
    /// Speed of twinkle animation
    pub twinkle_speed: f32,
    /// Star size in pixels
    pub size: f32,
}

/// Component for animated particles (menu version)
#[derive(Component)]
pub struct Particle {
    /// Velocity in percent per second
    pub velocity: Vec2,
    /// Lifetime in seconds
    pub lifetime: f32,
}

/// Configuration for starfield generation
pub struct StarfieldConfig {
    /// Number of stars to generate
    pub star_count: usize,
    /// Number of parallax layers
    pub layer_count: usize,
    /// Base star color
    pub base_color: Color,
    /// Whether to include nebula clouds
    pub include_nebula: bool,
    /// Number of nebula clouds
    pub nebula_count: usize,
}

impl Default for StarfieldConfig {
    fn default() -> Self {
        Self {
            star_count: 100,
            layer_count: 3,
            base_color: Color::srgba(0.95, 0.9, 1.0, 0.8),
            include_nebula: true,
            nebula_count: 3,
        }
    }
}

impl StarfieldConfig {
    /// Configuration for menu backgrounds
    pub fn menu() -> Self {
        Self {
            star_count: 50,
            layer_count: 3,
            ..Default::default()
        }
    }

    /// Configuration for credits backgrounds
    pub fn credits() -> Self {
        Self {
            star_count: 75,
            layer_count: 1,
            include_nebula: false,
            ..Default::default()
        }
    }

    /// Configuration for terminal backgrounds
    pub fn terminal() -> Self {
        Self {
            star_count: 150,
            layer_count: 1,
            include_nebula: true,
            nebula_count: 3,
            ..Default::default()
        }
    }
}

/// Spawns a starfield with the given configuration.
///
/// # Arguments
/// * `parent` - Parent entity's ChildSpawnerCommands<'_>
/// * `config` - Starfield configuration
pub fn spawn_starfield(parent: &mut ChildSpawnerCommands<'_>, config: &StarfieldConfig) {
    // Create stars based on layer count
    for layer in 0..config.layer_count {
        let stars_per_layer = config.star_count / config.layer_count.max(1);
        let base_size = 1.0 + (layer as f32 * 0.5);
        let speed_multiplier = 1.0 - (layer as f32 * 0.3);

        for i in 0..stars_per_layer {
            let x = ((i as f32 * 17.3) + (layer as f32 * 100.0)) % 100.0;
            let y = ((i as f32 * 23.7) + (layer as f32 * 50.0)) % 100.0;
            let size = base_size + (i as f32 * 0.05) % 2.0;
            let opacity = 0.3 + (layer as f32 * 0.2) + (i as f32 * 0.01) % 0.4;

            parent.spawn((
                Node {
                    width: Val::Px(size),
                    height: Val::Px(size),
                    position_type: PositionType::Absolute,
                    left: Val::Percent(x),
                    top: Val::Percent(y),
                    ..default()
                },
                BackgroundColor(config.base_color.with_alpha(opacity)),
                BorderRadius::all(Val::Percent(50.0)),
                Particle {
                    velocity: Vec2::new(
                        (i as f32 * 0.1) % 0.3 - 0.15,
                        0.05,
                    ) * speed_multiplier,
                    lifetime: 10.0 + (i as f32),
                },
            ));
        }
    }
}

/// Spawns nebula cloud effects for atmospheric depth.
///
/// # Arguments
/// * `parent` - Parent entity's ChildSpawnerCommands<'_>
/// * `count` - Number of nebula clouds to spawn
pub fn spawn_nebula_clouds(parent: &mut ChildSpawnerCommands<'_>, count: usize) {
    let nebula_color = Color::srgba(0.6, 0.2, 0.9, 0.03);

    for i in 0..count {
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
            BackgroundColor(nebula_color),
            BorderRadius::all(Val::Percent(50.0)),
            ZIndex(-5),
        ));
    }
}

/// Spawns a complete starfield container with optional nebula effects.
///
/// # Arguments
/// * `parent` - Parent entity's ChildSpawnerCommands<'_>
/// * `config` - Starfield configuration
/// * `z_index` - Z-index for the container
pub fn spawn_starfield_container(
    parent: &mut ChildSpawnerCommands<'_>,
    config: &StarfieldConfig,
    z_index: i32,
) {
    parent.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            ..default()
        },
        ZIndex(z_index),
    ))
    .with_children(|starfield| {
        spawn_starfield(starfield, config);

        if config.include_nebula {
            spawn_nebula_clouds(starfield, config.nebula_count);
        }
    });
}

/// Animates particles by drifting them and handling wrap-around.
pub fn animate_particles(
    time: Res<Time>,
    mut particle_query: Query<(&mut Node, &Particle)>,
) {
    for (mut node, particle) in particle_query.iter_mut() {
        if let Val::Percent(mut x) = node.left {
            x += particle.velocity.x * time.delta_secs() * 10.0;
            if x > 100.0 {
                x = -2.0;
            } else if x < -2.0 {
                x = 100.0;
            }
            node.left = Val::Percent(x);
        }

        if let Val::Percent(mut y) = node.top {
            y += particle.velocity.y * time.delta_secs() * 10.0;
            if y > 100.0 {
                y = -2.0;
            }
            node.top = Val::Percent(y);
        }
    }
}
