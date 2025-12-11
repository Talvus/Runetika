//! Portal effects for maze entrance and exit
//!
//! Provides animated visual indicators for maze entry points and goals.

use bevy::prelude::*;
use super::MazeEntity;

/// Component marking a portal entity
#[derive(Component)]
pub struct MazePortal {
    pub portal_type: PortalType,
    pub animation_phase: f32,
}

/// Type of portal - entrance or exit
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PortalType {
    /// Green portal at maze entrance
    Entrance,
    /// Golden portal at maze exit/goal
    Exit,
}

impl MazePortal {
    pub fn entrance() -> Self {
        Self {
            portal_type: PortalType::Entrance,
            animation_phase: 0.0,
        }
    }

    pub fn exit() -> Self {
        Self {
            portal_type: PortalType::Exit,
            animation_phase: 0.0,
        }
    }
}

/// Spawn an entrance portal at the specified position
pub fn spawn_entrance_portal(commands: &mut Commands, position: Vec2, size: f32) {
    // Main portal glow
    commands.spawn((
        MazeEntity,
        MazePortal::entrance(),
        Sprite {
            color: Color::srgba(0.3, 0.8, 0.3, 0.5),
            custom_size: Some(Vec2::splat(size)),
            ..default()
        },
        Transform::from_xyz(position.x, position.y, -7.0),
    ));

    // Inner portal core
    commands.spawn((
        MazeEntity,
        MazePortal::entrance(),
        Sprite {
            color: Color::srgba(0.5, 1.0, 0.5, 0.8),
            custom_size: Some(Vec2::splat(size * 0.6)),
            ..default()
        },
        Transform::from_xyz(position.x, position.y, -6.5),
    ));

    // Portal particles (stationary decorative elements)
    for i in 0..6 {
        let angle = (i as f32 / 6.0) * std::f32::consts::TAU;
        let offset = Vec2::from_angle(angle) * (size * 0.4);
        commands.spawn((
            MazeEntity,
            PortalParticle {
                base_position: position,
                orbit_radius: size * 0.4,
                orbit_speed: 1.5,
                orbit_offset: angle,
            },
            Sprite {
                color: Color::srgba(0.4, 1.0, 0.4, 0.6),
                custom_size: Some(Vec2::splat(size * 0.1)),
                ..default()
            },
            Transform::from_xyz(position.x + offset.x, position.y + offset.y, -6.0),
        ));
    }
}

/// Spawn an exit portal (goal) at the specified position
pub fn spawn_exit_portal(commands: &mut Commands, position: Vec2, size: f32) {
    // Main portal glow - golden
    commands.spawn((
        MazeEntity,
        MazePortal::exit(),
        Sprite {
            color: Color::srgba(0.9, 0.7, 0.2, 0.5),
            custom_size: Some(Vec2::splat(size)),
            ..default()
        },
        Transform::from_xyz(position.x, position.y, -7.0),
    ));

    // Inner portal core
    commands.spawn((
        MazeEntity,
        MazePortal::exit(),
        Sprite {
            color: Color::srgba(1.0, 0.85, 0.4, 0.9),
            custom_size: Some(Vec2::splat(size * 0.6)),
            ..default()
        },
        Transform::from_xyz(position.x, position.y, -6.5),
    ));

    // Portal particles
    for i in 0..8 {
        let angle = (i as f32 / 8.0) * std::f32::consts::TAU;
        let offset = Vec2::from_angle(angle) * (size * 0.5);
        commands.spawn((
            MazeEntity,
            PortalParticle {
                base_position: position,
                orbit_radius: size * 0.5,
                orbit_speed: 2.0,
                orbit_offset: angle,
            },
            Sprite {
                color: Color::srgba(1.0, 0.9, 0.5, 0.7),
                custom_size: Some(Vec2::splat(size * 0.08)),
                ..default()
            },
            Transform::from_xyz(position.x + offset.x, position.y + offset.y, -6.0),
        ));
    }
}

/// Component for orbiting portal particles
#[derive(Component)]
pub struct PortalParticle {
    pub base_position: Vec2,
    pub orbit_radius: f32,
    pub orbit_speed: f32,
    pub orbit_offset: f32,
}

/// System to animate portal pulse effects
pub fn animate_portals(
    time: Res<Time>,
    mut portal_query: Query<(&mut Sprite, &MazePortal)>,
) {
    for (mut sprite, portal) in portal_query.iter_mut() {
        // Pulsing alpha effect
        let pulse = (time.elapsed_secs() * 3.0).sin() * 0.2 + 0.6;
        let color = match portal.portal_type {
            PortalType::Entrance => Color::srgba(0.3, 0.8, 0.3, pulse),
            PortalType::Exit => Color::srgba(0.9, 0.7, 0.2, pulse),
        };
        sprite.color = color;
    }
}

/// System to animate orbiting particles around portals
pub fn animate_portal_particles(
    time: Res<Time>,
    mut particle_query: Query<(&mut Transform, &PortalParticle)>,
) {
    for (mut transform, particle) in particle_query.iter_mut() {
        let angle = particle.orbit_offset + time.elapsed_secs() * particle.orbit_speed;
        let offset = Vec2::from_angle(angle) * particle.orbit_radius;
        transform.translation.x = particle.base_position.x + offset.x;
        transform.translation.y = particle.base_position.y + offset.y;
    }
}
