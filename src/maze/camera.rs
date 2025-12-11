//! Maze-specific camera behavior
//!
//! Provides bounded camera following when the player is in the maze area.

use bevy::prelude::*;
use bevy::render::camera::Projection;
use super::{MazeState, knossos::KnossosMazeConfig};

/// Resource storing camera bounds for the current maze
#[derive(Resource, Default)]
pub struct MazeCameraBounds {
    pub min: Vec2,
    pub max: Vec2,
    pub active: bool,
}

impl MazeCameraBounds {
    /// Calculate bounds based on maze configuration and offset
    pub fn from_config(config: &KnossosMazeConfig, offset: Vec2) -> Self {
        let maze_width = config.width as f32 * config.cell_size;
        let maze_height = config.height as f32 * config.cell_size;

        // Add padding for camera view
        let padding = 200.0;

        Self {
            min: Vec2::new(offset.x - padding, offset.y - maze_height - padding),
            max: Vec2::new(offset.x + maze_width + padding, offset.y + padding),
            active: true,
        }
    }

    /// Clamp a position to within the bounds
    pub fn clamp(&self, pos: Vec2) -> Vec2 {
        Vec2::new(
            pos.x.clamp(self.min.x, self.max.x),
            pos.y.clamp(self.min.y, self.max.y),
        )
    }
}

/// System to handle camera following in maze with bounds
pub fn maze_camera_follow(
    maze_state: Res<MazeState>,
    bounds: Res<MazeCameraBounds>,
    player_query: Query<&Transform, With<crate::main_room::Player>>,
    mut camera_query: Query<&mut Transform, (With<Camera2d>, Without<crate::main_room::Player>)>,
) {
    // Only apply when in maze and bounds are active
    if !maze_state.in_maze || !bounds.active {
        return;
    }

    let Ok(player_transform) = player_query.single() else {
        return;
    };

    let Ok(mut camera_transform) = camera_query.single_mut() else {
        return;
    };

    // Get target position (player position)
    let target = player_transform.translation.truncate();

    // Clamp to maze bounds
    let clamped = bounds.clamp(target);

    // Smooth interpolation to target
    let current = camera_transform.translation.truncate();
    let new_pos = current.lerp(clamped, 0.08);

    camera_transform.translation.x = new_pos.x;
    camera_transform.translation.y = new_pos.y;
}

/// Reset camera bounds when leaving maze
pub fn reset_camera_bounds(
    maze_state: Res<MazeState>,
    mut bounds: ResMut<MazeCameraBounds>,
) {
    if !maze_state.in_maze && bounds.active {
        bounds.active = false;
    }
}

/// Optional: Zoom camera slightly when in maze for tighter view
pub fn maze_camera_zoom(
    maze_state: Res<MazeState>,
    mut camera_query: Query<&mut Projection, With<Camera2d>>,
) {
    let Ok(mut projection) = camera_query.single_mut() else {
        return;
    };

    let target_scale = if maze_state.in_maze { 0.8 } else { 1.0 };

    // Smooth transition - only works with orthographic projection
    if let Projection::Orthographic(ref mut ortho) = *projection {
        ortho.scale = ortho.scale + (target_scale - ortho.scale) * 0.05;
    }
}
