//! Isometric Renderer for Knossos Mazes
//!
//! Bridges bevy_knossos maze generation with WFC-style isometric 2.5D rendering.
//! Converts maze cells (passages) to visual tile variants for the Silicon Mind aesthetic.

use bevy::prelude::*;
use bevy_knossos::maze::{OrthogonalMaze, Cell};
use avian2d::prelude::*;
use crate::procedural::wfc::tiles::{TileVariant, MazeTheme};
use crate::procedural::wfc::renderer::{isometric_to_world, TILE_WIDTH, TILE_HEIGHT};
use super::{MazeEntity, MazeGoal, knossos::KnossosMazeConfig};

/// Component: Isometric tile sprite for Knossos maze
#[derive(Component)]
pub struct KnossosTileSprite {
    #[allow(dead_code)]
    pub grid_x: i32,
    #[allow(dead_code)]
    pub grid_y: i32,
    #[allow(dead_code)]
    pub variant: TileVariant,
}

/// Component: Wall sprite in isometric view
#[derive(Component)]
pub struct KnossosWallSprite {
    #[allow(dead_code)]
    pub grid_x: i32,
    #[allow(dead_code)]
    pub grid_y: i32,
    #[allow(dead_code)]
    pub direction: WallDirection,
}

#[derive(Clone, Copy, Debug)]
pub enum WallDirection {
    North,
    South,
    East,
    West,
}

/// Configuration for isometric rendering
#[derive(Resource, Clone)]
pub struct IsometricRenderConfig {
    pub enabled: bool,
    pub theme: MazeTheme,
    pub wall_height: f32,
    pub show_floors: bool,
    pub show_walls: bool,
}

impl Default for IsometricRenderConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            theme: MazeTheme::CircuitBoard,
            wall_height: 24.0,
            show_floors: true,
            show_walls: true,
        }
    }
}

/// Convert Knossos Cell passages to WFC TileVariant
///
/// # Algorithm
/// Cell bitflags indicate PASSAGES (open directions).
/// We count open directions and their configuration to determine tile type:
/// - 0 passages: Isolated (treated as Empty)
/// - 1 passage: Dead end
/// - 2 passages: Straight or Corner depending on configuration
/// - 3 passages: T-Junction
/// - 4 passages: Cross
pub fn cell_to_tile_variant(cell: &Cell) -> TileVariant {
    let north = cell.contains(Cell::NORTH);
    let south = cell.contains(Cell::SOUTH);
    let east = cell.contains(Cell::EAST);
    let west = cell.contains(Cell::WEST);

    let count = (north as u8) + (south as u8) + (east as u8) + (west as u8);

    match count {
        0 => TileVariant::Empty,
        1 => TileVariant::Straight, // Dead end - render as stub
        2 => {
            // Check if opposite directions (straight) or adjacent (corner)
            if (north && south) || (east && west) {
                TileVariant::Straight
            } else {
                TileVariant::Corner
            }
        }
        3 => TileVariant::TJunction,
        4 => TileVariant::Cross,
        _ => TileVariant::Empty,
    }
}

/// Spawn isometric tiles for a Knossos maze
pub fn spawn_isometric_knossos_maze(
    commands: &mut Commands,
    maze: &OrthogonalMaze,
    config: &KnossosMazeConfig,
    render_config: &IsometricRenderConfig,
    offset: Vec2,
) {
    if !render_config.enabled {
        return;
    }

    // Iterate through maze cells
    for (coords, cell) in maze.iter() {
        let grid_x = coords.0 as i32;
        let grid_y = coords.1 as i32;

        // Convert to isometric world position
        let world_pos = isometric_to_world(
            grid_x as f32 + offset.x / config.cell_size,
            grid_y as f32 + offset.y / config.cell_size,
        );

        // Z-depth for proper layering (further back = lower Z)
        let z_depth = -100.0 - (grid_y as f32);

        // Get tile variant from cell passages
        let variant = cell_to_tile_variant(cell);
        let color = get_isometric_tile_color(variant, render_config.theme);

        // Spawn floor tile
        if render_config.show_floors {
            commands.spawn((
                MazeEntity,
                KnossosTileSprite {
                    grid_x,
                    grid_y,
                    variant,
                },
                Sprite {
                    color,
                    custom_size: Some(Vec2::new(TILE_WIDTH, TILE_HEIGHT)),
                    ..default()
                },
                Transform::from_translation(Vec3::new(
                    world_pos.x,
                    world_pos.y,
                    z_depth,
                )),
            ));
        }

        // Spawn walls for missing passages, using the same canonical-owner
        // rule as the flat path (knossos.rs::spawn_knossos_maze_entities)
        // to keep each interior edge a single sprite + collider.
        if render_config.show_walls {
            if !cell.contains(Cell::SOUTH) {
                spawn_isometric_wall(commands, grid_x, grid_y, WallDirection::South, world_pos, z_depth, render_config);
            }
            if !cell.contains(Cell::EAST) {
                spawn_isometric_wall(commands, grid_x, grid_y, WallDirection::East, world_pos, z_depth, render_config);
            }
            if grid_y == 0 && !cell.contains(Cell::NORTH) {
                spawn_isometric_wall(commands, grid_x, grid_y, WallDirection::North, world_pos, z_depth, render_config);
            }
            if grid_x == 0 && !cell.contains(Cell::WEST) {
                spawn_isometric_wall(commands, grid_x, grid_y, WallDirection::West, world_pos, z_depth, render_config);
            }
        }
    }

    // Spawn goal at bottom-right corner so the maze is completable in
    // isometric mode (the flat path already does this in knossos::spawn_goal)
    let goal_grid_x = (config.width.saturating_sub(2)) as f32;
    let goal_grid_y = (config.height.saturating_sub(2)) as f32;
    let goal_world = isometric_to_world(
        goal_grid_x + offset.x / config.cell_size,
        goal_grid_y + offset.y / config.cell_size,
    );
    commands.spawn((
        MazeEntity,
        MazeGoal,
        Sprite {
            color: Color::srgba(0.3, 1.0, 0.3, 0.85),
            custom_size: Some(Vec2::new(TILE_WIDTH * 0.6, TILE_HEIGHT * 0.6)),
            ..default()
        },
        Transform::from_translation(Vec3::new(goal_world.x, goal_world.y, -8.0)),
    ));

    info!(
        "Spawned isometric maze {}x{} with theme {:?}",
        config.width, config.height, render_config.theme
    );
}

/// Spawn a single isometric wall segment
fn spawn_isometric_wall(
    commands: &mut Commands,
    grid_x: i32,
    grid_y: i32,
    direction: WallDirection,
    tile_pos: Vec2,
    base_z: f32,
    config: &IsometricRenderConfig,
) {
    // Calculate wall offset based on direction (in isometric space)
    let (offset, size, wall_z) = match direction {
        WallDirection::North => (
            Vec2::new(TILE_WIDTH * 0.25, TILE_HEIGHT * 0.5),
            Vec2::new(TILE_WIDTH * 0.5 + 4.0, config.wall_height),
            base_z + 0.5,
        ),
        WallDirection::South => (
            Vec2::new(-TILE_WIDTH * 0.25, -TILE_HEIGHT * 0.5),
            Vec2::new(TILE_WIDTH * 0.5 + 4.0, config.wall_height),
            base_z + 0.5,
        ),
        WallDirection::East => (
            Vec2::new(TILE_WIDTH * 0.25, -TILE_HEIGHT * 0.25),
            Vec2::new(TILE_WIDTH * 0.5 + 4.0, config.wall_height),
            base_z + 0.3,
        ),
        WallDirection::West => (
            Vec2::new(-TILE_WIDTH * 0.25, TILE_HEIGHT * 0.25),
            Vec2::new(TILE_WIDTH * 0.5 + 4.0, config.wall_height),
            base_z + 0.3,
        ),
    };

    let wall_pos = tile_pos + offset + Vec2::new(0.0, config.wall_height * 0.5);
    let wall_color = get_wall_color(config.theme);

    commands.spawn((
        MazeEntity,
        KnossosWallSprite {
            grid_x,
            grid_y,
            direction,
        },
        Sprite {
            color: wall_color,
            custom_size: Some(size),
            ..default()
        },
        Transform::from_translation(Vec3::new(
            wall_pos.x,
            wall_pos.y,
            wall_z,
        )),
        RigidBody::Static,
        Collider::rectangle(size.x, size.y),
    ));
}

/// Get floor tile color based on variant and theme
fn get_isometric_tile_color(variant: TileVariant, theme: MazeTheme) -> Color {
    match (variant, theme) {
        // Circuit Board Theme - Silicon Mind aesthetic
        (TileVariant::Empty, MazeTheme::CircuitBoard) => Color::srgb(0.08, 0.08, 0.12),
        (TileVariant::Straight, MazeTheme::CircuitBoard) => Color::srgb(0.15, 0.35, 0.50),
        (TileVariant::Corner, MazeTheme::CircuitBoard) => Color::srgb(0.18, 0.38, 0.52),
        (TileVariant::TJunction, MazeTheme::CircuitBoard) => Color::srgb(0.25, 0.45, 0.60),
        (TileVariant::Cross, MazeTheme::CircuitBoard) => Color::srgb(0.35, 0.55, 0.70),

        // Organic Growth - Biological patterns
        (TileVariant::Empty, MazeTheme::OrganicGrowth) => Color::srgb(0.08, 0.12, 0.06),
        (TileVariant::Straight, MazeTheme::OrganicGrowth) => Color::srgb(0.15, 0.35, 0.12),
        (TileVariant::Corner, MazeTheme::OrganicGrowth) => Color::srgb(0.18, 0.40, 0.15),
        (TileVariant::TJunction, MazeTheme::OrganicGrowth) => Color::srgb(0.22, 0.48, 0.18),
        (TileVariant::Cross, MazeTheme::OrganicGrowth) => Color::srgb(0.28, 0.55, 0.22),

        // Geometric Pure - Clean mathematical
        (TileVariant::Empty, MazeTheme::GeometricPure) => Color::srgb(0.85, 0.85, 0.88),
        (TileVariant::Straight, MazeTheme::GeometricPure) => Color::srgb(0.65, 0.65, 0.70),
        (TileVariant::Corner, MazeTheme::GeometricPure) => Color::srgb(0.55, 0.55, 0.62),
        (TileVariant::TJunction, MazeTheme::GeometricPure) => Color::srgb(0.45, 0.45, 0.52),
        (TileVariant::Cross, MazeTheme::GeometricPure) => Color::srgb(0.35, 0.35, 0.42),

        // Hybrid - Mixed aesthetic
        (_, MazeTheme::Hybrid) => Color::srgb(0.25, 0.25, 0.35),

        // Fallback for other variants
        (_, _) => Color::srgb(0.20, 0.20, 0.25),
    }
}

/// Get wall color based on theme
fn get_wall_color(theme: MazeTheme) -> Color {
    match theme {
        MazeTheme::CircuitBoard => Color::srgb(0.02, 0.05, 0.08),
        MazeTheme::OrganicGrowth => Color::srgb(0.06, 0.04, 0.02),
        MazeTheme::GeometricPure => Color::srgb(0.15, 0.15, 0.18),
        MazeTheme::Hybrid => Color::srgb(0.08, 0.08, 0.10),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cell_to_variant_empty() {
        let cell = Cell::empty();
        assert_eq!(cell_to_tile_variant(&cell), TileVariant::Empty);
    }

    #[test]
    fn test_cell_to_variant_straight() {
        // North-South passage = straight
        let cell = Cell::NORTH | Cell::SOUTH;
        assert_eq!(cell_to_tile_variant(&cell), TileVariant::Straight);

        // East-West passage = straight
        let cell = Cell::EAST | Cell::WEST;
        assert_eq!(cell_to_tile_variant(&cell), TileVariant::Straight);
    }

    #[test]
    fn test_cell_to_variant_corner() {
        // North-East = corner
        let cell = Cell::NORTH | Cell::EAST;
        assert_eq!(cell_to_tile_variant(&cell), TileVariant::Corner);

        // South-West = corner
        let cell = Cell::SOUTH | Cell::WEST;
        assert_eq!(cell_to_tile_variant(&cell), TileVariant::Corner);
    }

    #[test]
    fn test_cell_to_variant_tjunction() {
        // Three directions = T-junction
        let cell = Cell::NORTH | Cell::EAST | Cell::SOUTH;
        assert_eq!(cell_to_tile_variant(&cell), TileVariant::TJunction);
    }

    #[test]
    fn test_cell_to_variant_cross() {
        // All four directions = cross
        let cell = Cell::all();
        assert_eq!(cell_to_tile_variant(&cell), TileVariant::Cross);
    }
}
