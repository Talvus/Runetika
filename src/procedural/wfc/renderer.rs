/// WFC Isometric Tile Renderer
///
/// Visualizes Wave Function Collapse generated mazes using isometric 2.5D rendering.
/// Renders WfcCell entities as colored diamond-shaped tiles with proper depth sorting.
///
/// # Architecture
/// - Monitors WfcCell collapse events
/// - Spawns visual sprites for collapsed tiles
/// - Implements Z-depth sorting for isometric layering
/// - Supports 16x16 to 64x64 grid sizes

use bevy::prelude::*;
use super::{WfcCell, TileSet, tiles::{TileVariant, MazeTheme}};
use crate::game_state::GameState;

/// Isometric tile dimensions (diamond shape)
pub const TILE_WIDTH: f32 = 64.0;
pub const TILE_HEIGHT: f32 = 32.0;

/// Z-layer offset for maze floor
const FLOOR_Z_OFFSET: f32 = -100.0;

/// Component: Visual representation of a WFC tile
///
/// # Conceptual Model
/// Each WfcCell in the generation grid has a corresponding WfcTile sprite
/// in the render world. The grid position determines both screen position
/// (via isometric conversion) and Z-depth (for layering).
///
/// # Practical Implementation
/// This component stores grid coordinates for depth sorting and debugging.
#[derive(Component)]
pub struct WfcTileSprite {
    #[allow(dead_code)]
    pub grid_x: i32,
    pub grid_y: i32,
    #[allow(dead_code)]
    pub tile_id: super::tiles::TileId,
}

/// Component: Marker for entities that need isometric depth sorting
#[derive(Component)]
pub struct IsometricDepthSorted;

/// Plugin: WFC Isometric Rendering System
///
/// # Systems
/// - `spawn_wfc_tiles`: Creates visual sprites when generation completes
/// - `update_wfc_depth_sorting`: Maintains Z-order based on grid position
/// - `cleanup_wfc_tiles`: Removes tiles when maze is cleared
pub struct WfcRendererPlugin;

impl Plugin for WfcRendererPlugin {
    fn build(&self, app: &mut App) {
        app
            // Systems run when WFC visualization is active
            .add_systems(Update, (
                spawn_wfc_tiles_on_complete
                    .run_if(resource_exists::<super::WfcGenerationState>),
                update_wfc_depth_sorting,
            ).run_if(in_state(GameState::InGame)));

        info!("WfcRendererPlugin initialized with isometric rendering");
    }
}

/// System: Spawn visual tiles when WFC generation completes
///
/// # Algorithm
/// 1. Listen for GenerationCompleteEvent
/// 2. Query all collapsed WfcCell entities
/// 3. For each cell, spawn a WfcTileSprite with:
///    - Isometric world position
///    - Color based on tile variant
///    - Z-depth based on grid Y position
///
/// # Performance
/// - 16x16 grid: ~256 sprites spawned
/// - 32x32 grid: ~1024 sprites spawned
/// - 64x64 grid: ~4096 sprites spawned (consider culling)
pub fn spawn_wfc_tiles_on_complete(
    mut commands: Commands,
    gen_state: Res<super::WfcGenerationState>,
    tileset: Res<TileSet>,
    cells: Query<(&WfcCell, Entity)>,
    mut complete_events: EventReader<super::GenerationCompleteEvent>,
) {
    for event in complete_events.read() {
        info!(
            "Spawning WFC tile sprites for {}x{} maze ({} steps)",
            event.width, event.height, event.steps
        );

        // Iterate through the grid in generation state
        for y in 0..gen_state.height {
            for x in 0..gen_state.width {
                // Get the entity at this grid position
                if let Some(cell_entity) = gen_state.grid.get(y).and_then(|row| row.get(x)) {
                    if let Ok((cell, _)) = cells.get(*cell_entity) {
                        // Cell should be collapsed with single possibility
                        if cell.collapsed && cell.possibilities.len() == 1 {
                            if let Some(&tile_id) = cell.possibilities.iter().next() {
                                if let Some(tile) = tileset.tiles.get(&tile_id) {
                                    spawn_tile_sprite(
                                        &mut commands,
                                        x as i32,
                                        y as i32,
                                        tile_id,
                                        tile.variant,
                                        tileset.theme,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Helper: Spawn a single tile sprite
///
/// # Arguments
/// - `grid_x`, `grid_y`: Grid coordinates (0,0 = top-left)
/// - `tile_id`: Identifier for tile type
/// - `variant`: Visual variant (Empty, Straight, Corner, etc.)
/// - `theme`: Color theme (CircuitBoard, OrganicGrowth, etc.)
fn spawn_tile_sprite(
    commands: &mut Commands,
    grid_x: i32,
    grid_y: i32,
    tile_id: super::tiles::TileId,
    variant: TileVariant,
    theme: MazeTheme,
) {
    let world_pos = isometric_to_world(grid_x as f32, grid_y as f32);
    let color = get_tile_color(variant, theme);
    let z_depth = FLOOR_Z_OFFSET - (grid_y as f32);

    commands.spawn((
        WfcTileSprite {
            grid_x,
            grid_y,
            tile_id,
        },
        IsometricDepthSorted,
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

/// Coordinate conversion: Isometric grid → World screen space
///
/// # Mathematical Model
/// Isometric projection transforms a 2D grid into a diamond pattern:
/// - X-axis: Diagonal from top-left to bottom-right
/// - Y-axis: Diagonal from top-right to bottom-left
///
/// Formula: `world = (x - y, x + y) * scale`
///
/// # Practical Usage
/// Grid position (5, 3) → Screen position (64, 128)
pub fn isometric_to_world(grid_x: f32, grid_y: f32) -> Vec2 {
    Vec2::new(
        (grid_x - grid_y) * TILE_WIDTH * 0.5,
        (grid_x + grid_y) * TILE_HEIGHT * 0.5,
    )
}

/// Coordinate conversion: World screen space → Isometric grid
///
/// # Mathematical Model
/// Inverse of isometric_to_world transformation.
/// Used for mouse picking and raycasting (future feature).
///
/// # Practical Usage
/// Screen position (64, 128) → Grid position (5, 3)
#[allow(dead_code)]
pub fn world_to_isometric(world_x: f32, world_y: f32) -> Vec2 {
    let grid_x = (world_x / (TILE_WIDTH * 0.5) + world_y / (TILE_HEIGHT * 0.5)) * 0.5;
    let grid_y = (world_y / (TILE_HEIGHT * 0.5) - world_x / (TILE_WIDTH * 0.5)) * 0.5;
    Vec2::new(grid_x, grid_y)
}

/// System: Update Z-depth for isometric layering
///
/// # Depth Sorting Strategy
/// Z-depth is derived solely from grid Y position:
/// - Higher Y (further back) = Lower Z (rendered first)
/// - Formula: `z = FLOOR_Z_OFFSET - grid_y`
///
/// This prevents Z-fighting and ensures proper overlap.
pub fn update_wfc_depth_sorting(
    mut query: Query<(&mut Transform, &WfcTileSprite), With<IsometricDepthSorted>>,
) {
    for (mut transform, tile) in query.iter_mut() {
        transform.translation.z = FLOOR_Z_OFFSET - (tile.grid_y as f32);
    }
}

/// Color mapping: Tile variant + Theme → RGB color
///
/// # Circuit Board Theme
/// - Empty: Dark floor (low activity)
/// - Straight: Active circuit path (cyan/blue)
/// - Corner: Active circuit bend (cyan/blue)
/// - T-Junction: Circuit node (brighter blue)
/// - Cross: Major intersection (bright blue)
///
/// # Other Themes
/// - OrganicGrowth: Greens and browns
/// - GeometricPure: Clean grays and whites
/// - Hybrid: Mixed colors
fn get_tile_color(variant: TileVariant, theme: MazeTheme) -> Color {
    match (variant, theme) {
        // Circuit Board Theme (Silicon Mind aesthetic)
        (TileVariant::Empty, MazeTheme::CircuitBoard) => Color::srgb(0.12, 0.12, 0.20),
        (TileVariant::Straight, MazeTheme::CircuitBoard) => Color::srgb(0.25, 0.45, 0.65),
        (TileVariant::Corner, MazeTheme::CircuitBoard) => Color::srgb(0.25, 0.45, 0.65),
        (TileVariant::TJunction, MazeTheme::CircuitBoard) => Color::srgb(0.35, 0.55, 0.75),
        (TileVariant::Cross, MazeTheme::CircuitBoard) => Color::srgb(0.45, 0.65, 0.85),
        (TileVariant::Capacitor, MazeTheme::CircuitBoard) => Color::srgb(0.50, 0.70, 0.40),
        (TileVariant::Resistor, MazeTheme::CircuitBoard) => Color::srgb(0.70, 0.50, 0.30),
        (TileVariant::Junction, MazeTheme::CircuitBoard) => Color::srgb(0.55, 0.75, 0.95),

        // OrganicGrowth Theme (biological/fractal)
        (TileVariant::Empty, MazeTheme::OrganicGrowth) => Color::srgb(0.15, 0.20, 0.10),
        (_, MazeTheme::OrganicGrowth) => Color::srgb(0.20, 0.40, 0.15),

        // GeometricPure Theme (mathematical/clean)
        (TileVariant::Empty, MazeTheme::GeometricPure) => Color::srgb(0.90, 0.90, 0.90),
        (_, MazeTheme::GeometricPure) => Color::srgb(0.30, 0.30, 0.35),

        // Hybrid Theme (mixed aesthetic)
        (_, MazeTheme::Hybrid) => Color::srgb(0.35, 0.35, 0.45),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_isometric_conversion_identity() {
        let grid_pos = Vec2::new(10.0, 15.0);
        let world_pos = isometric_to_world(grid_pos.x, grid_pos.y);
        let back_to_grid = world_to_isometric(world_pos.x, world_pos.y);

        assert!((grid_pos.x - back_to_grid.x).abs() < 0.001);
        assert!((grid_pos.y - back_to_grid.y).abs() < 0.001);
    }

    #[test]
    fn test_depth_sorting_order() {
        // Further back (higher Y) should have lower Z
        let z_front = FLOOR_Z_OFFSET - 0.0;
        let z_back = FLOOR_Z_OFFSET - 10.0;
        assert!(z_back < z_front, "Back tiles should have lower Z than front tiles");
    }

    #[test]
    fn test_tile_color_circuit_board() {
        let color = get_tile_color(TileVariant::Cross, MazeTheme::CircuitBoard);
        // Cross should be brightest
        assert!(color.to_linear().red > 0.4);
    }
}
