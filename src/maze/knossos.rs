//! Knossos maze generation integration
//!
//! This module wraps bevy_knossos to generate mazes with configurable algorithms
//! and difficulty progression based on player completions.

use bevy::prelude::*;
use bevy_knossos::maze::{
    OrthogonalMazeBuilder, OrthogonalMaze, Cell,
    BinaryTree, Sidewinder, RecursiveBacktracking, Prim,
    GrowingTree, Kruskal, HuntAndKill, RecursiveDivision,
    Bias, Method,
};
use avian2d::prelude::*;

use super::{MazeEntity, MazeWall, MazeFloor, MazeGoal};

/// Configuration for maze generation
#[derive(Resource, Clone)]
pub struct KnossosMazeConfig {
    pub width: usize,
    pub height: usize,
    pub algorithm: KnossosMazeAlgorithm,
    pub seed: Option<u64>,
    pub cell_size: f32,
}

impl Default for KnossosMazeConfig {
    fn default() -> Self {
        Self {
            width: 15,
            height: 15,
            algorithm: KnossosMazeAlgorithm::Prim,
            seed: None,
            cell_size: 40.0,
        }
    }
}

/// Available maze generation algorithms, ordered by difficulty
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnossosMazeAlgorithm {
    /// Easiest - diagonal bias, predictable patterns
    BinaryTree,
    /// Easy - row-based patterns, slightly more complex
    Sidewinder,
    /// Medium - classic recursive backtracking, familiar
    RecursiveBacktracking,
    /// Medium-Hard - river-like passages, the default
    Prim,
    /// Hard - varied paths, adjustable
    GrowingTree,
    /// Hard - uniform random spanning tree
    Kruskal,
    /// Hardest - long corridors, challenging navigation
    HuntAndKill,
    /// Expert - room-based division
    RecursiveDivision,
}

impl KnossosMazeAlgorithm {
    /// Get the algorithm based on completion count for difficulty progression
    pub fn for_completion(completions: u32) -> Self {
        match completions {
            0..=2 => Self::BinaryTree,
            3..=5 => Self::Sidewinder,
            6..=9 => Self::RecursiveBacktracking,
            10..=14 => Self::Prim,
            15..=19 => Self::GrowingTree,
            20..=24 => Self::Kruskal,
            25..=29 => Self::HuntAndKill,
            _ => Self::RecursiveDivision,
        }
    }

    /// Get a human-readable name for the algorithm
    pub fn name(&self) -> &'static str {
        match self {
            Self::BinaryTree => "Binary Tree",
            Self::Sidewinder => "Sidewinder",
            Self::RecursiveBacktracking => "Recursive Backtracking",
            Self::Prim => "Prim's Algorithm",
            Self::GrowingTree => "Growing Tree",
            Self::Kruskal => "Kruskal's Algorithm",
            Self::HuntAndKill => "Hunt and Kill",
            Self::RecursiveDivision => "Recursive Division",
        }
    }

    /// Get difficulty rating (1-10)
    pub fn difficulty(&self) -> u8 {
        match self {
            Self::BinaryTree => 2,
            Self::Sidewinder => 3,
            Self::RecursiveBacktracking => 5,
            Self::Prim => 6,
            Self::GrowingTree => 7,
            Self::Kruskal => 7,
            Self::HuntAndKill => 8,
            Self::RecursiveDivision => 9,
        }
    }
}

/// Generate a maze using bevy_knossos with the specified configuration
pub fn generate_knossos_maze(config: &KnossosMazeConfig) -> Result<OrthogonalMaze, String> {
    let builder = OrthogonalMazeBuilder::new()
        .width(config.width)
        .height(config.height);

    let builder = if let Some(seed) = config.seed {
        builder.seed(Some(seed))
    } else {
        builder
    };

    // Apply algorithm based on configuration
    // Note: Some algorithms are unit structs, others require constructors
    let maze_result = match config.algorithm {
        KnossosMazeAlgorithm::BinaryTree => {
            builder.algorithm(Box::new(BinaryTree::new(Bias::NorthWest))).build()
        }
        KnossosMazeAlgorithm::Sidewinder => {
            builder.algorithm(Box::new(Sidewinder)).build()
        }
        KnossosMazeAlgorithm::RecursiveBacktracking => {
            builder.algorithm(Box::new(RecursiveBacktracking)).build()
        }
        KnossosMazeAlgorithm::Prim => {
            builder.algorithm(Box::new(Prim::new())).build()
        }
        KnossosMazeAlgorithm::GrowingTree => {
            builder.algorithm(Box::new(GrowingTree::new(Method::Random))).build()
        }
        KnossosMazeAlgorithm::Kruskal => {
            builder.algorithm(Box::new(Kruskal)).build()
        }
        KnossosMazeAlgorithm::HuntAndKill => {
            builder.algorithm(Box::new(HuntAndKill::new())).build()
        }
        KnossosMazeAlgorithm::RecursiveDivision => {
            builder.algorithm(Box::new(RecursiveDivision)).build()
        }
    };

    maze_result.map_err(|e| format!("Maze generation failed: {:?}", e))
}

/// Spawn the maze entities from a generated knossos maze
pub fn spawn_knossos_maze_entities(
    commands: &mut Commands,
    maze: &OrthogonalMaze,
    config: &KnossosMazeConfig,
    offset: Vec2,
) {
    let cell_size = config.cell_size;
    let wall_thickness = 5.0;

    // Iterate through maze cells and spawn entities
    for (coords, cell) in maze.iter() {
        let world_pos = Vec2::new(
            coords.0 as f32 * cell_size + offset.x,
            -(coords.1 as f32 * cell_size) + offset.y,
        );

        // Spawn floor for every cell
        let variation = ((coords.0 + coords.1) % 4) as u8;
        spawn_floor_tile(commands, world_pos, cell_size, variation);

        // Spawn walls based on cell boundaries
        // Cell stores passages (open directions), so check for ABSENCE of passage = wall
        if !cell.contains(Cell::NORTH) {
            spawn_wall(commands, world_pos, cell_size, wall_thickness, WallDirection::North);
        }
        if !cell.contains(Cell::SOUTH) {
            spawn_wall(commands, world_pos, cell_size, wall_thickness, WallDirection::South);
        }
        if !cell.contains(Cell::EAST) {
            spawn_wall(commands, world_pos, cell_size, wall_thickness, WallDirection::East);
        }
        if !cell.contains(Cell::WEST) {
            spawn_wall(commands, world_pos, cell_size, wall_thickness, WallDirection::West);
        }
    }

    // Spawn goal at bottom-right corner
    let goal_x = (config.width - 2) as f32 * cell_size + offset.x;
    let goal_y = -((config.height - 2) as f32 * cell_size) + offset.y;
    spawn_goal(commands, Vec2::new(goal_x, goal_y), cell_size);
}

enum WallDirection {
    North,
    South,
    East,
    West,
}

fn spawn_wall(
    commands: &mut Commands,
    cell_pos: Vec2,
    cell_size: f32,
    thickness: f32,
    direction: WallDirection,
) {
    let half_cell = cell_size / 2.0;
    let (offset, size) = match direction {
        WallDirection::North => (Vec2::new(0.0, half_cell), Vec2::new(cell_size, thickness)),
        WallDirection::South => (Vec2::new(0.0, -half_cell), Vec2::new(cell_size, thickness)),
        WallDirection::East => (Vec2::new(half_cell, 0.0), Vec2::new(thickness, cell_size)),
        WallDirection::West => (Vec2::new(-half_cell, 0.0), Vec2::new(thickness, cell_size)),
    };

    let pos = cell_pos + offset;

    commands.spawn((
        MazeEntity,
        MazeWall,
        Sprite {
            color: Color::srgb(0.02, 0.02, 0.06),
            custom_size: Some(size),
            ..default()
        },
        Transform::from_xyz(pos.x, pos.y, -5.0),
        RigidBody::Static,
        Collider::rectangle(size.x, size.y),
    ));
}

fn spawn_floor_tile(commands: &mut Commands, pos: Vec2, cell_size: f32, variation: u8) {
    let colors = [
        Color::srgb(0.15, 0.12, 0.25),  // Base purple
        Color::srgb(0.13, 0.11, 0.22),  // Darker
        Color::srgb(0.17, 0.14, 0.28),  // Lighter
        Color::srgb(0.14, 0.13, 0.24),  // Subtle variation
    ];

    commands.spawn((
        MazeEntity,
        MazeFloor,
        Sprite {
            color: colors[variation as usize % colors.len()],
            custom_size: Some(Vec2::splat(cell_size - 2.0)),
            ..default()
        },
        Transform::from_xyz(pos.x, pos.y, -10.0),
    ));
}

fn spawn_goal(commands: &mut Commands, pos: Vec2, cell_size: f32) {
    commands.spawn((
        MazeEntity,
        MazeGoal,
        Sprite {
            color: Color::srgba(0.3, 1.0, 0.3, 0.8),
            custom_size: Some(Vec2::splat(cell_size * 0.6)),
            ..default()
        },
        Transform::from_xyz(pos.x, pos.y, -8.0),
    ));
}

/// Update maze configuration based on current completion count
pub fn update_config_for_difficulty(config: &mut KnossosMazeConfig, completions: u32) {
    config.algorithm = KnossosMazeAlgorithm::for_completion(completions);

    // Optionally increase size with difficulty
    let size_bonus = (completions / 10).min(5) as usize;
    config.width = 15 + size_bonus * 2;
    config.height = 15 + size_bonus * 2;
}
