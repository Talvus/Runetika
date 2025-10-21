use super::tiles::{TileId, TileSet};
use bevy::prelude::*;
use std::collections::{HashMap, HashSet};

/// Cardinal directions for tile adjacency
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Direction {
    North,
    South,
    East,
    West,
}

impl Direction {
    /// Get the opposite direction
    pub fn opposite(&self) -> Direction {
        match self {
            Direction::North => Direction::South,
            Direction::South => Direction::North,
            Direction::East => Direction::West,
            Direction::West => Direction::East,
        }
    }

    /// Get the grid offset for this direction
    pub fn offset(&self) -> IVec2 {
        match self {
            Direction::North => IVec2::new(0, 1),
            Direction::South => IVec2::new(0, -1),
            Direction::East => IVec2::new(1, 0),
            Direction::West => IVec2::new(-1, 0),
        }
    }

    /// Get socket index for this direction
    /// Sockets are ordered: [North, East, South, West]
    pub fn socket_index(&self) -> usize {
        match self {
            Direction::North => 0,
            Direction::East => 1,
            Direction::South => 2,
            Direction::West => 3,
        }
    }

    /// All four directions
    pub fn all() -> [Direction; 4] {
        [
            Direction::North,
            Direction::East,
            Direction::South,
            Direction::West,
        ]
    }
}

/// Graph of constraint rules defining which tiles can be adjacent
///
/// # Conceptual Model: Pattern Recognition
/// The constraint graph encodes the "rules of reality" for the maze.
/// Players observing WFC generation learn these rules implicitly - a
/// fundamental ARC reasoning skill.
///
/// # Technical Implementation
/// Uses a hash map for O(1) constraint lookups during propagation.
/// Pre-computed at initialization from tile socket compatibility.
#[derive(Debug, Clone, Resource)]
pub struct ConstraintGraph {
    /// Map: (tile_id, direction) -> Set<allowed_neighbor_ids>
    adjacency: HashMap<(TileId, Direction), HashSet<TileId>>,
}

impl ConstraintGraph {
    /// Build constraint graph from a tile set
    ///
    /// # Algorithm
    /// For each tile, for each direction, find all tiles whose opposite
    /// socket is compatible. This creates the adjacency rules that WFC
    /// will propagate.
    pub fn from_tileset(tileset: &TileSet) -> Self {
        let mut adjacency = HashMap::new();

        // For each tile in the set
        for (tile_id, tile) in &tileset.tiles {
            // For each direction
            for direction in Direction::all() {
                let my_socket = tile.sockets[direction.socket_index()];

                // Find all compatible neighbors
                let allowed: HashSet<TileId> = tileset
                    .tiles
                    .iter()
                    .filter(|(_, neighbor_tile)| {
                        let opposite_socket =
                            neighbor_tile.sockets[direction.opposite().socket_index()];
                        my_socket.compatible_with(&opposite_socket)
                    })
                    .map(|(id, _)| *id)
                    .collect();

                adjacency.insert((*tile_id, direction), allowed);
            }
        }

        ConstraintGraph { adjacency }
    }

    /// Check if a tile is allowed to be adjacent to another in a specific direction
    ///
    /// # Arguments
    /// * `tile` - The source tile
    /// * `direction` - Direction to the neighbor
    /// * `neighbor` - The potential neighbor tile
    ///
    /// # Returns
    /// `true` if the adjacency is allowed by constraints
    pub fn allows(&self, tile: TileId, direction: Direction, neighbor: TileId) -> bool {
        self.adjacency
            .get(&(tile, direction))
            .map(|allowed_set| allowed_set.contains(&neighbor))
            .unwrap_or(false)
    }

    /// Get all allowed neighbors for a tile in a direction
    pub fn get_allowed(&self, tile: TileId, direction: Direction) -> HashSet<TileId> {
        self.adjacency
            .get(&(tile, direction))
            .cloned()
            .unwrap_or_else(HashSet::new)
    }

    /// Get the intersection of multiple allowed sets
    ///
    /// Used during propagation to constrain cells based on multiple neighbors
    pub fn intersect_allowed(
        &self,
        constraint_sets: Vec<HashSet<TileId>>,
    ) -> HashSet<TileId> {
        if constraint_sets.is_empty() {
            return HashSet::new();
        }

        let mut result = constraint_sets[0].clone();
        for set in &constraint_sets[1..] {
            result = result.intersection(set).copied().collect();
        }
        result
    }

    /// Count total constraint rules
    pub fn rule_count(&self) -> usize {
        self.adjacency.len()
    }

    /// Get statistics about the constraint graph
    pub fn stats(&self) -> ConstraintStats {
        let total_rules = self.adjacency.len();
        let avg_neighbors: f32 = self.adjacency
            .values()
            .map(|set| set.len() as f32)
            .sum::<f32>() / total_rules as f32;

        let max_neighbors = self.adjacency
            .values()
            .map(|set| set.len())
            .max()
            .unwrap_or(0);

        let min_neighbors = self.adjacency
            .values()
            .map(|set| set.len())
            .min()
            .unwrap_or(0);

        ConstraintStats {
            total_rules,
            avg_neighbors,
            max_neighbors,
            min_neighbors,
        }
    }
}

/// Statistics about the constraint graph
#[derive(Debug)]
pub struct ConstraintStats {
    pub total_rules: usize,
    pub avg_neighbors: f32,
    pub max_neighbors: usize,
    pub min_neighbors: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::procedural::wfc::tiles::TileSet;

    #[test]
    fn test_direction_opposite() {
        assert_eq!(Direction::North.opposite(), Direction::South);
        assert_eq!(Direction::East.opposite(), Direction::West);
    }

    #[test]
    fn test_direction_offset() {
        assert_eq!(Direction::North.offset(), IVec2::new(0, 1));
        assert_eq!(Direction::East.offset(), IVec2::new(1, 0));
    }

    #[test]
    fn test_constraint_graph_construction() {
        let tileset = TileSet::circuit_board();
        let constraints = ConstraintGraph::from_tileset(&tileset);

        // Verify constraint graph was built
        assert!(constraints.rule_count() > 0);

        // Empty tile (0) should allow empty tiles in all directions
        assert!(constraints.allows(TileId(0), Direction::North, TileId(0)));

        let stats = constraints.stats();
        println!("Constraint stats: {:?}", stats);
        assert!(stats.avg_neighbors > 0.0);
    }

    #[test]
    fn test_intersect_allowed() {
        let tileset = TileSet::circuit_board();
        let constraints = ConstraintGraph::from_tileset(&tileset);

        let set1: HashSet<TileId> = [TileId(0), TileId(1), TileId(2)].iter().copied().collect();
        let set2: HashSet<TileId> = [TileId(1), TileId(2), TileId(3)].iter().copied().collect();

        let intersection = constraints.intersect_allowed(vec![set1, set2]);
        assert_eq!(intersection.len(), 2); // Should contain TileId(1) and TileId(2)
        assert!(intersection.contains(&TileId(1)));
        assert!(intersection.contains(&TileId(2)));
    }
}
