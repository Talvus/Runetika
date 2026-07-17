use bevy::prelude::*;
use std::collections::HashMap;

/// Unique identifier for a tile type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TileId(pub u32);

/// Socket types for Wang tile-style constraint matching
///
/// # Conceptual Model
/// Sockets represent the "connection points" of a tile. Like puzzle pieces,
/// tiles can only be adjacent if their touching sockets are compatible.
/// This creates emergent patterns from simple local rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SocketType {
    /// Empty edge - connects only to other empty edges
    None,
    /// Generic circuit connection - universal connector
    Circuit,
    /// Power line - must connect to Power or Circuit
    #[allow(dead_code)]
    Power,
    /// Ground line - must connect to Ground or Circuit
    #[allow(dead_code)]
    Ground,
    /// Data line - must connect only to Data
    #[allow(dead_code)]
    Data,
}

impl SocketType {
    /// Check if two sockets can be adjacent
    pub fn compatible_with(&self, other: &SocketType) -> bool {
        match (self, other) {
            (SocketType::None, SocketType::None) => true,
            (SocketType::Circuit, SocketType::Circuit) => true,
            (SocketType::Circuit, SocketType::Power) | (SocketType::Power, SocketType::Circuit) => true,
            (SocketType::Circuit, SocketType::Ground) | (SocketType::Ground, SocketType::Circuit) => true,
            (SocketType::Power, SocketType::Power) => true,
            (SocketType::Ground, SocketType::Ground) => true,
            (SocketType::Data, SocketType::Data) => true,
            _ => false,
        }
    }
}

/// Tile variants for the circuit board theme
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TileVariant {
    /// Straight path (horizontal or vertical)
    Straight,
    /// 90-degree turn
    Corner,
    /// T-shaped junction
    TJunction,
    /// Four-way intersection
    Cross,
    /// Empty space (no circuit)
    Empty,
    /// Capacitor component (decorative)
    #[allow(dead_code)]
    Capacitor,
    /// Resistor component (decorative)
    #[allow(dead_code)]
    Resistor,
    /// Junction node (connects all directions)
    #[allow(dead_code)]
    Junction,
}

/// A single tile definition with visual and constraint information
///
/// # ARC Integration
/// Each tile represents a pattern primitive. Players learn to recognize
/// valid tile combinations through observation - a core ARC reasoning skill.
#[derive(Debug, Clone)]
pub struct Tile {
    #[allow(dead_code)]
    pub id: TileId,
    #[allow(dead_code)]
    pub name: String,
    pub variant: TileVariant,
    #[allow(dead_code)]
    pub sprite_path: String,
    /// Sockets in order: [North, East, South, West]
    pub sockets: [SocketType; 4],
    /// Weight for biased random selection (higher = more common)
    pub weight: f32,
}

/// Collection of tiles with metadata
#[derive(Debug, Clone, Resource)]
pub struct TileSet {
    pub tiles: HashMap<TileId, Tile>,
    pub theme: MazeTheme,
}

/// Visual theme for the maze
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MazeTheme {
    /// Silicon civilization tech aesthetic
    CircuitBoard,
    /// Biological/fractal patterns
    #[allow(dead_code)]
    OrganicGrowth,
    /// Clean mathematical structures
    #[allow(dead_code)]
    GeometricPure,
    /// Mixed aesthetic
    #[allow(dead_code)]
    Hybrid,
}

impl TileSet {
    /// Create the default circuit board tile set
    ///
    /// # Circuit Board Theme
    /// This theme evokes the "Silicon Mind" narrative - mazes are the
    /// memory structures of the fallen computational civilization.
    pub fn circuit_board() -> Self {
        let mut tiles = HashMap::new();

        // Tile 0: Empty space
        tiles.insert(TileId(0), Tile {
            id: TileId(0),
            name: "Empty".to_string(),
            variant: TileVariant::Empty,
            sprite_path: "textures/circuit_tiles/empty.png".to_string(),
            sockets: [
                SocketType::None,
                SocketType::None,
                SocketType::None,
                SocketType::None,
            ],
            weight: 2.0, // More common to create open spaces
        });

        // Tile 1: Straight vertical
        tiles.insert(TileId(1), Tile {
            id: TileId(1),
            name: "Straight_V".to_string(),
            variant: TileVariant::Straight,
            sprite_path: "textures/circuit_tiles/straight_v.png".to_string(),
            sockets: [
                SocketType::Circuit, // North
                SocketType::None,    // East
                SocketType::Circuit, // South
                SocketType::None,    // West
            ],
            weight: 1.0,
        });

        // Tile 2: Straight horizontal
        tiles.insert(TileId(2), Tile {
            id: TileId(2),
            name: "Straight_H".to_string(),
            variant: TileVariant::Straight,
            sprite_path: "textures/circuit_tiles/straight_h.png".to_string(),
            sockets: [
                SocketType::None,    // North
                SocketType::Circuit, // East
                SocketType::None,    // South
                SocketType::Circuit, // West
            ],
            weight: 1.0,
        });

        // Tile 3: Corner NE
        tiles.insert(TileId(3), Tile {
            id: TileId(3),
            name: "Corner_NE".to_string(),
            variant: TileVariant::Corner,
            sprite_path: "textures/circuit_tiles/corner_ne.png".to_string(),
            sockets: [
                SocketType::Circuit, // North
                SocketType::Circuit, // East
                SocketType::None,
                SocketType::None,
            ],
            weight: 0.8,
        });

        // Tile 4: Corner NW
        tiles.insert(TileId(4), Tile {
            id: TileId(4),
            name: "Corner_NW".to_string(),
            variant: TileVariant::Corner,
            sprite_path: "textures/circuit_tiles/corner_nw.png".to_string(),
            sockets: [
                SocketType::Circuit, // North
                SocketType::None,
                SocketType::None,
                SocketType::Circuit, // West
            ],
            weight: 0.8,
        });

        // Tile 5: Corner SE
        tiles.insert(TileId(5), Tile {
            id: TileId(5),
            name: "Corner_SE".to_string(),
            variant: TileVariant::Corner,
            sprite_path: "textures/circuit_tiles/corner_se.png".to_string(),
            sockets: [
                SocketType::None,
                SocketType::Circuit, // East
                SocketType::Circuit, // South
                SocketType::None,
            ],
            weight: 0.8,
        });

        // Tile 6: Corner SW
        tiles.insert(TileId(6), Tile {
            id: TileId(6),
            name: "Corner_SW".to_string(),
            variant: TileVariant::Corner,
            sprite_path: "textures/circuit_tiles/corner_sw.png".to_string(),
            sockets: [
                SocketType::None,
                SocketType::None,
                SocketType::Circuit, // South
                SocketType::Circuit, // West
            ],
            weight: 0.8,
        });

        // Tile 7: T-Junction North
        tiles.insert(TileId(7), Tile {
            id: TileId(7),
            name: "TJunction_N".to_string(),
            variant: TileVariant::TJunction,
            sprite_path: "textures/circuit_tiles/tjunc_n.png".to_string(),
            sockets: [
                SocketType::Circuit,
                SocketType::Circuit,
                SocketType::None,
                SocketType::Circuit,
            ],
            weight: 0.5,
        });

        // Tile 8: Cross intersection
        tiles.insert(TileId(8), Tile {
            id: TileId(8),
            name: "Cross".to_string(),
            variant: TileVariant::Cross,
            sprite_path: "textures/circuit_tiles/cross.png".to_string(),
            sockets: [
                SocketType::Circuit,
                SocketType::Circuit,
                SocketType::Circuit,
                SocketType::Circuit,
            ],
            weight: 0.3, // Rare to avoid over-connectivity
        });

        TileSet {
            tiles,
            theme: MazeTheme::CircuitBoard,
        }
    }

    /// Get all tile IDs in this set
    pub fn tile_ids(&self) -> Vec<TileId> {
        self.tiles.keys().copied().collect()
    }

    /// Get a tile by ID
    #[allow(dead_code)]
    pub fn get_tile(&self, id: TileId) -> Option<&Tile> {
        self.tiles.get(&id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_socket_compatibility() {
        assert!(SocketType::Circuit.compatible_with(&SocketType::Circuit));
        assert!(SocketType::Circuit.compatible_with(&SocketType::Power));
        assert!(SocketType::Power.compatible_with(&SocketType::Circuit));
        assert!(!SocketType::Data.compatible_with(&SocketType::Power));
        assert!(SocketType::None.compatible_with(&SocketType::None));
    }

    #[test]
    fn test_circuit_board_tileset() {
        let tileset = TileSet::circuit_board();
        assert_eq!(tileset.tiles.len(), 9); // 9 tiles in circuit board set
        assert_eq!(tileset.theme, MazeTheme::CircuitBoard);

        // Verify tile 0 is empty
        let empty = tileset.get_tile(TileId(0)).unwrap();
        assert_eq!(empty.variant, TileVariant::Empty);
        assert_eq!(empty.sockets, [SocketType::None; 4]);
    }
}
