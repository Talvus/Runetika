/// Core Wave Function Collapse algorithm implementation
///
/// # Algorithm Overview
/// 1. **Observe**: Find cell with minimum entropy (most constrained)
/// 2. **Collapse**: Choose a tile from possibilities (weighted random)
/// 3. **Propagate**: Update neighbor constraints, cascade changes
/// 4. **Repeat**: Until all cells collapsed or contradiction occurs
///
/// # ARC Integration
/// The WFC process mirrors human abstract reasoning:
/// - Pattern inference from constraints
/// - Backtracking when assumptions fail
/// - Emergent global structure from local rules

use super::constraints::{ConstraintGraph, Direction};
use super::tiles::{TileId, TileSet};
use bevy::prelude::*;
use rand::prelude::*;
use std::collections::{HashMap, HashSet, VecDeque};

/// A single cell in the WFC grid
#[derive(Component, Clone, Debug)]
pub struct WfcCell {
    /// Grid position
    pub position: IVec2,

    /// Possible tiles that can exist here (superposition)
    pub possibilities: HashSet<TileId>,

    /// Shannon entropy (lower = more constrained)
    pub entropy: f32,

    /// Noise for tie-breaking
    pub noise: f32,

    /// Has collapsed to single tile?
    pub collapsed: bool,
}

impl WfcCell {
    /// Create new cell with all tiles possible
    pub fn new(position: IVec2, all_tiles: HashSet<TileId>, noise: f32) -> Self {
        let tile_count = all_tiles.len();
        Self {
            position,
            possibilities: all_tiles,
            entropy: (tile_count as f32).log2() + noise * 0.1,
            noise,
            collapsed: false,
        }
    }

    /// Calculate Shannon entropy: -Σ(p * log2(p)) + noise
    pub fn calculate_entropy(&mut self, tile_weights: &HashMap<TileId, f32>) {
        if self.collapsed || self.possibilities.is_empty() {
            self.entropy = 0.0;
            return;
        }

        let total_weight: f32 = self
            .possibilities
            .iter()
            .map(|id| tile_weights.get(id).unwrap_or(&1.0))
            .sum();

        if total_weight == 0.0 {
            self.entropy = 0.0;
            return;
        }

        self.entropy = self
            .possibilities
            .iter()
            .map(|id| {
                let p = tile_weights.get(id).unwrap_or(&1.0) / total_weight;
                if p > 0.0 {
                    -p * p.log2()
                } else {
                    0.0
                }
            })
            .sum::<f32>()
            + self.noise * 0.1; // Tie-breaking
    }

    /// Collapse to a single tile (weighted random choice)
    pub fn collapse(&mut self, tile_weights: &HashMap<TileId, f32>, rng: &mut StdRng) -> Option<TileId> {
        if self.possibilities.is_empty() {
            return None;
        }

        // Build weighted distribution
        let choices: Vec<(TileId, f32)> = self
            .possibilities
            .iter()
            .map(|&id| (id, *tile_weights.get(&id).unwrap_or(&1.0)))
            .collect();

        let total_weight: f32 = choices.iter().map(|(_, w)| w).sum();
        if total_weight == 0.0 {
            // All weights are zero, pick uniformly
            let chosen = *self.possibilities.iter().next().unwrap();
            self.possibilities.clear();
            self.possibilities.insert(chosen);
            self.collapsed = true;
            self.entropy = 0.0;
            return Some(chosen);
        }

        // Weighted random selection
        let mut random_value = rng.gen::<f32>() * total_weight;
        let mut chosen = choices[0].0;

        for (tile, weight) in choices {
            random_value -= weight;
            if random_value <= 0.0 {
                chosen = tile;
                break;
            }
        }

        self.possibilities.clear();
        self.possibilities.insert(chosen);
        self.collapsed = true;
        self.entropy = 0.0;

        Some(chosen)
    }

    /// Constrain possibilities based on allowed tiles
    pub fn constrain(&mut self, allowed: &HashSet<TileId>) -> bool {
        let old_count = self.possibilities.len();
        self.possibilities = self.possibilities.intersection(allowed).copied().collect();
        self.possibilities.len() != old_count
    }
}

/// WFC generation state
#[derive(Resource)]
pub struct WfcGenerationState {
    /// Grid dimensions
    pub width: usize,
    pub height: usize,

    /// Cell entities (grid[y][x])
    pub grid: Vec<Vec<Entity>>,

    /// RNG for reproducible generation
    pub rng: StdRng,

    /// Generation seed
    pub seed: u64,

    /// Current generation step
    pub step: usize,

    /// Is generation complete?
    pub complete: bool,

    /// Did generation fail (contradiction)?
    pub failed: bool,
}

impl WfcGenerationState {
    /// Create new generation state
    pub fn new(width: usize, height: usize, seed: u64) -> Self {
        Self {
            width,
            height,
            grid: Vec::new(),
            rng: StdRng::seed_from_u64(seed),
            seed,
            step: 0,
            complete: false,
            failed: false,
        }
    }

    /// Get entity at grid position
    pub fn get_entity(&self, pos: IVec2) -> Option<Entity> {
        if pos.x < 0 || pos.y < 0 || pos.x >= self.width as i32 || pos.y >= self.height as i32 {
            return None;
        }
        self.grid.get(pos.y as usize)?.get(pos.x as usize).copied()
    }
}

/// Event: Cell has collapsed
#[derive(Event)]
pub struct CellCollapsedEvent {
    pub position: IVec2,
    pub tile: TileId,
    pub entropy_before: f32,
}

/// Event: Contradiction detected
#[derive(Event)]
pub struct ContradictionEvent {
    pub position: IVec2,
}

/// Event: Generation complete
#[derive(Event)]
pub struct GenerationCompleteEvent {
    pub steps: usize,
    pub width: usize,
    pub height: usize,
}

/// Initialize WFC grid with all possibilities
pub fn initialize_wfc_grid(
    mut commands: Commands,
    tileset: Res<TileSet>,
    mut gen_state: ResMut<WfcGenerationState>,
) {
    if !gen_state.grid.is_empty() {
        return; // Already initialized
    }

    let all_tiles: HashSet<TileId> = tileset.tile_ids().into_iter().collect();
    let mut grid = Vec::new();

    for y in 0..gen_state.height {
        let mut row = Vec::new();
        for x in 0..gen_state.width {
            let noise = gen_state.rng.gen::<f32>();
            let cell = WfcCell::new(IVec2::new(x as i32, y as i32), all_tiles.clone(), noise);

            let entity = commands.spawn(cell).id();
            row.push(entity);
        }
        grid.push(row);
    }

    gen_state.grid = grid;
    info!("WFC grid initialized: {}x{}", gen_state.width, gen_state.height);
}

/// WFC Step 1: Observe - find minimum entropy cell
pub fn wfc_observe_step(
    mut gen_state: ResMut<WfcGenerationState>,
    cells: Query<(&WfcCell, Entity)>,
) {
    if gen_state.complete || gen_state.failed {
        return;
    }

    // Find uncollapsed cell with minimum entropy
    let min_cell = cells
        .iter()
        .filter(|(cell, _)| !cell.collapsed && !cell.possibilities.is_empty())
        .min_by(|(a, _), (b, _)| {
            a.entropy
                .partial_cmp(&b.entropy)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

    if min_cell.is_none() {
        // All cells collapsed - generation complete!
        gen_state.complete = true;
    }
}

/// WFC Step 2: Collapse - collapse minimum entropy cell
pub fn wfc_collapse_step(
    mut gen_state: ResMut<WfcGenerationState>,
    tileset: Res<TileSet>,
    mut cells: Query<&mut WfcCell>,
    mut collapse_events: EventWriter<CellCollapsedEvent>,
) {
    if gen_state.complete || gen_state.failed {
        return;
    }

    // Build tile weights
    let tile_weights: HashMap<TileId, f32> = tileset
        .tiles
        .iter()
        .map(|(id, tile)| (*id, tile.weight))
        .collect();

    // Find minimum entropy uncollapsed cell
    let mut min_cell_data: Option<(Entity, IVec2, f32)> = None;
    let mut min_entropy = f32::INFINITY;

    for (entity, cell) in cells.iter().enumerate() {
        if !cell.collapsed && !cell.possibilities.is_empty() && cell.entropy < min_entropy {
            min_entropy = cell.entropy;
            if let Some(e) = gen_state.grid.iter().flatten().nth(entity) {
                min_cell_data = Some((*e, cell.position, cell.entropy));
            }
        }
    }

    if let Some((entity, position, entropy_before)) = min_cell_data {
        if let Ok(mut cell) = cells.get_mut(entity) {
            if let Some(chosen_tile) = cell.collapse(&tile_weights, &mut gen_state.rng) {
                collapse_events.send(CellCollapsedEvent {
                    position,
                    tile: chosen_tile,
                    entropy_before,
                });

                gen_state.step += 1;
            }
        }
    }
}

/// WFC Step 3: Propagate - update neighbor constraints
pub fn wfc_propagate_step(
    gen_state: Res<WfcGenerationState>,
    constraints: Res<ConstraintGraph>,
    tileset: Res<TileSet>,
    mut cells: Query<&mut WfcCell>,
    mut collapse_events: EventReader<CellCollapsedEvent>,
    mut contradiction_events: EventWriter<ContradictionEvent>,
) {
    let tile_weights: HashMap<TileId, f32> = tileset
        .tiles
        .iter()
        .map(|(id, tile)| (*id, tile.weight))
        .collect();

    for event in collapse_events.read() {
        // BFS propagation from collapsed cell
        let mut queue: VecDeque<IVec2> = VecDeque::new();
        let mut visited: HashSet<IVec2> = HashSet::new();

        queue.push_back(event.position);

        while let Some(pos) = queue.pop_front() {
            if visited.contains(&pos) {
                continue;
            }
            visited.insert(pos);

            // Get current cell's possibilities
            let current_entity = match gen_state.get_entity(pos) {
                Some(e) => e,
                None => continue,
            };

            let current_possibilities: HashSet<TileId> = match cells.get(current_entity) {
                Ok(cell) => cell.possibilities.clone(),
                Err(_) => continue,
            };

            // Propagate to all neighbors
            for direction in Direction::all() {
                let neighbor_pos = pos + direction.offset();
                let neighbor_entity = match gen_state.get_entity(neighbor_pos) {
                    Some(e) => e,
                    None => continue,
                };

                if let Ok(mut neighbor) = cells.get_mut(neighbor_entity) {
                    if neighbor.collapsed {
                        continue;
                    }

                    // Calculate allowed tiles for neighbor based on current cell
                    let allowed: HashSet<TileId> = current_possibilities
                        .iter()
                        .flat_map(|&tile| constraints.get_allowed(tile, direction))
                        .collect();

                    // Constrain neighbor
                    let changed = neighbor.constrain(&allowed);

                    // Check for contradiction
                    if neighbor.possibilities.is_empty() {
                        contradiction_events.send(ContradictionEvent {
                            position: neighbor_pos,
                        });
                        return;
                    }

                    // If changed, add to queue for further propagation
                    if changed {
                        neighbor.calculate_entropy(&tile_weights);
                        queue.push_back(neighbor_pos);
                    }
                }
            }
        }
    }
}

/// Handle contradictions (for now, just mark as failed)
pub fn handle_contradictions(
    mut gen_state: ResMut<WfcGenerationState>,
    mut contradiction_events: EventReader<ContradictionEvent>,
) {
    for event in contradiction_events.read() {
        warn!("WFC contradiction at {:?}", event.position);
        gen_state.failed = true;
    }
}

/// Check for completion and emit event
pub fn check_generation_complete(
    gen_state: Res<WfcGenerationState>,
    cells: Query<&WfcCell>,
    mut complete_events: EventWriter<GenerationCompleteEvent>,
) {
    if gen_state.complete {
        let all_collapsed = cells.iter().all(|cell| cell.collapsed);
        if all_collapsed {
            complete_events.send(GenerationCompleteEvent {
                steps: gen_state.step,
                width: gen_state.width,
                height: gen_state.height,
            });

            info!(
                "✅ WFC generation complete! Steps: {}, Size: {}x{}",
                gen_state.step, gen_state.width, gen_state.height
            );
        }
    }
}
