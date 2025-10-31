use bevy::prelude::*;
use std::collections::HashMap;

/// Temporal Layering System - Navigate puzzles across time dimensions
/// 
/// This mechanic allows players to view and manipulate puzzles across
/// different temporal states, seeing how patterns evolve and finding
/// solutions that only exist when considering multiple timeframes.
pub struct TemporalLayerPlugin;

impl Plugin for TemporalLayerPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(TemporalField::default())
            .insert_resource(ChronoNavigator::default())
            .add_event::<TemporalShiftEvent>()
            .add_event::<ParadoxEvent>()
            .add_systems(Update, (
                update_temporal_field,
                handle_temporal_navigation,
                detect_temporal_patterns,
                resolve_paradoxes,
                render_temporal_echoes,
            ).chain());
    }
}

/// The temporal field containing all time layers
#[derive(Resource)]
pub struct TemporalField {
    pub layers: Vec<TimeLayer>,
    pub active_layer: usize,
    pub visible_layers: Vec<usize>,
    pub temporal_links: HashMap<(usize, Entity), Vec<(usize, Entity)>>,
    pub chrono_stability: f32,
}

impl Default for TemporalField {
    fn default() -> Self {
        Self {
            layers: vec![TimeLayer::present()],
            active_layer: 0,
            visible_layers: vec![0],
            temporal_links: HashMap::new(),
            chrono_stability: 1.0,
        }
    }
}

/// A single layer in time
#[derive(Clone)]
pub struct TimeLayer {
    pub index: usize,
    pub time_offset: f32, // Relative to present (negative = past, positive = future)
    pub entities: Vec<TemporalEntity>,
    pub causality_locked: bool,
    pub entropy: f32,
}

impl TimeLayer {
    fn present() -> Self {
        Self {
            index: 0,
            time_offset: 0.0,
            entities: Vec::new(),
            causality_locked: false,
            entropy: 0.0,
        }
    }
}

/// Entity existing in a temporal layer
#[derive(Clone)]
pub struct TemporalEntity {
    pub entity_id: Entity,
    pub state: EntityState,
    pub causal_dependencies: Vec<CausalLink>,
    pub probability: f32, // For quantum superposition
}

#[derive(Clone)]
pub struct EntityState {
    pub position: Vec3,
    pub rotation: Quat,
    pub scale: Vec3,
    pub pattern_data: Option<PatternState>,
}

#[derive(Clone)]
pub struct PatternState {
    pub grid: Vec<Vec<bool>>,
    pub evolution_rule: EvolutionRule,
}

#[derive(Clone)]
pub enum EvolutionRule {
    Static,
    Conway, // Game of Life rules
    Quantum, // Probabilistic evolution
    Crystalline, // Growth patterns
    Entropic, // Decay over time
}

#[derive(Clone)]
pub struct CausalLink {
    pub source_layer: usize,
    pub source_entity: Entity,
    pub link_type: CausalType,
    pub strength: f32,
}

#[derive(Clone)]
pub enum CausalType {
    Direct,      // Direct cause-effect
    Butterfly,   // Small change, large effect
    Stable,      // Maintains consistency
    Paradoxical, // Creates temporal paradox
}

/// Navigator for moving through time
#[derive(Resource, Default)]
pub struct ChronoNavigator {
    pub position: f32, // Current time position
    pub velocity: f32, // Rate of time travel
    pub anchors: Vec<TemporalAnchor>, // Save points in time
    pub max_range: f32,
    pub energy: f32,
}

#[derive(Clone)]
pub struct TemporalAnchor {
    pub name: String,
    pub time_position: f32,
    pub layer_snapshot: TimeLayer,
}

/// Component for entities that exist across time
#[derive(Component)]
pub struct TemporalObject {
    pub exists_in_layers: Vec<usize>,
    pub temporal_signature: TemporalSignature,
    pub is_paradox_immune: bool,
}

#[derive(Clone)]
pub struct TemporalSignature {
    pub frequency: f32,
    pub phase: f32,
    pub quantum_state: QuantumState,
}

#[derive(Clone)]
pub enum QuantumState {
    Collapsed,
    Superposition(Vec<f32>), // Probability amplitudes
    Entangled(Entity),
}

/// Event for temporal navigation
#[derive(Event)]
pub struct TemporalShiftEvent {
    pub target_layer: usize,
    pub shift_type: ShiftType,
}

#[derive(Clone)]
pub enum ShiftType {
    Jump,        // Instant jump
    Slide,       // Smooth transition
    Fork,        // Create alternate timeline
    Merge,       // Combine timelines
}

/// Event for temporal paradoxes
#[derive(Event)]
pub struct ParadoxEvent {
    pub paradox_type: ParadoxType,
    pub affected_layers: Vec<usize>,
    pub severity: f32,
}

#[derive(Clone)]
pub enum ParadoxType {
    CausalLoop,      // A causes B causes A
    Grandfather,     // Preventing own existence
    Bootstrap,       // Information from nowhere
    Butterfly,       // Minor change cascades
}

/// Update the temporal field
fn update_temporal_field(
    mut field: ResMut<TemporalField>,
    time: Res<Time>,
    temporal_objects: Query<&TemporalObject>,
) {
    // Update entropy in each layer
    for layer in &mut field.layers {
        layer.entropy += time.delta_secs() * 0.01;
        
        // Evolve patterns based on their rules
        for entity in &mut layer.entities {
            if let Some(ref mut pattern) = entity.state.pattern_data {
                evolve_pattern(pattern, time.delta_secs());
            }
        }
    }
    
    // Update chrono stability based on paradoxes
    field.chrono_stability = (field.chrono_stability + 0.01).min(1.0);
}

/// Handle player navigation through time
fn handle_temporal_navigation(
    mut navigator: ResMut<ChronoNavigator>,
    mut field: ResMut<TemporalField>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut shift_events: EventWriter<TemporalShiftEvent>,
    time: Res<Time>,
) {
    // Navigate with arrow keys
    if keyboard.pressed(KeyCode::ArrowLeft) {
        navigator.position -= navigator.velocity * time.delta_secs();
        navigator.position = navigator.position.max(-navigator.max_range);
    }
    
    if keyboard.pressed(KeyCode::ArrowRight) {
        navigator.position += navigator.velocity * time.delta_secs();
        navigator.position = navigator.position.min(navigator.max_range);
    }
    
    // Create temporal anchor with T
    if keyboard.just_pressed(KeyCode::KeyT) {
        let current_layer = &field.layers[field.active_layer];
        navigator.anchors.push(TemporalAnchor {
            name: format!("Anchor {}", navigator.anchors.len()),
            time_position: navigator.position,
            layer_snapshot: current_layer.clone(),
        });
        info!("Temporal anchor created at t={:.2}", navigator.position);
    }
    
    // Fork timeline with F
    if keyboard.just_pressed(KeyCode::KeyF) {
        shift_events.send(TemporalShiftEvent {
            target_layer: field.layers.len(),
            shift_type: ShiftType::Fork,
        });
        
        // Create new timeline branch
        let mut new_layer = field.layers[field.active_layer].clone();
        new_layer.index = field.layers.len();
        new_layer.time_offset = navigator.position;
        field.layers.push(new_layer);
        
        info!("Timeline forked at t={:.2}", navigator.position);
    }
}

/// Detect patterns that only exist across time
fn detect_temporal_patterns(
    field: Res<TemporalField>,
    temporal_objects: Query<&TemporalObject>,
) {
    // Look for patterns that span multiple layers
    for (layer_idx, layer) in field.layers.iter().enumerate() {
        for entity in &layer.entities {
            // Check if entity forms pattern with its past/future selves
            if let Some(links) = field.temporal_links.get(&(layer_idx, entity.entity_id)) {
                for (linked_layer, linked_entity) in links {
                    // Pattern detection across time
                    if forms_temporal_pattern(entity, *linked_layer, &field) {
                        info!("Temporal pattern detected across layers {} and {}", layer_idx, linked_layer);
                    }
                }
            }
        }
    }
}

/// Resolve temporal paradoxes
fn resolve_paradoxes(
    mut field: ResMut<TemporalField>,
    mut paradox_events: EventReader<ParadoxEvent>,
) {
    for event in paradox_events.read() {
        match event.paradox_type {
            ParadoxType::CausalLoop => {
                // Break the loop by introducing quantum uncertainty
                field.chrono_stability -= 0.2;
                info!("Causal loop detected! Stability: {:.2}", field.chrono_stability);
            }
            ParadoxType::Grandfather => {
                // Create alternate timeline to resolve
                let mut alternate = field.layers[field.active_layer].clone();
                alternate.causality_locked = true;
                field.layers.push(alternate);
                info!("Grandfather paradox resolved with alternate timeline");
            }
            _ => {}
        }
        
        // If stability too low, collapse to single timeline
        if field.chrono_stability < 0.3 {
            field.layers.retain(|l| l.index == 0);
            field.chrono_stability = 1.0;
            info!("Timeline collapsed due to instability");
        }
    }
}

/// Render visual echoes of other time layers
fn render_temporal_echoes(
    field: Res<TemporalField>,
    mut gizmos: Gizmos,
    time: Res<Time>,
) {
    // Draw echoes from visible layers
    for &layer_idx in &field.visible_layers {
        if layer_idx == field.active_layer {
            continue; // Skip current layer
        }
        
        let layer = &field.layers[layer_idx];
        let alpha = 0.3 * (1.0 - (layer.time_offset.abs() / 10.0).min(1.0));
        
        for entity in &layer.entities {
            // Draw ghostly echo
            let color = if layer.time_offset < 0.0 {
                Color::srgba(0.3, 0.3, 1.0, alpha) // Past = blue
            } else {
                Color::srgba(1.0, 0.3, 0.3, alpha) // Future = red
            };
            
            // Draw temporal echo
            gizmos.sphere(
                Isometry3d::new(entity.state.position, entity.state.rotation),
                0.5,
                color,
            );
            
            // Draw causal links
            for link in &entity.causal_dependencies {
                let link_color = match link.link_type {
                    CausalType::Paradoxical => Color::srgba(1.0, 0.0, 1.0, 0.5),
                    _ => Color::srgba(0.5, 0.5, 0.5, 0.2),
                };
                
                gizmos.line(
                    entity.state.position,
                    entity.state.position + Vec3::Y * link.strength * 2.0,
                    link_color,
                );
            }
        }
    }
    
    // Draw timeline visualization
    let timeline_y = -5.0;
    for layer in &field.layers {
        let x = layer.time_offset * 10.0;
        let color = if layer.causality_locked {
            Color::srgba(1.0, 0.0, 0.0, 0.8)
        } else {
            Color::srgba(0.0, 1.0, 0.0, 0.8)
        };
        
        gizmos.circle_2d(Vec2::new(x, timeline_y), 0.3, color);
    }
}

// Helper functions
fn evolve_pattern(pattern: &mut PatternState, delta: f32) {
    // Apply evolution rules to pattern
    match pattern.evolution_rule {
        EvolutionRule::Conway => {
            // Apply Game of Life rules
        }
        EvolutionRule::Entropic => {
            // Random decay
        }
        _ => {}
    }
}

fn forms_temporal_pattern(entity: &TemporalEntity, other_layer: usize, field: &TemporalField) -> bool {
    // Check if entity states form recognizable pattern across time
    false // Simplified
}