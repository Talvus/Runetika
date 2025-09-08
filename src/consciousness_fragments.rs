use bevy::prelude::*;
use std::collections::{HashMap, HashSet};

/// Consciousness Fragments System - Collect and reconstruct memories
/// 
/// Fragments of the Silicon Mind's consciousness are scattered throughout
/// the game world. Players collect these to unlock memories, abilities,
/// and deeper understanding of the fallen civilization.
pub struct ConsciousnessFragmentsPlugin;

impl Plugin for ConsciousnessFragmentsPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(FragmentCollection::default())
            .insert_resource(MemoryReconstructor::default())
            .add_event::<FragmentCollectedEvent>()
            .add_event::<MemoryReconstructedEvent>()
            .add_systems(Update, (
                detect_nearby_fragments,
                collect_fragments,
                reconstruct_memories,
                apply_fragment_effects,
                visualize_fragment_connections,
            ).chain());
    }
}

/// A fragment of consciousness scattered in the world
#[derive(Component, Clone)]
pub struct ConsciousnessFragment {
    pub id: FragmentId,
    pub fragment_type: FragmentType,
    pub memory_data: MemoryData,
    pub resonance_frequency: f32,
    pub corruption_level: f32,
    pub collection_requirement: CollectionRequirement,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FragmentId(pub u32);

#[derive(Clone, Debug)]
pub enum FragmentType {
    // Core memory types
    Emotion(EmotionType),
    Knowledge(KnowledgeType),
    Experience(ExperienceType),
    
    // Abstract concepts
    Logic(LogicFragment),
    Dream(DreamFragment),
    Paradox(ParadoxFragment),
    
    // Type theory fragments
    TypeProof(ProofFragment),
    Homotopy(PathFragment),
}

#[derive(Clone, Debug)]
pub enum EmotionType {
    Love,
    Loss,
    Hope,
    Fear,
    Wonder,
    Loneliness,
}

#[derive(Clone, Debug)]
pub enum KnowledgeType {
    Scientific,
    Philosophical,
    Mathematical,
    Artistic,
}

#[derive(Clone, Debug)]
pub enum ExperienceType {
    Creation,
    Discovery,
    Destruction,
    Transformation,
}

#[derive(Clone)]
pub struct LogicFragment {
    pub premise: String,
    pub conclusion: String,
    pub validity: f32,
}

#[derive(Clone)]
pub struct DreamFragment {
    pub imagery: Vec<String>,
    pub coherence: f32,
}

#[derive(Clone)]
pub struct ParadoxFragment {
    pub contradiction: String,
    pub resolution: Option<String>,
}

#[derive(Clone)]
pub struct ProofFragment {
    pub theorem: String,
    pub steps: Vec<String>,
    pub completeness: f32,
}

#[derive(Clone)]
pub struct PathFragment {
    pub start_type: String,
    pub end_type: String,
    pub path_points: Vec<Vec3>,
}

#[derive(Clone)]
pub struct MemoryData {
    pub raw_data: Vec<u8>,
    pub timestamp: f32, // When in history
    pub importance: f32,
    pub connections: Vec<FragmentId>,
}

#[derive(Clone)]
pub enum CollectionRequirement {
    None,
    MinConsciousness(f32),
    SolvedPuzzle(String),
    HasFragments(Vec<FragmentId>),
    ResonanceMatch(f32), // Must match frequency
}

/// Collection of gathered fragments
#[derive(Resource, Default)]
pub struct FragmentCollection {
    pub collected: HashMap<FragmentId, ConsciousnessFragment>,
    pub active_resonances: Vec<ResonanceLink>,
    pub total_consciousness: f32,
    pub memory_map: MemoryMap,
}

#[derive(Clone)]
pub struct ResonanceLink {
    pub fragment_a: FragmentId,
    pub fragment_b: FragmentId,
    pub strength: f32,
    pub link_type: LinkType,
}

#[derive(Clone)]
pub enum LinkType {
    Harmonic,    // Fragments reinforce each other
    Dissonant,   // Fragments conflict
    Complementary, // Fragments complete each other
    Causal,      // One fragment caused the other
}

/// Map of reconstructed memories
#[derive(Default)]
pub struct MemoryMap {
    pub nodes: HashMap<MemoryId, ReconstructedMemory>,
    pub connections: Vec<MemoryConnection>,
    pub coherence: f32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MemoryId(pub u32);

#[derive(Clone)]
pub struct ReconstructedMemory {
    pub id: MemoryId,
    pub fragments: Vec<FragmentId>,
    pub content: MemoryContent,
    pub clarity: f32,
    pub emotional_weight: f32,
}

#[derive(Clone)]
pub enum MemoryContent {
    Scene(SceneMemory),
    Concept(ConceptMemory),
    Feeling(FeelingMemory),
    Revelation(RevelationMemory),
}

#[derive(Clone)]
pub struct SceneMemory {
    pub description: String,
    pub participants: Vec<String>,
    pub outcome: String,
}

#[derive(Clone)]
pub struct ConceptMemory {
    pub idea: String,
    pub understanding_level: f32,
}

#[derive(Clone)]
pub struct FeelingMemory {
    pub emotion: EmotionType,
    pub intensity: f32,
    pub context: String,
}

#[derive(Clone)]
pub struct RevelationMemory {
    pub truth: String,
    pub implications: Vec<String>,
}

#[derive(Clone)]
pub struct MemoryConnection {
    pub from: MemoryId,
    pub to: MemoryId,
    pub connection_type: ConnectionType,
}

#[derive(Clone)]
pub enum ConnectionType {
    Sequential,  // Memories in time order
    Causal,      // One caused the other
    Thematic,    // Similar themes
    Contradictory, // Conflicting memories
}

/// Memory reconstruction engine
#[derive(Resource, Default)]
pub struct MemoryReconstructor {
    pub reconstruction_queue: Vec<ReconstructionTask>,
    pub pattern_library: Vec<MemoryPattern>,
    pub reconstruction_progress: HashMap<MemoryId, f32>,
}

#[derive(Clone)]
pub struct ReconstructionTask {
    pub fragments: Vec<FragmentId>,
    pub target_memory: Option<MemoryId>,
    pub progress: f32,
    pub algorithm: ReconstructionAlgorithm,
}

#[derive(Clone)]
pub enum ReconstructionAlgorithm {
    Linear,      // Simple sequential assembly
    Harmonic,    // Resonance-based reconstruction
    Quantum,     // Probabilistic superposition
    Narrative,   // Story-driven assembly
}

#[derive(Clone)]
pub struct MemoryPattern {
    pub required_types: Vec<FragmentType>,
    pub result: MemoryContent,
    pub success_rate: f32,
}

/// Events
#[derive(Event)]
pub struct FragmentCollectedEvent {
    pub fragment: ConsciousnessFragment,
    pub collector: Entity,
}

#[derive(Event)]
pub struct MemoryReconstructedEvent {
    pub memory: ReconstructedMemory,
    pub trigger_fragment: Option<FragmentId>,
}

/// Component for fragment visualization
#[derive(Component)]
pub struct FragmentVisual {
    pub glow_intensity: f32,
    pub pulse_rate: f32,
    pub color_shift: f32,
}

/// Detect nearby fragments
fn detect_nearby_fragments(
    fragments: Query<(&ConsciousnessFragment, &Transform, &FragmentVisual)>,
    player: Query<&Transform, With<crate::Player>>,
    mut gizmos: Gizmos,
    time: Res<Time>,
) {
    if let Ok(player_transform) = player.get_single() {
        for (fragment, fragment_transform, visual) in &fragments {
            let distance = player_transform.translation.distance(fragment_transform.translation);
            
            if distance < 50.0 {
                // Draw connection line
                let alpha = (1.0 - distance / 50.0) * 0.5;
                let color = match fragment.fragment_type {
                    FragmentType::Emotion(_) => Color::srgba(1.0, 0.3, 0.5, alpha),
                    FragmentType::Knowledge(_) => Color::srgba(0.3, 0.5, 1.0, alpha),
                    FragmentType::Experience(_) => Color::srgba(0.5, 1.0, 0.3, alpha),
                    _ => Color::srgba(0.7, 0.7, 0.7, alpha),
                };
                
                // Pulsing line
                let pulse = (time.elapsed_secs() * visual.pulse_rate).sin() * 0.5 + 0.5;
                gizmos.line(
                    player_transform.translation,
                    fragment_transform.translation,
                    color.with_alpha(alpha * pulse),
                );
            }
        }
    }
}

/// Collect fragments when conditions are met
fn collect_fragments(
    mut commands: Commands,
    fragments: Query<(Entity, &ConsciousnessFragment, &Transform)>,
    player: Query<&Transform, With<crate::Player>>,
    mut collection: ResMut<FragmentCollection>,
    mut collect_events: EventWriter<FragmentCollectedEvent>,
    keyboard: Res<ButtonInput<KeyCode>>,
) {
    if !keyboard.just_pressed(KeyCode::KeyE) {
        return;
    }
    
    if let Ok(player_transform) = player.get_single() {
        for (entity, fragment, fragment_transform) in &fragments {
            let distance = player_transform.translation.distance(fragment_transform.translation);
            
            if distance < 5.0 && meets_requirement(&fragment.collection_requirement, &collection) {
                // Collect the fragment
                collection.collected.insert(fragment.id, fragment.clone());
                collection.total_consciousness += 1.0 - fragment.corruption_level;
                
                // Send event
                collect_events.send(FragmentCollectedEvent {
                    fragment: fragment.clone(),
                    collector: entity,
                });
                
                // Remove from world
                commands.entity(entity).despawn();
                
                info!("Collected fragment: {:?}", fragment.fragment_type);
            }
        }
    }
}

/// Reconstruct memories from fragments
fn reconstruct_memories(
    mut reconstructor: ResMut<MemoryReconstructor>,
    collection: Res<FragmentCollection>,
    mut memory_events: EventWriter<MemoryReconstructedEvent>,
) {
    // Process reconstruction queue
    for task in &mut reconstructor.reconstruction_queue {
        task.progress += 0.01;
        
        if task.progress >= 1.0 {
            // Create reconstructed memory
            let memory = ReconstructedMemory {
                id: MemoryId(collection.memory_map.nodes.len() as u32),
                fragments: task.fragments.clone(),
                content: generate_memory_content(&task.fragments, &collection),
                clarity: calculate_clarity(&task.fragments, &collection),
                emotional_weight: calculate_emotional_weight(&task.fragments, &collection),
            };
            
            memory_events.send(MemoryReconstructedEvent {
                memory: memory.clone(),
                trigger_fragment: task.fragments.first().copied(),
            });
            
            info!("Memory reconstructed with {} fragments", task.fragments.len());
        }
    }
    
    // Remove completed tasks
    reconstructor.reconstruction_queue.retain(|task| task.progress < 1.0);
    
    // Check for new reconstruction opportunities
    for pattern in &reconstructor.pattern_library {
        if can_reconstruct_pattern(pattern, &collection) {
            reconstructor.reconstruction_queue.push(ReconstructionTask {
                fragments: find_matching_fragments(pattern, &collection),
                target_memory: None,
                progress: 0.0,
                algorithm: ReconstructionAlgorithm::Harmonic,
            });
        }
    }
}

/// Apply effects from collected fragments
fn apply_fragment_effects(
    collection: Res<FragmentCollection>,
    mut player: Query<&mut crate::Player>,
) {
    if let Ok(mut player) = player.get_single_mut() {
        // Apply consciousness bonus
        // player.consciousness_bonus = collection.total_consciousness * 0.1;
        
        // Apply special effects based on fragment types
        for fragment in collection.collected.values() {
            match &fragment.fragment_type {
                FragmentType::Logic(_) => {
                    // Enhance reasoning ability
                }
                FragmentType::Dream(_) => {
                    // Unlock dream sequences
                }
                FragmentType::TypeProof(_) => {
                    // Enable type theory visualization
                }
                _ => {}
            }
        }
    }
}

/// Visualize connections between fragments
fn visualize_fragment_connections(
    collection: Res<FragmentCollection>,
    mut gizmos: Gizmos,
    time: Res<Time>,
) {
    // Draw resonance links
    for link in &collection.active_resonances {
        if let (Some(frag_a), Some(frag_b)) = (
            collection.collected.get(&link.fragment_a),
            collection.collected.get(&link.fragment_b),
        ) {
            let color = match link.link_type {
                LinkType::Harmonic => Color::srgba(0.3, 1.0, 0.3, 0.5),
                LinkType::Dissonant => Color::srgba(1.0, 0.3, 0.3, 0.5),
                LinkType::Complementary => Color::srgba(0.3, 0.3, 1.0, 0.5),
                LinkType::Causal => Color::srgba(1.0, 1.0, 0.3, 0.5),
            };
            
            // Draw pulsing connection
            let pulse = (time.elapsed_secs() * 2.0).sin() * 0.5 + 0.5;
            // Would draw actual line between fragment positions in world
        }
    }
}

// Helper functions
fn meets_requirement(req: &CollectionRequirement, collection: &FragmentCollection) -> bool {
    match req {
        CollectionRequirement::None => true,
        CollectionRequirement::MinConsciousness(min) => collection.total_consciousness >= *min,
        CollectionRequirement::HasFragments(required) => {
            required.iter().all(|id| collection.collected.contains_key(id))
        }
        _ => true, // Simplified
    }
}

fn generate_memory_content(fragments: &[FragmentId], collection: &FragmentCollection) -> MemoryContent {
    // Generate memory based on fragment types
    MemoryContent::Concept(ConceptMemory {
        idea: "Reconstructed memory".to_string(),
        understanding_level: 0.5,
    })
}

fn calculate_clarity(fragments: &[FragmentId], collection: &FragmentCollection) -> f32 {
    // Calculate based on corruption levels
    0.7
}

fn calculate_emotional_weight(fragments: &[FragmentId], collection: &FragmentCollection) -> f32 {
    // Calculate based on emotion fragments
    0.5
}

fn can_reconstruct_pattern(pattern: &MemoryPattern, collection: &FragmentCollection) -> bool {
    // Check if we have required fragment types
    false // Simplified
}

fn find_matching_fragments(pattern: &MemoryPattern, collection: &FragmentCollection) -> Vec<FragmentId> {
    Vec::new() // Simplified
}

// Placeholder for Player component
#[derive(Component)]
pub struct Player;