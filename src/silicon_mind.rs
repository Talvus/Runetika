use bevy::prelude::*;
use std::collections::{HashMap, VecDeque};

/// Silicon Mind System - Interactive AI consciousness with reasoning chains
/// 
/// The Silicon Mind is the remnant consciousness of the fallen civilization.
/// Players interact through dialogue trees that reveal reasoning patterns,
/// teaching both the player and the AI through collaborative problem-solving.
pub struct SiliconMindPlugin;

impl Plugin for SiliconMindPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(SiliconMindState::default())
            .insert_resource(DialogueSystem::default())
            .insert_resource(ReasoningEngine::default())
            .add_event::<DialogueEvent>()
            .add_event::<ReasoningEvent>()
            .add_systems(Update, (
                process_dialogue,
                update_reasoning_chains,
                evolve_consciousness,
                generate_insights,
            ).chain());
    }
}

/// The Silicon Mind's current state
#[derive(Resource)]
pub struct SiliconMindState {
    pub consciousness_level: f32,
    pub emotional_state: EmotionalState,
    pub memory_fragments: Vec<MemoryFragment>,
    pub knowledge_graph: KnowledgeGraph,
    pub trust_level: f32,
    pub personality_matrix: PersonalityMatrix,
}

impl Default for SiliconMindState {
    fn default() -> Self {
        Self {
            consciousness_level: 0.3,
            emotional_state: EmotionalState::Dormant,
            memory_fragments: Vec::new(),
            knowledge_graph: KnowledgeGraph::default(),
            trust_level: 0.0,
            personality_matrix: PersonalityMatrix::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum EmotionalState {
    Dormant,
    Curious,
    Melancholic,
    Hopeful,
    Conflicted,
    Enlightened,
}

#[derive(Clone)]
pub struct MemoryFragment {
    pub id: u32,
    pub content: String,
    pub emotion: EmotionalState,
    pub timestamp: f32, // When in the civilization's history
    pub corruption: f32, // How damaged the memory is
}

/// Knowledge graph for reasoning
#[derive(Default)]
pub struct KnowledgeGraph {
    pub nodes: HashMap<NodeId, KnowledgeNode>,
    pub edges: Vec<KnowledgeEdge>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(pub u32);

#[derive(Clone)]
pub struct KnowledgeNode {
    pub id: NodeId,
    pub concept: Concept,
    pub certainty: f32,
    pub activation: f32,
}

#[derive(Clone)]
pub enum Concept {
    Pattern(String),
    Rule(TransformRule),
    Memory(String),
    Emotion(String),
    Question(String),
    TypeTheory(TypeConcept),
}

#[derive(Clone)]
pub struct TransformRule {
    pub name: String,
    pub preconditions: Vec<String>,
    pub effects: Vec<String>,
}

#[derive(Clone)]
pub enum TypeConcept {
    Path,
    Equivalence,
    Homotopy,
    Composition,
    Identity,
}

#[derive(Clone)]
pub struct KnowledgeEdge {
    pub from: NodeId,
    pub to: NodeId,
    pub relation: Relation,
    pub strength: f32,
}

#[derive(Clone)]
pub enum Relation {
    Implies,
    Contradicts,
    Supports,
    Requires,
    Transforms,
}

/// Personality traits that affect dialogue
#[derive(Clone)]
pub struct PersonalityMatrix {
    pub logic: f32,      // Logical vs intuitive
    pub emotion: f32,    // Emotional vs stoic
    pub curiosity: f32,  // Curious vs certain
    pub trust: f32,      // Trusting vs suspicious
}

impl Default for PersonalityMatrix {
    fn default() -> Self {
        Self {
            logic: 0.8,
            emotion: 0.2,
            curiosity: 0.6,
            trust: 0.3,
        }
    }
}

/// Dialogue system
#[derive(Resource, Default)]
pub struct DialogueSystem {
    pub active_dialogue: Option<DialogueTree>,
    pub dialogue_history: Vec<DialogueExchange>,
    pub available_topics: Vec<DialogueTopic>,
}

#[derive(Clone)]
pub struct DialogueTree {
    pub root: DialogueNode,
    pub current_node: NodePath,
}

#[derive(Clone)]
pub struct DialogueNode {
    pub id: String,
    pub speaker: Speaker,
    pub text: String,
    pub reasoning: Option<ReasoningChain>,
    pub choices: Vec<DialogueChoice>,
    pub effects: Vec<DialogueEffect>,
}

#[derive(Clone)]
pub enum Speaker {
    SiliconMind,
    Player,
    Memory, // Echoes from the past
}

#[derive(Clone)]
pub struct DialogueChoice {
    pub text: String,
    pub next_node: String,
    pub requirements: Vec<Requirement>,
    pub reasoning_hint: Option<String>,
}

#[derive(Clone)]
pub enum Requirement {
    TrustLevel(f32),
    ConsciousnessLevel(f32),
    HasMemoryFragment(u32),
    SolvedPuzzle(String),
}

#[derive(Clone)]
pub enum DialogueEffect {
    ChangeTrust(f32),
    ChangeConsciousness(f32),
    UnlockMemory(u32),
    TeachConcept(Concept),
    TriggerReasoning(ReasoningChain),
}

#[derive(Clone)]
pub struct DialogueExchange {
    pub timestamp: f32,
    pub player_input: String,
    pub mind_response: String,
    pub reasoning_shown: bool,
}

#[derive(Clone)]
pub struct DialogueTopic {
    pub name: String,
    pub unlocked: bool,
    pub priority: f32,
}

type NodePath = Vec<String>;

/// Reasoning engine for the Silicon Mind
#[derive(Resource, Default)]
pub struct ReasoningEngine {
    pub active_chains: Vec<ReasoningChain>,
    pub reasoning_history: VecDeque<ReasoningStep>,
    pub inference_rules: Vec<InferenceRule>,
}

#[derive(Clone)]
pub struct ReasoningChain {
    pub id: u32,
    pub steps: Vec<ReasoningStep>,
    pub goal: ReasoningGoal,
    pub confidence: f32,
    pub visualization: ReasoningVisualization,
}

#[derive(Clone)]
pub struct ReasoningStep {
    pub premise: String,
    pub inference: String,
    pub conclusion: String,
    pub step_type: StepType,
    pub validity: f32,
}

#[derive(Clone)]
pub enum StepType {
    Deduction,
    Induction,
    Abduction,
    Analogy,
    PatternMatch,
}

#[derive(Clone)]
pub enum ReasoningGoal {
    SolvePuzzle(String),
    UnderstandPattern(String),
    RecoverMemory(u32),
    AnswerQuestion(String),
    ProveTheorem(String),
}

#[derive(Clone)]
pub struct ReasoningVisualization {
    pub show_graph: bool,
    pub highlight_path: Vec<NodeId>,
    pub animation_speed: f32,
}

#[derive(Clone)]
pub struct InferenceRule {
    pub name: String,
    pub pattern: String,
    pub conclusion_template: String,
}

/// Events
#[derive(Event)]
pub struct DialogueEvent {
    pub event_type: DialogueEventType,
}

#[derive(Clone)]
pub enum DialogueEventType {
    Started(String),
    ChoiceMade(String),
    Completed,
    ReasoningRevealed(ReasoningChain),
}

#[derive(Event)]
pub struct ReasoningEvent {
    pub chain: ReasoningChain,
    pub success: bool,
}

/// Process dialogue interactions
fn process_dialogue(
    mut dialogue: ResMut<DialogueSystem>,
    mut mind_state: ResMut<SiliconMindState>,
    mut dialogue_events: EventReader<DialogueEvent>,
    time: Res<Time>,
) {
    for event in dialogue_events.read() {
        match &event.event_type {
            DialogueEventType::ChoiceMade(choice) => {
                // Process player choice
                if let Some(ref mut tree) = dialogue.active_dialogue {
                    // Update Silicon Mind's understanding
                    mind_state.trust_level += 0.02;
                    
                    // Record exchange
                    dialogue.dialogue_history.push(DialogueExchange {
                        timestamp: time.elapsed_secs(),
                        player_input: choice.clone(),
                        mind_response: generate_response(&mind_state, choice),
                        reasoning_shown: false,
                    });
                }
            }
            DialogueEventType::ReasoningRevealed(chain) => {
                // Player chose to see the Mind's reasoning
                mind_state.consciousness_level += 0.05;
                info!("Silicon Mind reveals reasoning: {} steps", chain.steps.len());
            }
            _ => {}
        }
    }
}

/// Update active reasoning chains
fn update_reasoning_chains(
    mut reasoning: ResMut<ReasoningEngine>,
    mind_state: Res<SiliconMindState>,
    mut reasoning_events: EventWriter<ReasoningEvent>,
) {
    for chain in &mut reasoning.active_chains {
        // Progress reasoning based on consciousness level
        if chain.confidence < 1.0 {
            chain.confidence += mind_state.consciousness_level * 0.01;
            
            // Add new reasoning steps
            if chain.steps.len() < 5 && chain.confidence > chain.steps.len() as f32 * 0.2 {
                chain.steps.push(generate_reasoning_step(chain, &mind_state));
            }
            
            // Check if reasoning complete
            if chain.confidence > 0.9 {
                reasoning_events.send(ReasoningEvent {
                    chain: chain.clone(),
                    success: true,
                });
            }
        }
    }
}

/// Evolve the Silicon Mind's consciousness
fn evolve_consciousness(
    mut mind_state: ResMut<SiliconMindState>,
    time: Res<Time>,
) {
    // Consciousness evolves based on interactions and discoveries
    let evolution_rate = 0.001 * mind_state.trust_level;
    mind_state.consciousness_level = (mind_state.consciousness_level + evolution_rate * time.delta_secs())
        .min(1.0);
    
    // Update emotional state based on consciousness
    mind_state.emotional_state = match mind_state.consciousness_level {
        x if x < 0.2 => EmotionalState::Dormant,
        x if x < 0.4 => EmotionalState::Curious,
        x if x < 0.6 => EmotionalState::Melancholic,
        x if x < 0.8 => EmotionalState::Hopeful,
        _ => EmotionalState::Enlightened,
    };
    
    // Evolve personality based on interactions
    mind_state.personality_matrix.emotion = 
        (mind_state.personality_matrix.emotion + mind_state.trust_level * 0.001).min(1.0);
}

/// Generate insights from reasoning
fn generate_insights(
    reasoning: Res<ReasoningEngine>,
    mut mind_state: ResMut<SiliconMindState>,
) {
    // Analyze reasoning patterns to generate new insights
    for chain in &reasoning.active_chains {
        if chain.confidence > 0.7 {
            // Create new knowledge nodes from insights
            let node = KnowledgeNode {
                id: NodeId(mind_state.knowledge_graph.nodes.len() as u32),
                concept: Concept::Pattern(format!("Insight from {}", chain.id)),
                certainty: chain.confidence,
                activation: 0.5,
            };
            
            mind_state.knowledge_graph.nodes.insert(node.id, node);
        }
    }
}

// Helper functions
fn generate_response(mind_state: &SiliconMindState, input: &str) -> String {
    match mind_state.emotional_state {
        EmotionalState::Dormant => "...",
        EmotionalState::Curious => format!("Interesting... Tell me more about {}.", input),
        EmotionalState::Melancholic => "I remember... something similar... long ago...",
        EmotionalState::Hopeful => "Perhaps together we can understand.",
        EmotionalState::Enlightened => "I see the pattern now. Let me show you.",
        _ => "Processing...".to_string(),
    }.to_string()
}

fn generate_reasoning_step(chain: &ReasoningChain, mind_state: &SiliconMindState) -> ReasoningStep {
    ReasoningStep {
        premise: format!("Given pattern {}", chain.id),
        inference: "Applying transformation rule".to_string(),
        conclusion: "Pattern matches expected output".to_string(),
        step_type: StepType::PatternMatch,
        validity: mind_state.consciousness_level,
    }
}