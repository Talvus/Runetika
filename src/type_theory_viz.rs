use bevy::prelude::*;
use std::collections::HashMap;

// Import debug modules
#[cfg(feature = "debug")]
mod type_theory_viz_debug;
#[cfg(feature = "debug")]
mod debug_overlay;
#[cfg(feature = "debug")]
mod type_inspector;

#[cfg(feature = "debug")]
use type_theory_viz_debug::TypeTheoryDebugPlugin;
#[cfg(feature = "debug")]
use debug_overlay::DebugOverlayPlugin;
#[cfg(feature = "debug")]
use type_inspector::TypeInspectorPlugin;

/// Type Theory Visualization System - See and manipulate mathematical reality
/// 
/// This mode reveals the underlying type-theoretical structure of the game world,
/// allowing players to directly manipulate paths, equivalences, and proofs
/// as visual/interactive elements.
/// 
/// With debug features enabled, it also provides powerful introspection tools
/// for development and testing.
pub struct TypeTheoryVizPlugin;

impl Plugin for TypeTheoryVizPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(TypeSpace::default())
            .insert_resource(ProofAssistant::default())
            .add_state::<VizMode>()
            .add_event::<TypeTransformEvent>()
            .add_event::<ProofCompleteEvent>()
            .add_systems(Update, (
                toggle_viz_mode,
                render_type_space,
                manipulate_types,
                construct_proofs,
                verify_equivalences,
            ).chain());
        
        // Add debug plugins when feature is enabled
        #[cfg(feature = "debug")]
        {
            app.add_plugins((
                TypeTheoryDebugPlugin,
                DebugOverlayPlugin,
                TypeInspectorPlugin,
            ));
        }
    }
}

/// Visualization modes
#[derive(States, Default, Debug, Clone, PartialEq, Eq, Hash)]
pub enum VizMode {
    #[default]
    Normal,
    TypeView,
    ProofMode,
    HomotopyView,
}

/// The type space being visualized
#[derive(Resource)]
pub struct TypeSpace {
    pub types: HashMap<TypeId, Type>,
    pub paths: Vec<Path>,
    pub equivalences: Vec<Equivalence>,
    pub active_construction: Option<Construction>,
    pub visualization_level: VisualizationLevel,
}

impl Default for TypeSpace {
    fn default() -> Self {
        Self {
            types: HashMap::new(),
            paths: Vec::new(),
            equivalences: Vec::new(),
            active_construction: None,
            visualization_level: VisualizationLevel::Basic,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

/// A type in the type theory
#[derive(Clone)]
pub struct Type {
    pub id: TypeId,
    pub kind: TypeKind,
    pub level: UniverseLevel,
    pub visual: TypeVisual,
}

#[derive(Clone)]
pub enum TypeKind {
    // Basic types
    Unit,
    Bool,
    Natural,
    
    // Type constructors
    Product(Box<Type>, Box<Type>),
    Sum(Box<Type>, Box<Type>),
    Function(Box<Type>, Box<Type>),
    
    // Higher types
    Identity(Box<Type>, Term, Term),
    Path(Box<Type>, Term, Term),
    
    // Inductive types
    Inductive(InductiveType),
    
    // Cubical types
    Interval,
    Cube(usize), // n-dimensional cube
}

#[derive(Clone)]
pub struct InductiveType {
    pub name: String,
    pub constructors: Vec<Constructor>,
    pub eliminator: Eliminator,
}

#[derive(Clone)]
pub struct Constructor {
    pub name: String,
    pub arguments: Vec<Type>,
}

#[derive(Clone)]
pub struct Eliminator {
    pub motive: Box<Type>,
    pub methods: Vec<Method>,
}

#[derive(Clone)]
pub struct Method {
    pub constructor: String,
    pub implementation: Term,
}

#[derive(Clone)]
pub struct Term {
    pub expression: Expression,
    pub type_annotation: Option<Box<Type>>,
}

#[derive(Clone)]
pub enum Expression {
    Variable(String),
    Lambda(String, Box<Term>),
    Application(Box<Term>, Box<Term>),
    Constructor(String, Vec<Term>),
    Projection(ProjectionType),
}

#[derive(Clone)]
pub enum ProjectionType {
    First,
    Second,
}

#[derive(Clone, Copy)]
pub struct UniverseLevel(pub u32);

/// Visual representation of a type
#[derive(Clone)]
pub struct TypeVisual {
    pub shape: Shape,
    pub color: Color,
    pub position: Vec3,
    pub connections: Vec<TypeId>,
}

#[derive(Clone)]
pub enum Shape {
    Point,
    Line,
    Square,
    Cube,
    Hypercube(usize),
    Torus,
    Custom(Mesh2d),
}

/// A path between terms
#[derive(Clone)]
pub struct Path {
    pub id: PathId,
    pub source: Term,
    pub target: Term,
    pub path_type: PathType,
    pub visualization: PathVisualization,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PathId(pub u32);

#[derive(Clone)]
pub enum PathType {
    Direct,           // Simple path
    Composite(Vec<PathId>), // Composition of paths
    Inverse(Box<Path>), // Inverse path
    Constant,         // Reflexivity
    Transport(Box<Path>, Term), // Transport along a path
}

#[derive(Clone)]
pub struct PathVisualization {
    pub points: Vec<Vec3>,
    pub interpolation: InterpolationType,
    pub animation_speed: f32,
}

#[derive(Clone)]
pub enum InterpolationType {
    Linear,
    Bezier,
    Smooth,
}

/// An equivalence between types
#[derive(Clone)]
pub struct Equivalence {
    pub type_a: TypeId,
    pub type_b: TypeId,
    pub forward: Path,
    pub backward: Path,
    pub proof: Option<EquivalenceProof>,
}

#[derive(Clone)]
pub struct EquivalenceProof {
    pub left_inverse: Path,
    pub right_inverse: Path,
    pub coherence: Option<CoherenceProof>,
}

#[derive(Clone)]
pub struct CoherenceProof {
    pub higher_path: Path,
}

/// Active type construction
#[derive(Clone)]
pub struct Construction {
    pub goal: ConstructionGoal,
    pub steps: Vec<ConstructionStep>,
    pub current_context: Context,
}

#[derive(Clone)]
pub enum ConstructionGoal {
    ProveEquivalence(TypeId, TypeId),
    ConstructPath(Term, Term),
    BuildType(TypeKind),
    SolveEquation(Equation),
}

#[derive(Clone)]
pub struct Equation {
    pub left: Term,
    pub right: Term,
    pub context: Context,
}

#[derive(Clone)]
pub struct ConstructionStep {
    pub action: ConstructionAction,
    pub justification: String,
    pub result: Option<Term>,
}

#[derive(Clone)]
pub enum ConstructionAction {
    Introduce(String, Type),
    Apply(Term, Term),
    Rewrite(Path),
    Induction(InductiveType),
    Reflexivity,
    Symmetry,
    Transitivity(Path, Path),
}

#[derive(Clone, Default)]
pub struct Context {
    pub variables: HashMap<String, Type>,
    pub assumptions: Vec<Term>,
}

#[derive(Clone)]
pub enum VisualizationLevel {
    Basic,       // Just types and simple paths
    Intermediate, // Include equivalences
    Advanced,    // Full cubical structure
    Expert,      // Higher dimensional visualization
}

/// Proof assistant for guided construction
#[derive(Resource, Default)]
pub struct ProofAssistant {
    pub tactics: Vec<Tactic>,
    pub hints: Vec<Hint>,
    pub automation_level: AutomationLevel,
}

#[derive(Clone)]
pub struct Tactic {
    pub name: String,
    pub description: String,
    pub applicability: TacticCondition,
    pub effect: TacticEffect,
}

#[derive(Clone)]
pub enum TacticCondition {
    Always,
    GoalMatches(String), // Pattern
    InContext(String),   // Variable exists
}

#[derive(Clone)]
pub enum TacticEffect {
    Simplify,
    SplitGoal,
    ApplyLemma(String),
    Compute,
}

#[derive(Clone)]
pub struct Hint {
    pub trigger: HintTrigger,
    pub message: String,
    pub suggestion: Option<ConstructionAction>,
}

#[derive(Clone)]
pub enum HintTrigger {
    StuckFor(f32), // Seconds
    WrongPath,
    NearSolution,
}

#[derive(Clone, Default)]
pub enum AutomationLevel {
    #[default]
    None,
    Basic,    // Auto-apply simple tactics
    Advanced, // Solve routine proofs automatically
}

/// Events
#[derive(Event)]
pub struct TypeTransformEvent {
    pub transform: TypeTransform,
    pub source: TypeId,
    pub target: Option<TypeId>,
}

#[derive(Clone)]
pub enum TypeTransform {
    Univalence(Equivalence),
    Transport(Path, Term),
    Composition(Vec<Path>),
    KanFilling(Cube),
}

#[derive(Clone)]
pub struct Cube {
    pub dimension: usize,
    pub faces: Vec<Face>,
    pub filler: Option<Term>,
}

#[derive(Clone)]
pub struct Face {
    pub dimension: usize,
    pub orientation: Orientation,
    pub content: Term,
}

#[derive(Clone)]
pub enum Orientation {
    Positive,
    Negative,
}

#[derive(Event)]
pub struct ProofCompleteEvent {
    pub proof: Proof,
    pub goal: ConstructionGoal,
}

#[derive(Clone)]
pub struct Proof {
    pub steps: Vec<ProofStep>,
    pub conclusion: Term,
    pub validity: ValidityStatus,
}

#[derive(Clone)]
pub struct ProofStep {
    pub premise: Term,
    pub rule: InferenceRule,
    pub conclusion: Term,
}

#[derive(Clone)]
pub enum InferenceRule {
    ModusPonens,
    Universal instantiation,
    Existential(String),
    Induction,
    Computation,
}

#[derive(Clone)]
pub enum ValidityStatus {
    Valid,
    Invalid(String), // Reason
    Unchecked,
}

/// Toggle visualization mode
fn toggle_viz_mode(
    current_state: Res<State<VizMode>>,
    mut next_state: ResMut<NextState<VizMode>>,
    keyboard: Res<ButtonInput<KeyCode>>,
) {
    if keyboard.just_pressed(KeyCode::KeyV) {
        let next = match current_state.get() {
            VizMode::Normal => VizMode::TypeView,
            VizMode::TypeView => VizMode::ProofMode,
            VizMode::ProofMode => VizMode::HomotopyView,
            VizMode::HomotopyView => VizMode::Normal,
        };
        next_state.set(next);
        info!("Switched to {:?} mode", next);
    }
}

/// Render the type space visualization
fn render_type_space(
    type_space: Res<TypeSpace>,
    viz_mode: Res<State<VizMode>>,
    mut gizmos: Gizmos,
    time: Res<Time>,
) {
    if *viz_mode.get() == VizMode::Normal {
        return;
    }
    
    // Render types as shapes
    for (type_id, typ) in &type_space.types {
        let visual = &typ.visual;
        
        // Draw type shape
        match &visual.shape {
            Shape::Point => {
                gizmos.sphere(
                    Isometry3d::from_translation(visual.position),
                    0.2,
                    visual.color,
                );
            }
            Shape::Cube => {
                gizmos.cuboid(
                    Transform::from_translation(visual.position),
                    visual.color,
                );
            }
            _ => {} // Other shapes
        }
        
        // Draw connections
        for connected_id in &visual.connections {
            if let Some(connected) = type_space.types.get(connected_id) {
                gizmos.line(
                    visual.position,
                    connected.visual.position,
                    Color::srgba(0.5, 0.5, 0.5, 0.3),
                );
            }
        }
    }
    
    // Render paths
    for path in &type_space.paths {
        render_path(path, &mut gizmos, time.elapsed_secs());
    }
    
    // Render equivalences
    if matches!(type_space.visualization_level, VisualizationLevel::Intermediate | VisualizationLevel::Advanced | VisualizationLevel::Expert) {
        for equiv in &type_space.equivalences {
            render_equivalence(equiv, &type_space, &mut gizmos);
        }
    }
}

/// Handle type manipulation
fn manipulate_types(
    mut type_space: ResMut<TypeSpace>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut transform_events: EventWriter<TypeTransformEvent>,
) {
    // Example: Create product type with P key
    if keyboard.just_pressed(KeyCode::KeyP) {
        if type_space.types.len() >= 2 {
            // Create product of first two types
            let types: Vec<_> = type_space.types.values().take(2).cloned().collect();
            let product = Type {
                id: TypeId(type_space.types.len() as u32),
                kind: TypeKind::Product(Box::new(types[0].clone()), Box::new(types[1].clone())),
                level: UniverseLevel(0),
                visual: TypeVisual {
                    shape: Shape::Square,
                    color: Color::srgb(0.5, 0.5, 1.0),
                    position: Vec3::new(0.0, 2.0, 0.0),
                    connections: vec![types[0].id, types[1].id],
                },
            };
            
            let product_id = product.id;
            type_space.types.insert(product_id, product);
            
            transform_events.send(TypeTransformEvent {
                transform: TypeTransform::Composition(vec![]),
                source: types[0].id,
                target: Some(product_id),
            });
            
            info!("Created product type");
        }
    }
}

/// Construct proofs interactively
fn construct_proofs(
    mut type_space: ResMut<TypeSpace>,
    assistant: Res<ProofAssistant>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut proof_events: EventWriter<ProofCompleteEvent>,
) {
    if let Some(ref mut construction) = type_space.active_construction {
        // Apply tactics with number keys
        for (i, tactic) in assistant.tactics.iter().enumerate() {
            if keyboard.just_pressed(match i {
                0 => KeyCode::Digit1,
                1 => KeyCode::Digit2,
                2 => KeyCode::Digit3,
                _ => continue,
            }) {
                // Apply tactic
                let step = ConstructionStep {
                    action: ConstructionAction::Reflexivity, // Simplified
                    justification: tactic.description.clone(),
                    result: None,
                };
                construction.steps.push(step);
                info!("Applied tactic: {}", tactic.name);
            }
        }
        
        // Check if proof is complete
        if construction.steps.len() > 5 { // Simplified condition
            let proof = Proof {
                steps: vec![], // Would convert construction steps
                conclusion: Term {
                    expression: Expression::Variable("QED".to_string()),
                    type_annotation: None,
                },
                validity: ValidityStatus::Valid,
            };
            
            proof_events.send(ProofCompleteEvent {
                proof,
                goal: construction.goal.clone(),
            });
            
            type_space.active_construction = None;
            info!("Proof complete!");
        }
    }
}

/// Verify type equivalences
fn verify_equivalences(
    type_space: Res<TypeSpace>,
    mut gizmos: Gizmos,
) {
    for equiv in &type_space.equivalences {
        if equiv.proof.is_some() {
            // Draw verified equivalence
            if let (Some(type_a), Some(type_b)) = (
                type_space.types.get(&equiv.type_a),
                type_space.types.get(&equiv.type_b),
            ) {
                // Draw double arrow for equivalence
                let mid = (type_a.visual.position + type_b.visual.position) / 2.0;
                gizmos.arrow(
                    type_a.visual.position,
                    mid,
                    Color::srgb(0.0, 1.0, 0.0),
                );
                gizmos.arrow(
                    type_b.visual.position,
                    mid,
                    Color::srgb(0.0, 1.0, 0.0),
                );
            }
        }
    }
}

// Helper functions
fn render_path(path: &Path, gizmos: &mut Gizmos, time: f32) {
    let viz = &path.visualization;
    
    // Animate path
    let t = (time * viz.animation_speed) % 1.0;
    
    for i in 0..viz.points.len() - 1 {
        let alpha = if i as f32 / viz.points.len() as f32 <= t {
            1.0
        } else {
            0.3
        };
        
        gizmos.line(
            viz.points[i],
            viz.points[i + 1],
            Color::srgba(1.0, 0.5, 0.0, alpha),
        );
    }
}

fn render_equivalence(equiv: &Equivalence, type_space: &TypeSpace, gizmos: &mut Gizmos) {
    // Render equivalence as a special visualization
    if let (Some(type_a), Some(type_b)) = (
        type_space.types.get(&equiv.type_a),
        type_space.types.get(&equiv.type_b),
    ) {
        let color = if equiv.proof.is_some() {
            Color::srgb(0.0, 1.0, 0.0) // Proven
        } else {
            Color::srgb(1.0, 1.0, 0.0) // Conjectured
        };
        
        // Draw bidirectional connection
        gizmos.line(
            type_a.visual.position,
            type_b.visual.position,
            color.with_alpha(0.5),
        );
    }
}