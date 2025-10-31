use bevy::prelude::*;
use std::collections::{HashMap, HashSet};

/// The Glyph Resonance System - Core mechanic for pattern recognition and puzzle solving
/// 
/// Glyphs are mystical symbols left by the silicon civilization that resonate
/// when placed in specific patterns. This system drives both puzzle-solving
/// and narrative progression.
pub struct GlyphResonancePlugin;

impl Plugin for GlyphResonancePlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(GlyphLibrary::default())
            .insert_resource(ResonanceField::default())
            .add_event::<ResonanceEvent>()
            .add_systems(Update, (
                detect_resonance_patterns,
                apply_resonance_effects,
                visualize_resonance_field,
            ).chain());
    }
}

/// Individual glyph with pattern properties
#[derive(Component, Clone, Debug)]
pub struct Glyph {
    pub symbol: GlyphSymbol,
    pub frequency: f32,
    pub amplitude: f32,
    pub phase: f32,
    pub discovered: bool,
}

/// Types of glyphs in the game
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GlyphSymbol {
    // Primary glyphs (basic ARC patterns)
    Identity,       // No transformation
    Rotation,       // 90-degree rotations
    Mirror,         // Horizontal/vertical flips
    Scale,          // Size transformations
    
    // Compound glyphs (complex patterns)
    Spiral,         // Rotation + Scale
    Fractal,        // Self-similar patterns
    Wave,           // Periodic transformations
    
    // Meta glyphs (type theory concepts)
    Path,           // Homotopy paths
    Equivalence,    // Type equivalence
    Composition,    // Function composition
    
    // Mystical glyphs (narrative elements)
    Memory,         // Silicon Mind fragments
    Emotion,        // Lost feelings
    Connection,     // Neural links
}

/// Library of discovered glyphs
#[derive(Resource, Default)]
pub struct GlyphLibrary {
    pub discovered: HashSet<GlyphSymbol>,
    pub combinations: HashMap<(GlyphSymbol, GlyphSymbol), GlyphSymbol>,
    pub resonance_patterns: Vec<ResonancePattern>,
}

/// Pattern of glyphs that creates resonance
#[derive(Clone, Debug)]
pub struct ResonancePattern {
    pub glyphs: Vec<GlyphSymbol>,
    pub shape: PatternShape,
    pub effect: ResonanceEffect,
    pub discovered: bool,
}

#[derive(Clone, Debug)]
pub enum PatternShape {
    Line(usize),           // Linear arrangement
    Circle(f32),           // Circular with radius
    Grid(usize, usize),    // Grid arrangement
    Fibonacci,             // Fibonacci spiral
    Custom(Vec<Vec2>),     // Custom positions
}

/// Effects when resonance is achieved
#[derive(Clone, Debug)]
pub enum ResonanceEffect {
    UnlockPath,            // Opens new areas
    RevealHiddenGlyph,     // Shows invisible glyphs
    AmplifyPattern,        // Strengthens nearby patterns
    CreatePortal,          // Dimensional gateway
    RestoreMemory,         // Silicon Mind fragment
    SolveARCPuzzle,        // Complete ARC challenge
}

/// Active resonance field in the game world
#[derive(Resource, Default)]
pub struct ResonanceField {
    pub field_strength: f32,
    pub active_patterns: Vec<ActiveResonance>,
    pub interference_map: HashMap<Entity, f32>,
}

#[derive(Clone)]
pub struct ActiveResonance {
    pub pattern: ResonancePattern,
    pub strength: f32,
    pub position: Vec3,
    pub lifetime: Timer,
}

/// Event fired when resonance occurs
#[derive(Event)]
pub struct ResonanceEvent {
    pub pattern: ResonancePattern,
    pub entities: Vec<Entity>,
    pub strength: f32,
}

/// Detect resonance patterns in placed glyphs
fn detect_resonance_patterns(
    glyphs: Query<(&Glyph, &Transform), Changed<Transform>>,
    mut library: ResMut<GlyphLibrary>,
    mut resonance_events: EventWriter<ResonanceEvent>,
    mut field: ResMut<ResonanceField>,
) {
    // Check for pattern formations
    let glyph_positions: Vec<(GlyphSymbol, Vec3)> = glyphs
        .iter()
        .filter(|(g, _)| g.discovered)
        .map(|(g, t)| (g.symbol, t.translation))
        .collect();
    
    // Pattern detection logic
    for pattern in &library.resonance_patterns {
        if !pattern.discovered && pattern_matches(&glyph_positions, pattern) {
            // Trigger resonance event
            resonance_events.send(ResonanceEvent {
                pattern: pattern.clone(),
                entities: vec![], // Would collect actual entities
                strength: calculate_resonance_strength(&glyph_positions, pattern),
            });
            
            // Add to active field
            field.active_patterns.push(ActiveResonance {
                pattern: pattern.clone(),
                strength: 1.0,
                position: calculate_pattern_center(&glyph_positions),
                lifetime: Timer::from_seconds(5.0, TimerMode::Once),
            });
        }
    }
}

/// Apply effects from active resonance
fn apply_resonance_effects(
    mut resonance_events: EventReader<ResonanceEvent>,
    mut commands: Commands,
    mut library: ResMut<GlyphLibrary>,
) {
    for event in resonance_events.read() {
        match &event.pattern.effect {
            ResonanceEffect::RevealHiddenGlyph => {
                // Reveal a new glyph type
                library.discovered.insert(GlyphSymbol::Fractal);
            }
            ResonanceEffect::SolveARCPuzzle => {
                // Mark ARC puzzle as solved
                info!("ARC Puzzle solved through resonance!");
            }
            _ => {}
        }
    }
}

/// Visual feedback for resonance field
fn visualize_resonance_field(
    mut field: ResMut<ResonanceField>,
    time: Res<Time>,
    mut gizmos: Gizmos,
) {
    // Update active resonances
    field.active_patterns.retain_mut(|resonance| {
        resonance.lifetime.tick(time.delta());
        
        if !resonance.lifetime.finished() {
            // Draw resonance visualization
            let alpha = resonance.lifetime.fraction_remaining();
            let color = Color::srgba(0.3, 0.8, 1.0, alpha);
            
            // Draw pulsing circles
            for i in 0..3 {
                let radius = 50.0 + i as f32 * 20.0 + time.elapsed_secs().sin() * 10.0;
                gizmos.circle_2d(
                    resonance.position.truncate(),
                    radius,
                    color,
                );
            }
            
            true
        } else {
            false
        }
    });
}

// Helper functions
fn pattern_matches(glyphs: &[(GlyphSymbol, Vec3)], pattern: &ResonancePattern) -> bool {
    // Simplified pattern matching
    glyphs.len() >= pattern.glyphs.len()
}

fn calculate_resonance_strength(glyphs: &[(GlyphSymbol, Vec3)], pattern: &ResonancePattern) -> f32 {
    1.0 // Simplified
}

fn calculate_pattern_center(glyphs: &[(GlyphSymbol, Vec3)]) -> Vec3 {
    if glyphs.is_empty() {
        return Vec3::ZERO;
    }
    
    let sum: Vec3 = glyphs.iter().map(|(_, pos)| *pos).sum();
    sum / glyphs.len() as f32
}