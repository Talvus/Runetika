use std::collections::HashMap;
use super::pattern::{Grid, Pattern, Color};

#[derive(Clone, Debug)]
pub struct ARCPuzzle {
    pub id: String,
    pub name: String,
    pub description: String,
    pub input_examples: Vec<(Grid, Grid)>,
    pub test_input: Grid,
    pub expected_output: Grid,
    pub rules: Vec<Rule>,
    pub difficulty: Difficulty,
    pub glyph_hint: GlyphHint,
}

#[derive(Clone, Debug)]
pub enum Rule {
    Symmetry(SymmetryType),
    ColorMap(HashMap<Color, Color>),
    PatternFill(Pattern),
    Transformation(Transformation),
    Composite(Vec<Rule>),
}

#[derive(Clone, Debug)]
pub enum Transformation {
    Rotate(i32),
    Mirror(Axis),
    Scale(f32),
    Translate(i32, i32),
    ColorShift(Color, Color),
}

#[derive(Clone, Debug)]
pub enum SymmetryType {
    Horizontal,
    Vertical,
    Diagonal,
    Rotational(u8),
}

#[derive(Clone, Debug)]
pub enum Axis {
    Horizontal,
    Vertical,
    Diagonal,
}

#[derive(Clone, Debug)]
pub enum Difficulty {
    Tutorial,
    Easy,
    Medium,
    Hard,
    Expert,
}

#[derive(Clone, Debug)]
pub struct GlyphHint {
    pub symbol: String,
    pub meaning: String,
    pub resonance_color: Color,
}