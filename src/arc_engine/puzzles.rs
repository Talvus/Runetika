use super::types::*;
use super::pattern::*;
use std::collections::HashMap;

pub fn get_all_puzzles() -> Vec<ARCPuzzle> {
    vec![
        create_tutorial_puzzle(),
        create_symmetry_puzzle(),
        create_transformation_puzzle(),
        create_composition_puzzle(),
        create_emergence_puzzle(),
    ]
}

pub fn create_tutorial_puzzle() -> ARCPuzzle {
    // Simple 3x3 pattern recognition
    let mut input = Grid::new(3, 3);
    input.cells[0][0] = Cell { color: Color::Blue, symbol: None };
    input.cells[0][2] = Cell { color: Color::Blue, symbol: None };
    input.cells[2][0] = Cell { color: Color::Blue, symbol: None };
    input.cells[2][2] = Cell { color: Color::Blue, symbol: None };
    
    let mut output = input.clone();
    output.cells[1][1] = Cell { color: Color::Blue, symbol: None };
    
    ARCPuzzle {
        id: "tutorial".to_string(),
        name: "Echo of Patterns".to_string(),
        description: "The center seeks harmony with its corners".to_string(),
        input_examples: vec![(input.clone(), output.clone())],
        test_input: input,
        expected_output: output,
        rules: vec![Rule::PatternFill(Pattern {
            template: vec![vec![true, false, true], vec![false, true, false], vec![true, false, true]],
            anchor: (1, 1),
        })],
        difficulty: Difficulty::Tutorial,
        glyph_hint: GlyphHint {
            symbol: "◊".to_string(),
            meaning: "Echo - patterns repeat and resonate".to_string(),
            resonance_color: Color::Blue,
        },
    }
}

pub fn create_symmetry_puzzle() -> ARCPuzzle {
    // 5x5 grid with partial symmetry to complete
    let mut input = Grid::new(5, 5);
    // Left half filled
    for y in 0..5 {
        input.cells[y][0] = Cell { color: Color::Red, symbol: None };
        if y % 2 == 0 {
            input.cells[y][1] = Cell { color: Color::Green, symbol: None };
        }
    }
    
    let mut output = input.clone();
    // Mirror to right
    for y in 0..5 {
        output.cells[y][4] = Cell { color: Color::Red, symbol: None };
        if y % 2 == 0 {
            output.cells[y][3] = Cell { color: Color::Green, symbol: None };
        }
    }
    
    ARCPuzzle {
        id: "symmetry".to_string(),
        name: "Mirror of the Mind".to_string(),
        description: "What exists on one side must balance on the other".to_string(),
        input_examples: vec![(input.clone(), output.clone())],
        test_input: input,
        expected_output: output,
        rules: vec![Rule::Symmetry(SymmetryType::Vertical)],
        difficulty: Difficulty::Easy,
        glyph_hint: GlyphHint {
            symbol: "⧉".to_string(),
            meaning: "Mirror - reflection reveals truth".to_string(),
            resonance_color: Color::Red,
        },
    }
}

pub fn create_transformation_puzzle() -> ARCPuzzle {
    // Rotation pattern
    let mut input = Grid::new(3, 3);
    input.cells[0][0] = Cell { color: Color::Yellow, symbol: None };
    input.cells[0][1] = Cell { color: Color::Yellow, symbol: None };
    input.cells[1][0] = Cell { color: Color::Yellow, symbol: None };
    
    let output = input.rotate(90);
    
    ARCPuzzle {
        id: "transformation".to_string(),
        name: "The Spiral Dance".to_string(),
        description: "All things turn in time".to_string(),
        input_examples: vec![(input.clone(), output.clone())],
        test_input: input,
        expected_output: output,
        rules: vec![Rule::Transformation(Transformation::Rotate(90))],
        difficulty: Difficulty::Easy,
        glyph_hint: GlyphHint {
            symbol: "⟲".to_string(),
            meaning: "Spiral - transformation through rotation".to_string(),
            resonance_color: Color::Yellow,
        },
    }
}

pub fn create_composition_puzzle() -> ARCPuzzle {
    // Color map + symmetry
    let mut input = Grid::new(4, 4);
    input.cells[0][0] = Cell { color: Color::Blue, symbol: None };
    input.cells[0][1] = Cell { color: Color::Red, symbol: None };
    input.cells[1][0] = Cell { color: Color::Red, symbol: None };
    input.cells[1][1] = Cell { color: Color::Blue, symbol: None };
    
    let mut output = Grid::new(4, 4);
    // Apply color swap AND mirror
    output.cells[0][2] = Cell { color: Color::Red, symbol: None };
    output.cells[0][3] = Cell { color: Color::Blue, symbol: None };
    output.cells[1][2] = Cell { color: Color::Blue, symbol: None };
    output.cells[1][3] = Cell { color: Color::Red, symbol: None };
    
    let mut color_map = HashMap::new();
    color_map.insert(Color::Blue, Color::Red);
    color_map.insert(Color::Red, Color::Blue);
    
    ARCPuzzle {
        id: "composition".to_string(),
        name: "The Weaving".to_string(),
        description: "Multiple truths intertwine to form reality".to_string(),
        input_examples: vec![(input.clone(), output.clone())],
        test_input: input,
        expected_output: output,
        rules: vec![Rule::Composite(vec![
            Rule::ColorMap(color_map),
            Rule::Symmetry(SymmetryType::Vertical),
        ])],
        difficulty: Difficulty::Medium,
        glyph_hint: GlyphHint {
            symbol: "⧬".to_string(),
            meaning: "Weave - patterns combine and transform".to_string(),
            resonance_color: Color::Purple,
        },
    }
}

pub fn create_emergence_puzzle() -> ARCPuzzle {
    // Conway-like growth pattern - the wow moment!
    let mut input = Grid::new(5, 5);
    input.cells[2][2] = Cell { color: Color::Cyan, symbol: Some('✦') };
    
    let mut output = Grid::new(5, 5);
    // Bloom pattern
    output.cells[2][2] = Cell { color: Color::Cyan, symbol: Some('✦') };
    output.cells[1][2] = Cell { color: Color::Cyan, symbol: None };
    output.cells[3][2] = Cell { color: Color::Cyan, symbol: None };
    output.cells[2][1] = Cell { color: Color::Cyan, symbol: None };
    output.cells[2][3] = Cell { color: Color::Cyan, symbol: None };
    
    ARCPuzzle {
        id: "emergence".to_string(),
        name: "The Blooming".to_string(),
        description: "From one, many. From simplicity, complexity. The pattern echoes...".to_string(),
        input_examples: vec![(input.clone(), output.clone())],
        test_input: input,
        expected_output: output,
        rules: vec![Rule::PatternFill(Pattern {
            template: vec![
                vec![false, true, false],
                vec![true, true, true],
                vec![false, true, false],
            ],
            anchor: (1, 1),
        })],
        difficulty: Difficulty::Hard,
        glyph_hint: GlyphHint {
            symbol: "❈".to_string(),
            meaning: "Bloom - from seed to infinity, the pattern echoes!".to_string(),
            resonance_color: Color::Cyan,
        },
    }
}