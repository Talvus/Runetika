use bevy::prelude::*;

#[derive(Clone, Debug, PartialEq)]
pub struct Grid {
    pub cells: Vec<Vec<Cell>>,
    pub width: usize,
    pub height: usize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Cell {
    pub color: Color,
    pub symbol: Option<char>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Color {
    Empty,
    Black,
    Blue,
    Red,
    Green,
    Yellow,
    Purple,
    Orange,
    Cyan,
    Brown,
}

impl Color {
    pub fn to_bevy_color(&self) -> bevy::prelude::Color {
        match self {
            Color::Empty => bevy::prelude::Color::NONE,
            Color::Black => bevy::prelude::Color::BLACK,
            Color::Blue => bevy::prelude::Color::srgb(0.0, 0.0, 1.0),
            Color::Red => bevy::prelude::Color::srgb(1.0, 0.0, 0.0),
            Color::Green => bevy::prelude::Color::srgb(0.0, 1.0, 0.0),
            Color::Yellow => bevy::prelude::Color::srgb(1.0, 1.0, 0.0),
            Color::Purple => bevy::prelude::Color::srgb(0.5, 0.0, 0.5),
            Color::Orange => bevy::prelude::Color::srgb(1.0, 0.5, 0.0),
            Color::Cyan => bevy::prelude::Color::srgb(0.0, 1.0, 1.0),
            Color::Brown => bevy::prelude::Color::srgb(0.5, 0.25, 0.0),
        }
    }
    
    pub fn to_char(&self) -> char {
        match self {
            Color::Empty => '.',
            Color::Black => '#',
            Color::Blue => 'B',
            Color::Red => 'R',
            Color::Green => 'G',
            Color::Yellow => 'Y',
            Color::Purple => 'P',
            Color::Orange => 'O',
            Color::Cyan => 'C',
            Color::Brown => 'W',
        }
    }
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub template: Vec<Vec<bool>>,
    pub anchor: (usize, usize),
}

impl Grid {
    pub fn new(width: usize, height: usize) -> Self {
        Self {
            cells: vec![vec![Cell { color: Color::Empty, symbol: None }; width]; height],
            width,
            height,
        }
    }
    
    pub fn to_ascii(&self) -> String {
        let mut result = String::new();
        for row in &self.cells {
            for cell in row {
                result.push(cell.color.to_char());
                result.push(' ');
            }
            result.push('\n');
        }
        result
    }
    
    pub fn rotate(&self, degrees: i32) -> Self {
        let rotations = (degrees / 90) % 4;
        let mut result = self.clone();
        
        for _ in 0..rotations {
            let mut new_grid = Grid::new(result.height, result.width);
            for y in 0..result.height {
                for x in 0..result.width {
                    new_grid.cells[x][result.height - 1 - y] = result.cells[y][x];
                }
            }
            result = new_grid;
        }
        result
    }
    
    pub fn mirror_horizontal(&self) -> Self {
        let mut result = self.clone();
        for row in &mut result.cells {
            row.reverse();
        }
        result
    }
    
    pub fn detect_symmetry(&self) -> Option<super::types::SymmetryType> {
        // Check horizontal symmetry
        let mut h_symmetric = true;
        for y in 0..self.height {
            for x in 0..self.width / 2 {
                if self.cells[y][x] != self.cells[y][self.width - 1 - x] {
                    h_symmetric = false;
                    break;
                }
            }
        }
        if h_symmetric {
            return Some(super::types::SymmetryType::Horizontal);
        }
        
        // Check vertical symmetry
        let mut v_symmetric = true;
        for y in 0..self.height / 2 {
            for x in 0..self.width {
                if self.cells[y][x] != self.cells[self.height - 1 - y][x] {
                    v_symmetric = false;
                    break;
                }
            }
        }
        if v_symmetric {
            return Some(super::types::SymmetryType::Vertical);
        }
        
        None
    }
}