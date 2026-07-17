//! Terminal commands that expose Lemma's proof kernel to gameplay.
//!
//! Each command implements the terminal's `Command` trait and accesses
//! shared proof state via Arc<Mutex<ProofWorkspaceInner>>.

use std::sync::{Arc, Mutex};

use bevy::prelude::*;

use crate::terminal::{Command, CommandResult, CommandRegistry, TerminalHistory};

use super::resources::{ProofWorkspace, ProofWorkspaceInner};

// ── ALIEN command ────────────────────────────────────────────────────

/// Parse an ALIEN expression and display its three representations.
pub struct AlienCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for AlienCommand {
    fn execute(&self, args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        if args.is_empty() {
            return CommandResult::Error("Usage: alien <expression>".to_string());
        }

        let input = args.join(" ");
        let Ok(ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        match lemma_alien::parse(&input) {
            Ok(expr) => {
                let mut output = String::new();
                output.push_str(&format!("  Alien:  {}\n", input));

                // Elaborate to TTT
                match ws.elaborator.elaborate(&expr) {
                    Ok(ttt) => {
                        output.push_str(&format!("  TTT:    {}\n", ttt));
                    }
                    Err(e) => {
                        output.push_str(&format!("  TTT:    (elaboration error: {})\n", e));
                    }
                }

                // Render as glyph
                let ascii = ws.elaborator.render_ascii(&expr);
                output.push_str(&format!("  Glyph:  {}", ascii));

                CommandResult::Success(output)
            }
            Err(e) => CommandResult::Error(format!("Parse error: {}", e)),
        }
    }

    fn help(&self) -> String {
        "Parse an ALIEN expression and show TTT + glyph (usage: alien <expr>)".to_string()
    }

    fn autocomplete(&self, _partial: &str) -> Vec<String> {
        vec![
            "erode".to_string(),
            "dilate".to_string(),
            "open".to_string(),
            "close".to_string(),
        ]
    }
}

// ── TILES command ────────────────────────────────────────────────────

/// List all available proof tiles from the library.
pub struct TilesCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for TilesCommand {
    fn execute(&self, _args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        let Ok(ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        let mut output = String::new();
        output.push_str("Available Proof Tiles:\n");

        for (_, tile) in ws.library.iter() {
            let name = tile.name.as_deref().unwrap_or("(unnamed)");
            let desc = tile.description.as_deref().unwrap_or("");
            let arity = tile.inputs.len();
            let closed = if tile.is_closed() { " (closed)" } else { "" };
            output.push_str(&format!("  {:<12} [{} inputs]{} {}\n", name, arity, closed, desc));
        }

        CommandResult::Success(output.trim_end().to_string())
    }

    fn help(&self) -> String {
        "List all available proof tiles".to_string()
    }
}

// ── GOALS command ────────────────────────────────────────────────────

/// Show open proof goals (unconnected input edges).
pub struct GoalsCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for GoalsCommand {
    fn execute(&self, _args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        let Ok(ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        let goals = ws.graph.open_goals();

        if goals.is_empty() {
            if ws.graph.tile_count() == 0 {
                return CommandResult::Success("No tiles placed. Use 'place <tile>' to begin.".to_string());
            }
            return CommandResult::Success("No open goals — proof is complete!".to_string());
        }

        let mut output = format!("{} open goals:\n", goals.len());
        for (placed_id, edge_idx, edge) in &goals {
            output.push_str(&format!("  tile {:?} edge {} needs: {}\n", placed_id, edge_idx, edge.ty));
        }

        CommandResult::Success(output.trim_end().to_string())
    }

    fn help(&self) -> String {
        "Show open proof goals (unconnected edges)".to_string()
    }
}

// ── PLACE command ────────────────────────────────────────────────────

/// Place a tile in the proof workspace.
pub struct PlaceCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for PlaceCommand {
    fn execute(&self, args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        if args.is_empty() {
            return CommandResult::Error("Usage: place <tile_name>".to_string());
        }

        let tile_name = &args[0];
        let Ok(mut ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        // Find the tile by name in the library
        let tile_id = match ws.library.find_by_name(tile_name) {
            Some((id, _)) => id,
            None => {
                return CommandResult::Error(format!("Unknown tile: '{}'. Use 'tiles' to list.", tile_name));
            }
        };

        // Place at origin (position doesn't matter for proof validity)
        let count = ws.graph.tile_count() as f32;
        match ws.graph.place_tile(tile_id, (count * 80.0, 0.0)) {
            Some(placed_id) => {
                let tile = ws.library.get(tile_id).unwrap();
                let name = tile.name.as_deref().unwrap_or("unnamed");
                CommandResult::Success(format!(
                    "Placed '{}' (id: {:?}, {} inputs, {} outputs)",
                    name, placed_id, tile.inputs.len(), tile.outputs.len()
                ))
            }
            None => CommandResult::Error("Failed to place tile".to_string()),
        }
    }

    fn help(&self) -> String {
        "Place a proof tile in the workspace (usage: place <tile_name>)".to_string()
    }

    fn autocomplete(&self, partial: &str) -> Vec<String> {
        let Ok(ws) = self.workspace.lock() else { return vec![] };
        ws.library.iter()
            .filter_map(|(_, t)| t.name.as_ref())
            .filter(|n| n.starts_with(partial))
            .cloned()
            .collect()
    }
}

// ── CONNECT command ──────────────────────────────────────────────────

/// Connect two tile edges in the proof workspace.
pub struct ConnectCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for ConnectCommand {
    fn execute(&self, args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        if args.len() < 4 {
            return CommandResult::Error(
                "Usage: connect <from_tile_idx> <from_edge> <to_tile_idx> <to_edge>".to_string(),
            );
        }

        // Parse indices (simplified — uses tile placement order)
        let from_idx: usize = match args[0].parse() {
            Ok(n) => n,
            Err(_) => return CommandResult::Error("Invalid from_tile index".to_string()),
        };
        let from_edge: usize = match args[1].parse() {
            Ok(n) => n,
            Err(_) => return CommandResult::Error("Invalid from_edge index".to_string()),
        };
        let to_idx: usize = match args[2].parse() {
            Ok(n) => n,
            Err(_) => return CommandResult::Error("Invalid to_tile index".to_string()),
        };
        let to_edge: usize = match args[3].parse() {
            Ok(n) => n,
            Err(_) => return CommandResult::Error("Invalid to_edge index".to_string()),
        };

        let Ok(mut ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        // Collect placed tile IDs in order
        let placed_ids: Vec<_> = ws.graph.placed_tile_ids().collect();

        if from_idx >= placed_ids.len() || to_idx >= placed_ids.len() {
            return CommandResult::Error(format!(
                "Tile index out of range (have {} tiles)",
                placed_ids.len()
            ));
        }

        let from_id = placed_ids[from_idx];
        let to_id = placed_ids[to_idx];

        match ws.graph.connect(from_id, from_edge, to_id, to_edge) {
            Ok(conn_id) => CommandResult::Success(format!(
                "Connected! (connection {:?}). {} goals remaining.",
                conn_id,
                ws.graph.open_goals().len()
            )),
            Err(e) => CommandResult::Error(format!("Connection failed: {}", e)),
        }
    }

    fn help(&self) -> String {
        "Connect tile edges (usage: connect <from> <edge> <to> <edge>)".to_string()
    }
}

// ── VERIFY command ───────────────────────────────────────────────────

/// Verify the current proof graph and generate a certificate.
pub struct VerifyCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for VerifyCommand {
    fn execute(&self, _args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        let Ok(ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        if ws.graph.tile_count() == 0 {
            return CommandResult::Error("No tiles placed. Nothing to verify.".to_string());
        }

        match lemma_verify::verify_graph(&ws.graph) {
            lemma_verify::VerificationResult::Valid(cert) => {
                let mut output = String::new();
                output.push_str("PROOF VERIFIED\n");
                output.push_str(&format!("  Root hash: {}\n", cert.merkle_root));
                output.push_str(&format!("  Proven type: {}\n", cert.proven_type));
                output.push_str(&format!("  Tiles: {}\n", cert.tile_count));
                output.push_str(&format!("  Connections: {}", cert.connection_count));
                CommandResult::Success(output)
            }
            lemma_verify::VerificationResult::Invalid(errors) => {
                let msgs: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
                CommandResult::Error(format!("Proof INVALID: {}", msgs.join("; ")))
            }
            lemma_verify::VerificationResult::Incomplete { open_goal_count, .. } => {
                CommandResult::Error(format!(
                    "Proof incomplete: {} open goals remain. Use 'goals' to see them.",
                    open_goal_count
                ))
            }
        }
    }

    fn help(&self) -> String {
        "Verify the proof graph and generate a certificate".to_string()
    }
}

// ── GLYPH command ────────────────────────────────────────────────────

/// Render an ALIEN expression as an ASCII glyph.
pub struct GlyphCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for GlyphCommand {
    fn execute(&self, args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        if args.is_empty() {
            return CommandResult::Error("Usage: glyph <expression>".to_string());
        }

        let input = args.join(" ");
        let Ok(ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        match lemma_alien::parse(&input) {
            Ok(expr) => {
                let ascii = ws.elaborator.render_ascii(&expr);
                CommandResult::Success(ascii)
            }
            Err(e) => CommandResult::Error(format!("Parse error: {}", e)),
        }
    }

    fn help(&self) -> String {
        "Render an ALIEN expression as ASCII glyph art (usage: glyph <expr>)".to_string()
    }
}

// ── TYPECHECK command ────────────────────────────────────────────────

/// Type-check an ALIEN expression through the full pipeline.
pub struct TypecheckCommand {
    workspace: Arc<Mutex<ProofWorkspaceInner>>,
}

impl Command for TypecheckCommand {
    fn execute(&self, args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        if args.is_empty() {
            return CommandResult::Error("Usage: typecheck <expression>".to_string());
        }

        let input = args.join(" ");
        let Ok(ws) = self.workspace.lock() else {
            return CommandResult::Error("Proof workspace busy".to_string());
        };

        // Parse ALIEN → elaborate to TTT → type-check
        let expr = match lemma_alien::parse(&input) {
            Ok(e) => e,
            Err(e) => return CommandResult::Error(format!("Parse error: {}", e)),
        };

        let ttt = match ws.elaborator.elaborate(&expr) {
            Ok(t) => t,
            Err(e) => return CommandResult::Error(format!("Elaboration error: {}", e)),
        };

        match lemma_core::type_of(&ttt) {
            Ok(ty) => {
                let mut output = String::new();
                output.push_str(&format!("  Term:  {}\n", ttt));
                output.push_str(&format!("  Type:  {}", ty));
                CommandResult::Success(output)
            }
            Err(e) => CommandResult::Error(format!("Type error: {}", e)),
        }
    }

    fn help(&self) -> String {
        "Type-check an ALIEN expression (usage: typecheck <expr>)".to_string()
    }
}

// ── Registration ─────────────────────────────────────────────────────

/// Register all Lemma terminal commands.
pub fn register_lemma_commands(
    mut registry: ResMut<CommandRegistry>,
    workspace: Res<ProofWorkspace>,
) {
    let shared = workspace.shared.clone();

    registry.commands.insert(
        "alien".to_string(),
        Box::new(AlienCommand { workspace: shared.clone() }),
    );
    registry.commands.insert(
        "tiles".to_string(),
        Box::new(TilesCommand { workspace: shared.clone() }),
    );
    registry.commands.insert(
        "goals".to_string(),
        Box::new(GoalsCommand { workspace: shared.clone() }),
    );
    registry.commands.insert(
        "place".to_string(),
        Box::new(PlaceCommand { workspace: shared.clone() }),
    );
    registry.commands.insert(
        "connect".to_string(),
        Box::new(ConnectCommand { workspace: shared.clone() }),
    );
    registry.commands.insert(
        "verify".to_string(),
        Box::new(VerifyCommand { workspace: shared.clone() }),
    );
    registry.commands.insert(
        "glyph".to_string(),
        Box::new(GlyphCommand { workspace: shared.clone() }),
    );
    registry.commands.insert(
        "typecheck".to_string(),
        Box::new(TypecheckCommand { workspace: shared }),
    );
}
