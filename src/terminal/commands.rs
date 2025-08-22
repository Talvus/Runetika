use super::{Command, CommandResult, TerminalHistory, TerminalLine, LineType, CommandRegistry};
use bevy::prelude::*;

pub struct HelpCommand;
pub struct ClearCommand;
pub struct EchoCommand;
pub struct StatusCommand;
pub struct ExitCommand;
pub struct HistoryCommand;

impl Command for HelpCommand {
    fn execute(&self, _args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        let mut output = String::new();
        output.push_str("╔════════════════════════════════════╗\n");
        output.push_str("║     COSMIC TERMINAL COMMANDS       ║\n");
        output.push_str("╚════════════════════════════════════╝\n\n");
        output.push_str("SYSTEM COMMANDS:\n");
        output.push_str("  help      → Display this help menu\n");
        output.push_str("  clear     → Clear terminal display\n");
        output.push_str("  echo      → Echo text to terminal\n");
        output.push_str("  status    → System status report\n");
        output.push_str("  history   → Command history log\n");
        output.push_str("  exit      → Terminate session\n");
        output.push_str("\nNAVIGATION CONTROLS:\n");
        output.push_str("  ↑/↓       → Browse command history\n");
        output.push_str("  Tab       → Autocomplete command\n");
        output.push_str("  Scroll    → Navigate output\n");
        output.push_str("\n══════════════════════════════════════");
        CommandResult::Success(output)
    }
    
    fn help(&self) -> String {
        "Show available commands and help information".to_string()
    }
}

impl Command for ClearCommand {
    fn execute(&self, _args: Vec<String>, terminal: &mut TerminalHistory) -> CommandResult {
        terminal.lines.clear();
        terminal.lines.push(TerminalLine {
            text: "Terminal cleared".to_string(),
            line_type: LineType::System,
            timestamp: 0.0,
        });
        CommandResult::Continue
    }
    
    fn help(&self) -> String {
        "Clear the terminal screen".to_string()
    }
}

impl Command for EchoCommand {
    fn execute(&self, args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        if args.is_empty() {
            CommandResult::Success(String::new())
        } else {
            CommandResult::Success(args.join(" "))
        }
    }
    
    fn help(&self) -> String {
        "Echo text back to the terminal".to_string()
    }
}

impl Command for StatusCommand {
    fn execute(&self, _args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        let output = format!(
            "╭─────── SYSTEM STATUS ───────╮\n\
             │ ◆ Memory.......... [████] OK │\n\
             │ ◆ CPU............. [███░] 75% │\n\
             │ ◆ Network......... ONLINE ✓  │\n\
             │ ◆ Quantum Core.... STABLE    │\n\
             │ ◆ Navigation...... READY     │\n\
             ╰──────────────────────────────╯"
        );
        CommandResult::Success(output)
    }
    
    fn help(&self) -> String {
        "Show current game status".to_string()
    }
}

impl Command for ExitCommand {
    fn execute(&self, _args: Vec<String>, _terminal: &mut TerminalHistory) -> CommandResult {
        std::process::exit(0);
    }
    
    fn help(&self) -> String {
        "Exit the game".to_string()
    }
}

impl Command for HistoryCommand {
    fn execute(&self, args: Vec<String>, terminal: &mut TerminalHistory) -> CommandResult {
        let limit = args.first()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(20);
        
        let start = terminal.command_history.len().saturating_sub(limit);
        let history_slice = &terminal.command_history[start..];
        
        if history_slice.is_empty() {
            CommandResult::Success("No command history".to_string())
        } else {
            let mut output = String::new();
            for (i, cmd) in history_slice.iter().enumerate() {
                output.push_str(&format!("{:4} {}\n", start + i + 1, cmd));
            }
            CommandResult::Success(output.trim_end().to_string())
        }
    }
    
    fn help(&self) -> String {
        "Show command history (usage: history [count])".to_string()
    }
}

pub fn register_builtin_commands(mut command_registry: ResMut<CommandRegistry>) {
    command_registry.commands.insert("help".to_string(), Box::new(HelpCommand));
    command_registry.commands.insert("clear".to_string(), Box::new(ClearCommand));
    command_registry.commands.insert("echo".to_string(), Box::new(EchoCommand));
    command_registry.commands.insert("status".to_string(), Box::new(StatusCommand));
    command_registry.commands.insert("exit".to_string(), Box::new(ExitCommand));
    command_registry.commands.insert("history".to_string(), Box::new(HistoryCommand));
}