#!/bin/bash
echo "🎮 Running Runetika Test Build"
echo "=============================="
echo ""

# Temporarily disable problematic modules
mv src/terminal_interface.rs src/terminal_interface.rs.bak 2>/dev/null
mv src/terminal_commands.rs src/terminal_commands.rs.bak 2>/dev/null

# Create minimal versions
cat > src/terminal_interface.rs << 'EOF'
use bevy::prelude::*;

pub struct TerminalInterfacePlugin;

impl Plugin for TerminalInterfacePlugin {
    fn build(&self, _app: &mut App) {
        // Minimal implementation
    }
}
EOF

cat > src/terminal_commands.rs << 'EOF'
use bevy::prelude::*;

pub fn register_commands() {
    // Minimal implementation
}
EOF

echo "Building with minimal modules..."
cargo run 2>&1 | grep -E "Compiling|Finished|Running|error" 

# Restore original files
mv src/terminal_interface.rs.bak src/terminal_interface.rs 2>/dev/null
mv src/terminal_commands.rs.bak src/terminal_commands.rs 2>/dev/null

echo ""
echo "Build test complete!"