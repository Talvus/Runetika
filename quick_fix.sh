#!/bin/bash
echo "🔧 Applying quick fixes to run the game..."

# Backup problematic files
for file in terminal_interface terminal_commands; do
    mv src/${file}.rs src/${file}.rs.broken 2>/dev/null
    echo "use bevy::prelude::*; pub struct ${file}Plugin; impl Plugin for ${file}Plugin { fn build(&self, _app: &mut App) {} }" > src/${file}.rs
done

# Try to run
cargo run

# Restore files
for file in terminal_interface terminal_commands; do
    mv src/${file}.rs.broken src/${file}.rs 2>/dev/null
done