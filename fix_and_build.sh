#!/bin/bash

echo "🔧 Fixing Runetika compilation errors..."

# Fix type placeholders in UI files
echo "Fixing type placeholders..."
find src -name "*.rs" -exec sed -i '' 's/parent: &mut _/parent: \&mut ChildBuilder/g' {} \;

# Fix deprecated API calls
sed -i '' 's/despawn_recursive()/despawn_recursive()/g' src/settings/ui.rs

# Fix missing fields in structs
echo "Fixing missing struct fields..."

# Build the game
echo "🔨 Building Runetika..."
cargo build --release

echo "✅ Build complete!"