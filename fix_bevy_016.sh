#!/bin/bash
echo "🔧 Fixing Bevy 0.16 compilation errors..."

# Fix 1: Remove incorrect type aliases and use ChildBuilder from prelude
echo "Fixing ChildBuilder types..."
sed -i '' '/type ChildBuilder.*WorldChildBuilder/d' src/menu/ui.rs src/settings/ui.rs src/credits/ui.rs

# Fix 2: Replace deprecated get_single() and get_single_mut() with single() and single_mut()
echo "Fixing deprecated Bevy APIs..."
find src -name "*.rs" -exec sed -i '' 's/\.get_single()/\.single()/g' {} \;
find src -name "*.rs" -exec sed -i '' 's/\.get_single_mut()/\.single_mut()/g' {} \;

# Fix 3: Fix deprecated despawn_recursive() - it's now just despawn_recursive()
echo "Fixing despawn calls..."
find src -name "*.rs" -exec sed -i '' 's/\.despawn_recursive()/\.despawn_recursive()/g' {} \;

# Fix 4: Fix send() to send() for events (not deprecated, keep as is)
echo "Event sending is fine in Bevy 0.16..."

echo "✅ Automated fixes complete!"
echo ""
echo "Manual fixes still needed:"
echo "1. Fix silicon_mind.rs think() method signature"
echo "2. Fix terminal_commands.rs string type mismatches"
echo "3. Fix terminal_interface.rs borrow checker issues"