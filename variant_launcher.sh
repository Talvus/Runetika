#!/bin/bash

# Runetika Variant Launcher
# Easy switching between different game variants

echo "╔════════════════════════════════════════╗"
echo "║      RUNETIKA VARIANT LAUNCHER        ║"
echo "╚════════════════════════════════════════╝"
echo ""
echo "Select a variant to run:"
echo ""
echo "1) Standard - Full game experience"
echo "2) Terminal Minimalist - Pure text gameplay"
echo "3) Visual Novel - Story-focused"
echo "4) Puzzle Mechanics - ARC challenges"
echo "5) Art Aesthetic - Visual showcase"
echo "6) Creative Mechanics - Experimental features"
echo ""
echo -n "Choice (1-6): "
read choice

case $choice in
    1)
        echo "Running Standard Runetika..."
        git checkout main
        cargo run --release
        ;;
    2)
        echo "Running Terminal Minimalist..."
        git checkout variant/terminal-minimalist
        cargo run --bin terminal --release
        ;;
    3)
        echo "Running Visual Novel mode..."
        git checkout variant/visual-novel
        cargo run --release
        ;;
    4)
        echo "Running Puzzle Mechanics mode..."
        git checkout variant/puzzle-mechanics
        cargo run --release
        ;;
    5)
        echo "Running Art Aesthetic mode..."
        git checkout variant/art-aesthetic
        cargo run --release
        ;;
    6)
        echo "Running Creative Mechanics..."
        git checkout creative-mechanics
        cargo run --release
        ;;
    *)
        echo "Invalid choice!"
        exit 1
        ;;
esac