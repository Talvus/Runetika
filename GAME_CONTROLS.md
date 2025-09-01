# Runetika - First Level Controls

## Movement
- **WASD** or **Arrow Keys**: Move the human character
- **Camera**: Automatically follows the player

## Perspective Switching
- **SPACEBAR**: Switch between Human and Silicon perspective (must be near a terminal)
- **ESC**: Exit Silicon perspective and return to Human view

## Interactions
- **E**: Interact with objects (activate power nodes in the puzzle)

## First Puzzle: Power Restoration
Located in the Engineering room, this puzzle requires switching between perspectives:

1. **Human Perspective**: Can activate physical power nodes (visible as dark squares)
2. **Silicon Perspective**: Can see and activate digital power nodes (cyan colored)
3. **Goal**: Activate all 3 power nodes to restore ship power and unlock the Storage room

### Puzzle Solution:
- Node 1 (left): Activate in Human mode
- Node 2 (center): Only visible/activatable in Silicon mode
- Node 3 (right): Activate in Human mode

## Room Layout
```
     [Bridge]
        |
  [Engineering] <- Power Puzzle Here
        |
   [Corridor]---[Storage] <- Initially Locked
        |
   [Quarters] <- Starting Location
```

## Visual Indicators
- **Green Player Square**: Your character
- **Cyan Terminal**: Main terminal (Bridge)
- **Blue-gray Terminals**: Secondary terminals
- **Red Door**: Locked
- **Blue Door**: Unlocked
- **Green Power Node**: Activated
- **Dark Power Node**: Inactive

## Silicon Perspective Features
- Cyan overlay tint
- Data visualization elements
- "SILICON CONSCIOUSNESS ACTIVE" text
- Different visual perception of the ship

## Debug Commands
Press **F1** to see FPS and performance metrics (if enabled)