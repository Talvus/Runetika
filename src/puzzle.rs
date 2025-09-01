use bevy::prelude::*;
use crate::game_state::GameState;
use crate::perspective::CurrentPerspective;
use crate::spaceship::{Door, RoomType};

pub struct PuzzlePlugin;

impl Plugin for PuzzlePlugin {
    fn build(&self, app: &mut App) {
        app.add_event::<PuzzleSolvedEvent>()
            .add_systems(OnEnter(GameState::InGame), setup_puzzles)
            .add_systems(Update, (
                check_power_puzzle,
                handle_puzzle_solved,
            ).run_if(in_state(GameState::InGame)));
    }
}

#[derive(Component)]
pub struct Puzzle {
    pub id: PuzzleId,
    pub solved: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PuzzleId {
    PowerRestoration,
    DoorUnlock,
}

#[derive(Event)]
pub struct PuzzleSolvedEvent {
    pub puzzle_id: PuzzleId,
}

#[derive(Component)]
pub struct PowerNode {
    pub active: bool,
    pub requires_silicon_view: bool,
}

#[derive(Component)]
pub struct PowerCircuit {
    pub nodes_activated: u32,
    pub nodes_required: u32,
}

fn setup_puzzles(mut commands: Commands) {
    // Create the power restoration puzzle
    commands.spawn((
        Puzzle {
            id: PuzzleId::PowerRestoration,
            solved: false,
        },
        PowerCircuit {
            nodes_activated: 0,
            nodes_required: 3,
        },
    ));
    
    // Spawn power nodes in Engineering room
    // Node 1: Visible in human view
    commands.spawn((
        PowerNode {
            active: false,
            requires_silicon_view: false,
        },
        Sprite {
            color: Color::srgb(0.2, 0.2, 0.2),
            custom_size: Some(Vec2::splat(20.0)),
            ..default()
        },
        Transform::from_translation(Vec3::new(-50.0, 200.0, 5.0)),
    ));
    
    // Node 2: Only visible/interactable in silicon view
    commands.spawn((
        PowerNode {
            active: false,
            requires_silicon_view: true,
        },
        Sprite {
            color: Color::srgba(0.0, 0.8, 0.8, 0.0), // Invisible in human view
            custom_size: Some(Vec2::splat(20.0)),
            ..default()
        },
        Transform::from_translation(Vec3::new(0.0, 200.0, 5.0)),
    ));
    
    // Node 3: Visible in human view but activated from silicon view
    commands.spawn((
        PowerNode {
            active: false,
            requires_silicon_view: false,
        },
        Sprite {
            color: Color::srgb(0.2, 0.2, 0.2),
            custom_size: Some(Vec2::splat(20.0)),
            ..default()
        },
        Transform::from_translation(Vec3::new(50.0, 200.0, 5.0)),
    ));
}

fn check_power_puzzle(
    keyboard: Res<ButtonInput<KeyCode>>,
    current_perspective: Res<CurrentPerspective>,
    player_query: Query<&Transform, With<crate::player::Player>>,
    mut node_query: Query<(&mut PowerNode, &mut Sprite, &Transform), Without<crate::player::Player>>,
    mut circuit_query: Query<(&mut PowerCircuit, &mut Puzzle)>,
    mut events: EventWriter<PuzzleSolvedEvent>,
) {
    if !keyboard.just_pressed(KeyCode::KeyE) {
        return;
    }
    
    if let Ok(player_transform) = player_query.get_single() {
        let player_pos = player_transform.translation.truncate();
        
        // Check if player is near any power node
        for (mut node, mut sprite, node_transform) in node_query.iter_mut() {
            let node_pos = node_transform.translation.truncate();
            let distance = player_pos.distance(node_pos);
            
            if distance < 40.0 && !node.active {
                // Check if we can activate this node
                let can_activate = if node.requires_silicon_view {
                    *current_perspective == CurrentPerspective::Silicon
                } else {
                    *current_perspective == CurrentPerspective::Human
                };
                
                if can_activate {
                    node.active = true;
                    sprite.color = Color::srgb(0.0, 1.0, 0.0); // Green when active
                    
                    // Update circuit progress
                    for (mut circuit, mut puzzle) in circuit_query.iter_mut() {
                        if puzzle.id == PuzzleId::PowerRestoration {
                            circuit.nodes_activated += 1;
                            
                            info!("Power node activated! {}/{} nodes active", 
                                  circuit.nodes_activated, circuit.nodes_required);
                            
                            if circuit.nodes_activated >= circuit.nodes_required && !puzzle.solved {
                                puzzle.solved = true;
                                events.send(PuzzleSolvedEvent {
                                    puzzle_id: PuzzleId::PowerRestoration,
                                });
                            }
                        }
                    }
                }
            }
        }
    }
}

fn handle_puzzle_solved(
    mut events: EventReader<PuzzleSolvedEvent>,
    mut door_query: Query<(&mut Door, &mut Sprite)>,
) {
    for event in events.read() {
        match event.puzzle_id {
            PuzzleId::PowerRestoration => {
                info!("Power restored! Storage room door unlocked!");
                
                // Unlock the storage room door
                for (mut door, mut sprite) in door_query.iter_mut() {
                    if door.connects.0 == RoomType::Corridor && door.connects.1 == RoomType::Storage {
                        door.locked = false;
                        sprite.color = Color::srgb(0.4, 0.6, 0.8); // Change to unlocked color
                    }
                }
            }
            PuzzleId::DoorUnlock => {
                info!("Door puzzle solved!");
            }
        }
    }
}