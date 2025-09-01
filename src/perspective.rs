use bevy::prelude::*;
use crate::game_state::GameState;
use crate::player::Player;

pub struct PerspectivePlugin;

impl Plugin for PerspectivePlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(CurrentPerspective::Human)
            .add_event::<PerspectiveSwitchEvent>()
            .add_systems(Update, (
                handle_perspective_input,
                apply_perspective_switch,
                update_perspective_visuals,
                check_terminal_proximity,
            ).run_if(in_state(GameState::InGame)));
    }
}

#[derive(Resource, Clone, Copy, PartialEq, Eq, Debug)]
pub enum CurrentPerspective {
    Human,
    Silicon,
}

#[derive(Event)]
pub struct PerspectiveSwitchEvent {
    pub to: CurrentPerspective,
}

#[derive(Component)]
pub struct InteractableTerminal {
    pub is_main: bool,
}

#[derive(Component)]
pub struct TerminalProximity {
    pub in_range: bool,
    pub terminal_entity: Option<Entity>,
}

#[derive(Component)]
pub struct SiliconVision;

#[derive(Component)]
pub struct HumanVision;

const INTERACTION_RANGE: f32 = 50.0;

fn check_terminal_proximity(
    player_query: Query<(Entity, &Transform), With<Player>>,
    terminal_query: Query<(Entity, &Transform, &InteractableTerminal)>,
    mut commands: Commands,
) {
    if let Ok((player_entity, player_transform)) = player_query.get_single() {
        let player_pos = player_transform.translation.truncate();
        
        let mut closest_terminal: Option<(Entity, f32)> = None;
        
        for (terminal_entity, terminal_transform, _terminal) in terminal_query.iter() {
            let terminal_pos = terminal_transform.translation.truncate();
            let distance = player_pos.distance(terminal_pos);
            
            if distance < INTERACTION_RANGE {
                if let Some((_, closest_dist)) = closest_terminal {
                    if distance < closest_dist {
                        closest_terminal = Some((terminal_entity, distance));
                    }
                } else {
                    closest_terminal = Some((terminal_entity, distance));
                }
            }
        }
        
        // Update or create proximity component
        if let Some((terminal_entity, _)) = closest_terminal {
            commands.entity(player_entity).insert(TerminalProximity {
                in_range: true,
                terminal_entity: Some(terminal_entity),
            });
        } else {
            commands.entity(player_entity).insert(TerminalProximity {
                in_range: false,
                terminal_entity: None,
            });
        }
    }
}

fn handle_perspective_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    current_perspective: Res<CurrentPerspective>,
    player_query: Query<&TerminalProximity, With<Player>>,
    mut switch_events: EventWriter<PerspectiveSwitchEvent>,
) {
    if keyboard.just_pressed(KeyCode::Space) {
        // Check if player is near a terminal
        if let Ok(proximity) = player_query.get_single() {
            if proximity.in_range {
                // Switch perspective
                let new_perspective = match *current_perspective {
                    CurrentPerspective::Human => CurrentPerspective::Silicon,
                    CurrentPerspective::Silicon => CurrentPerspective::Human,
                };
                
                switch_events.send(PerspectiveSwitchEvent { to: new_perspective });
            }
        }
    }
    
    // ESC to exit silicon mode
    if keyboard.just_pressed(KeyCode::Escape) && *current_perspective == CurrentPerspective::Silicon {
        switch_events.send(PerspectiveSwitchEvent { to: CurrentPerspective::Human });
    }
}

fn apply_perspective_switch(
    mut events: EventReader<PerspectiveSwitchEvent>,
    mut current_perspective: ResMut<CurrentPerspective>,
    mut player_query: Query<&mut Player>,
    mut commands: Commands,
) {
    for event in events.read() {
        *current_perspective = event.to;
        
        // Update player state
        if let Ok(mut player) = player_query.get_single_mut() {
            player.in_terminal_mode = event.to == CurrentPerspective::Silicon;
        }
        
        // Trigger visual transition
        match event.to {
            CurrentPerspective::Silicon => {
                info!("Entering Silicon Perspective");
                spawn_silicon_overlay(&mut commands);
            }
            CurrentPerspective::Human => {
                info!("Returning to Human Perspective");
                despawn_silicon_overlay(&mut commands);
            }
        }
    }
}

fn update_perspective_visuals(
    current_perspective: Res<CurrentPerspective>,
    mut camera_query: Query<&mut Camera>,
    mut sprite_query: Query<&mut Sprite, Without<Player>>,
    time: Res<Time>,
) {
    match *current_perspective {
        CurrentPerspective::Silicon => {
            // Apply silicon vision effects
            if let Ok(mut camera) = camera_query.get_single_mut() {
                // Tint everything blue-green
                camera.clear_color = ClearColorConfig::Custom(Color::srgb(0.0, 0.1, 0.15));
            }
            
            // Make everything look like data/circuits
            for mut sprite in sprite_query.iter_mut() {
                // Pulse effect
                let pulse = (time.elapsed_secs() * 2.0).sin() * 0.1 + 0.9;
                sprite.color = sprite.color.with_alpha(pulse);
            }
        }
        CurrentPerspective::Human => {
            // Normal vision
            if let Ok(mut camera) = camera_query.get_single_mut() {
                camera.clear_color = ClearColorConfig::Custom(Color::srgb(0.05, 0.05, 0.1));
            }
            
            // Reset sprite colors
            for mut sprite in sprite_query.iter_mut() {
                sprite.color = sprite.color.with_alpha(1.0);
            }
        }
    }
}

fn spawn_silicon_overlay(commands: &mut Commands) {
    // Create visual overlay for silicon mode
    commands.spawn((
        SiliconVision,
        Sprite {
            color: Color::srgba(0.0, 0.8, 0.8, 0.1), // Cyan tint
            custom_size: Some(Vec2::new(2000.0, 2000.0)),
            ..default()
        },
        Transform::from_translation(Vec3::new(0.0, 0.0, 900.0)),
    ));
    
    // Add UI text showing silicon mode
    commands.spawn((
        SiliconVision,
        Text2d::new("SILICON CONSCIOUSNESS ACTIVE"),
        TextFont {
            font_size: 20.0,
            ..default()
        },
        TextColor(Color::srgb(0.0, 1.0, 1.0)),
        Transform::from_translation(Vec3::new(0.0, 350.0, 950.0)),
    ));
    
    // Add data visualization elements
    for i in 0..10 {
        let angle = (i as f32 / 10.0) * std::f32::consts::TAU;
        let radius = 200.0;
        let x = angle.cos() * radius;
        let y = angle.sin() * radius;
        
        commands.spawn((
            SiliconVision,
            Sprite {
                color: Color::srgba(0.0, 1.0, 1.0, 0.3),
                custom_size: Some(Vec2::splat(5.0)),
                ..default()
            },
            Transform::from_translation(Vec3::new(x, y, 850.0)),
        ));
    }
}

fn despawn_silicon_overlay(commands: &mut Commands) {
    // Remove all silicon vision elements
    // Note: In a real implementation, we'd query and despawn entities with SiliconVision component
    // This is a placeholder for the actual implementation
}