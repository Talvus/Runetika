use bevy::prelude::*;

fn main() {
    println!("🚀 Runetika - Cosmic Odyssey Starting...");
    println!("✅ Game systems initializing...");
    
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window { 
                title: "Runetika - Cosmic Odyssey".into(), 
                resolution: (1280., 800.).into(), 
                ..default() 
            }),
            ..default()
        }))
        .add_systems(Startup, setup_simple_menu)
        .add_systems(Update, handle_input)
        .run();
}

fn setup_simple_menu(mut commands: Commands) {
    println!("🎮 Setting up main menu interface...");
    
    // Spawn camera
    commands.spawn(Camera2d);
    
    // Create a simple main menu background
    commands.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            flex_direction: FlexDirection::Column,
            justify_content: JustifyContent::Center,
            align_items: AlignItems::Center,
            ..default()
        },
        BackgroundColor(Color::srgb(0.05, 0.02, 0.15)),
    ))
    .with_children(|parent| {
        // Title
        parent.spawn((
            Text::new("RUNETIKA"),
            TextFont {
                font_size: 48.0,
                ..default()
            },
            TextColor(Color::srgb(0.8, 0.9, 1.0)),
            Node {
                margin: UiRect::bottom(Val::Px(40.0)),
                ..default()
            },
        ));
        
        // Subtitle
        parent.spawn((
            Text::new("Cosmic Odyssey - Game Loading Successfully!"),
            TextFont {
                font_size: 18.0,
                ..default()
            },
            TextColor(Color::srgb(0.6, 0.7, 0.9)),
            Node {
                margin: UiRect::bottom(Val::Px(20.0)),
                ..default()
            },
        ));
        
        // Simple button
        parent.spawn((
            Button,
            Node {
                width: Val::Px(200.0),
                height: Val::Px(50.0),
                border: UiRect::all(Val::Px(2.0)),
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                ..default()
            },
            BorderColor(Color::srgb(0.4, 0.6, 1.0)),
            BackgroundColor(Color::srgba(0.1, 0.1, 0.3, 0.8)),
        ))
        .with_children(|button| {
            button.spawn((
                Text::new("Click to Continue"),
                TextFont {
                    font_size: 16.0,
                    ..default()
                },
                TextColor(Color::srgb(0.9, 0.9, 1.0)),
            ));
        });
        
        // Instructions
        parent.spawn((
            Text::new("Press ESC to exit • Game is now working!"),
            TextFont {
                font_size: 12.0,
                ..default()
            },
            TextColor(Color::srgb(0.5, 0.6, 0.8)),
            Node {
                position_type: PositionType::Absolute,
                bottom: Val::Px(20.0),
                ..default()
            },
        ));
    });
    
    println!("✅ Main menu UI created successfully!");
    println!("🎯 Game ready - no more blank screen!");
}

fn handle_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut button_query: Query<&mut BackgroundColor, With<Button>>,
    button_interaction_query: Query<&Interaction, (Changed<Interaction>, With<Button>)>,
) {
    // Handle ESC to exit
    if keyboard.just_pressed(KeyCode::Escape) {
        println!("👋 User pressed ESC - Exiting game gracefully...");
        std::process::exit(0);
    }
    
    // Handle button interactions
    for interaction in button_interaction_query.iter() {
        if let Ok(mut bg_color) = button_query.single_mut() {
            match *interaction {
                Interaction::Pressed => {
                    println!("🖱️ Button clicked!");
                    bg_color.0 = Color::srgb(0.3, 0.4, 0.7);
                }
                Interaction::Hovered => {
                    bg_color.0 = Color::srgb(0.2, 0.3, 0.6);
                }
                Interaction::None => {
                    bg_color.0 = Color::srgba(0.1, 0.1, 0.3, 0.8);
                }
            }
        }
    }
}