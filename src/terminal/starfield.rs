use bevy::prelude::*;
use rand::Rng;

#[derive(Component)]
pub struct Star {
    pub speed: f32,
    pub brightness: f32,
    pub twinkle_speed: f32,
    pub size: f32,
}

#[derive(Component)]
pub struct Starfield;

#[derive(Component)]
pub struct TerminalBackdrop;

pub fn setup_starfield(
    mut commands: Commands,
) {
    // Create backdrop
    commands.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            ..default()
        },
        BackgroundColor(Color::srgb(0.02, 0.0, 0.05)), // Very dark purple space
        TerminalBackdrop,
        ZIndex(-100),
    ));
    
    // Create starfield container
    commands.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            ..default()
        },
        Starfield,
        ZIndex(-99),
    ))
    .with_children(|parent| {
        let mut rng = rand::thread_rng();
        
        // Generate stars
        for _ in 0..150 {
            let x = rng.gen_range(0.0..100.0);
            let y = rng.gen_range(0.0..100.0);
            let size = rng.gen_range(1.0..4.0);
            let brightness = rng.gen_range(0.3..1.0);
            let twinkle_speed = rng.gen_range(1.0..4.0);
            
            parent.spawn((
                Node {
                    width: Val::Px(size),
                    height: Val::Px(size),
                    position_type: PositionType::Absolute,
                    left: Val::Percent(x),
                    top: Val::Percent(y),
                    ..default()
                },
                BackgroundColor(Color::srgba(
                    0.8 + rng.gen_range(0.0..0.2),
                    0.7 + rng.gen_range(0.0..0.3),
                    1.0,
                    brightness
                )),
                BorderRadius::all(Val::Percent(50.0)),
                Star {
                    speed: rng.gen_range(0.05..0.3),
                    brightness,
                    twinkle_speed,
                    size,
                },
            ));
        }
        
        // Add some nebula clouds
        for _ in 0..3 {
            let x = rng.gen_range(10.0..90.0);
            let y = rng.gen_range(10.0..90.0);
            let size = rng.gen_range(200.0..400.0);
            
            parent.spawn((
                Node {
                    width: Val::Px(size),
                    height: Val::Px(size),
                    position_type: PositionType::Absolute,
                    left: Val::Percent(x),
                    top: Val::Percent(y),
                    ..default()
                },
                BackgroundColor(Color::srgba(
                    0.6,
                    0.2,
                    0.9,
                    0.02
                )),
                BorderRadius::all(Val::Percent(50.0)),
            ));
        }
    });
}

pub fn animate_stars(
    time: Res<Time>,
    mut star_query: Query<(&mut Node, &mut BackgroundColor, &Star)>,
) {
    for (mut node, mut bg_color, star) in star_query.iter_mut() {
        // Twinkle effect
        let twinkle = (time.elapsed_secs() * star.twinkle_speed).sin() * 0.3 + 0.7;
        bg_color.0.set_alpha(star.brightness * twinkle);
        
        // Slow drift
        if let Val::Percent(mut x) = node.left {
            x += star.speed * time.delta_secs();
            if x > 100.0 {
                x = -2.0;
            }
            node.left = Val::Percent(x);
        }
    }
}

pub fn create_scanline_effect(
    mut commands: Commands,
) {
    // Add subtle scanline overlay
    commands.spawn((
        Node {
            width: Val::Percent(100.0),
            height: Val::Percent(100.0),
            position_type: PositionType::Absolute,
            ..default()
        },
        BackgroundColor(Color::NONE),
        ZIndex(1000),
    ))
    .with_children(|parent| {
        // Create horizontal scanlines
        for i in 0..30 {
            parent.spawn((
                Node {
                    width: Val::Percent(100.0),
                    height: Val::Px(1.0),
                    position_type: PositionType::Absolute,
                    top: Val::Px(i as f32 * 20.0),
                    ..default()
                },
                BackgroundColor(Color::srgba(0.5, 0.2, 0.8, 0.02)),
            ));
        }
    });
}