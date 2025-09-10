mod arc_engine;
mod mvp_terminal;
mod silicon_mind_mvp;
mod pattern_echo_mvp;

use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Runetika MVP - Silicon Mind".into(),
                resolution: (1280., 800.).into(),
                ..default()
            }),
            ..default()
        }))
        .add_plugins((
            arc_engine::ARCEnginePlugin,
            mvp_terminal::MVPTerminalPlugin,
            silicon_mind_mvp::SiliconMindMVPPlugin,
            pattern_echo_mvp::PatternEchoMVPPlugin,
        ))
        .run();
}