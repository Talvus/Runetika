use bevy::prelude::*;

#[derive(Component)]
pub struct MainMenu;

#[derive(Component)]
pub struct MenuButton {
    pub index: usize,
    pub action: MenuAction,
}

#[derive(Component)]
pub struct MenuTitle;

#[derive(Component)]
pub struct MenuBackground;

#[derive(Component)]
pub struct MenuParticle {
    pub velocity: Vec2,
    pub lifetime: f32,
}

#[derive(Component)]
pub struct MenuStarfield;

#[derive(Clone, Copy, Debug)]
pub enum MenuAction {
    StartGame,
    OpenTerminal,
    Settings,
    Credits,
    Exit,
}

#[derive(Component)]
pub struct SelectedMarker;

#[derive(Component)]
pub struct MenuGlow {
    pub intensity: f32,
    pub speed: f32,
}