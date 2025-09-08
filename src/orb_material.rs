use bevy::prelude::*;
use bevy::render::render_resource::{AsBindGroup, ShaderRef};
use bevy::pbr::Material;
use bevy::render::mesh::shape::{Box as BoxShape, Icosphere};

#[derive(AsBindGroup, Debug, Clone, Asset, Reflect)]
pub struct OrbMaterial {
    #[uniform(0)]
    pub color: Vec4,
    #[uniform(1)]
    pub glow_strength: f32,
}

impl Material for OrbMaterial {
    fn fragment_shader() -> ShaderRef {
        "shaders/orb_glow.wgsl".into()
    }
} 