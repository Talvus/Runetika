@group(1) @binding(0)
var<uniform> color: vec4<f32>;
@group(1) @binding(1)
var<uniform> glow_strength: f32;

@fragment
fn fragment_main(
    @location(0) uv: vec2<f32>,
    @builtin(front_facing) front_facing: bool
) -> @location(0) vec4<f32> {
    let dist = length(uv - vec2(0.5, 0.5));
    let glow = smoothstep(0.4, 0.5, dist) * glow_strength;
    let orb = smoothstep(0.5, 0.4, dist);
    let base = color.rgb * orb;
    let glow_col = color.rgb * glow;
    return vec4(base + glow_col, color.a * (orb + glow));
} 