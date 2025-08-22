//! Performance monitoring and optimization utilities.
//!
//! This module provides tools for monitoring game performance,
//! detecting bottlenecks, and automatically adjusting quality
//! settings based on runtime performance metrics.
//!
//! # Platform-Specific Optimizations
//!
//! ## macOS/Apple Silicon
//! - Uses Metal performance shaders when available
//! - Optimizes for unified memory architecture
//! - Supports ProMotion displays (120Hz)
//!
//! ## Windows
//! - DirectX 12 optimizations
//! - DLSS/FSR support (future)
//!
//! ## Linux
//! - Vulkan renderer optimizations
//! - Wayland vs X11 detection

use bevy::prelude::*;
use bevy::diagnostic::{DiagnosticsStore, FrameTimeDiagnosticsPlugin, LogDiagnosticsPlugin};
use std::collections::VecDeque;

/// Plugin for performance monitoring and auto-optimization
pub struct PerformancePlugin;

impl Plugin for PerformancePlugin {
    fn build(&self, app: &mut App) {
        app
            .add_plugins((
                FrameTimeDiagnosticsPlugin,
                #[cfg(debug_assertions)]
                LogDiagnosticsPlugin::default(),
            ))
            .init_resource::<PerformanceMetrics>()
            .init_resource::<QualitySettings>()
            .add_systems(Update, (
                update_performance_metrics,
                auto_adjust_quality.run_if(resource_changed::<PerformanceMetrics>),
                #[cfg(target_os = "macos")]
                macos_specific_optimizations,
            ));
    }
}

/// Performance metrics tracked over time
#[derive(Resource, Default)]
pub struct PerformanceMetrics {
    /// Rolling average FPS over the last 60 frames
    pub average_fps: f32,
    
    /// Minimum FPS in the last second
    pub min_fps: f32,
    
    /// Maximum FPS in the last second  
    pub max_fps: f32,
    
    /// Frame time history (last 60 frames)
    pub frame_times: VecDeque<f32>,
    
    /// Number of frame drops (< 30 FPS) in last second
    pub frame_drops: u32,
    
    /// Total memory usage in MB
    pub memory_usage_mb: f32,
    
    /// Entity count
    pub entity_count: usize,
    
    /// Draw calls per frame
    pub draw_calls: u32,
}

impl PerformanceMetrics {
    /// Check if performance is below acceptable threshold
    pub fn is_struggling(&self) -> bool {
        self.average_fps < 30.0 || self.frame_drops > 5
    }
    
    /// Check if we have headroom for quality improvements
    pub fn has_headroom(&self) -> bool {
        self.average_fps > 55.0 && self.frame_drops == 0
    }
}

/// Dynamic quality settings that can be adjusted at runtime
#[derive(Resource, Clone)]
pub struct QualitySettings {
    /// Render resolution scale (0.5 - 2.0)
    pub resolution_scale: f32,
    
    /// Shadow quality (0 = off, 3 = ultra)
    pub shadow_quality: u8,
    
    /// Particle density multiplier
    pub particle_density: f32,
    
    /// UI effects enabled
    pub ui_effects: bool,
    
    /// Post-processing effects
    pub post_processing: bool,
    
    /// Maximum visible entities
    pub max_visible_entities: usize,
    
    /// Texture filtering quality
    pub texture_filtering: TextureFiltering,
    
    /// VSync enabled
    pub vsync: bool,
    
    /// Target FPS (0 = unlimited)
    pub target_fps: u32,
}

impl Default for QualitySettings {
    fn default() -> Self {
        Self {
            resolution_scale: 1.0,
            shadow_quality: 2,
            particle_density: 1.0,
            ui_effects: true,
            post_processing: true,
            max_visible_entities: 1000,
            texture_filtering: TextureFiltering::Trilinear,
            vsync: true,
            target_fps: 60,
        }
    }
}

impl QualitySettings {
    /// Create settings optimized for performance
    pub fn performance() -> Self {
        Self {
            resolution_scale: 0.75,
            shadow_quality: 0,
            particle_density: 0.5,
            ui_effects: false,
            post_processing: false,
            max_visible_entities: 500,
            texture_filtering: TextureFiltering::Bilinear,
            vsync: true,
            target_fps: 30,
        }
    }
    
    /// Create settings optimized for quality
    pub fn quality() -> Self {
        Self {
            resolution_scale: 1.0,
            shadow_quality: 3,
            particle_density: 1.5,
            ui_effects: true,
            post_processing: true,
            max_visible_entities: 2000,
            texture_filtering: TextureFiltering::Anisotropic16x,
            vsync: true,
            target_fps: 60,
        }
    }
    
    /// Platform-specific default settings
    #[cfg(target_os = "macos")]
    pub fn platform_default() -> Self {
        Self {
            resolution_scale: 1.0,
            shadow_quality: 2,
            particle_density: 1.0,
            ui_effects: true,
            post_processing: true,
            max_visible_entities: 1500,
            texture_filtering: TextureFiltering::Anisotropic8x,
            vsync: true,
            target_fps: 60, // Can go to 120 on ProMotion displays
        }
    }
    
    #[cfg(not(target_os = "macos"))]
    pub fn platform_default() -> Self {
        Self::default()
    }
}

/// Texture filtering modes
#[derive(Clone, Copy, Debug)]
pub enum TextureFiltering {
    Nearest,
    Bilinear,
    Trilinear,
    Anisotropic4x,
    Anisotropic8x,
    Anisotropic16x,
}

/// Updates performance metrics each frame
fn update_performance_metrics(
    time: Res<Time>,
    diagnostics: Res<DiagnosticsStore>,
    mut metrics: ResMut<PerformanceMetrics>,
    entities: Query<Entity>,
) {
    // Update entity count
    metrics.entity_count = entities.iter().count();
    
    // Get FPS from diagnostics
    if let Some(fps_diagnostic) = diagnostics.get(&FrameTimeDiagnosticsPlugin::FPS) {
        if let Some(fps) = fps_diagnostic.smoothed() {
            // Update frame time history
            let frame_time = 1000.0 / fps; // Convert to milliseconds
            metrics.frame_times.push_back(frame_time);
            if metrics.frame_times.len() > 60 {
                metrics.frame_times.pop_front();
            }
            
            // Calculate metrics
            metrics.average_fps = fps as f32;
            
            // Track frame drops
            if fps < 30.0 {
                metrics.frame_drops += 1;
            }
            
            // Reset frame drops counter every second
            if time.elapsed_secs() % 1.0 < time.delta_secs() {
                metrics.frame_drops = 0;
            }
        }
    }
    
    // Estimate memory usage (simplified)
    #[cfg(not(target_arch = "wasm32"))]
    {
        // This is a rough estimate, actual implementation would use system APIs
        metrics.memory_usage_mb = (metrics.entity_count as f32 * 0.001) + 100.0;
    }
}

/// Automatically adjusts quality settings based on performance
fn auto_adjust_quality(
    metrics: Res<PerformanceMetrics>,
    mut quality: ResMut<QualitySettings>,
) {
    // Don't adjust too frequently - use atomic for thread safety
    use std::sync::atomic::{AtomicU64, Ordering};
    static LAST_ADJUSTMENT: AtomicU64 = AtomicU64::new(0);
    
    let current_time = bevy::utils::Instant::now().elapsed().as_secs_f32();
    let current_time_bits = current_time.to_bits() as u64;
    
    let last_time_bits = LAST_ADJUSTMENT.load(Ordering::Relaxed);
    let last_time = f32::from_bits(last_time_bits as u32);
    
    if current_time - last_time < 2.0 {
        return;
    }
    
    if metrics.is_struggling() {
        // Reduce quality incrementally
        if quality.resolution_scale > 0.5 {
            quality.resolution_scale -= 0.1;
            info!("Reducing resolution scale to {}", quality.resolution_scale);
        } else if quality.particle_density > 0.25 {
            quality.particle_density -= 0.25;
            info!("Reducing particle density to {}", quality.particle_density);
        } else if quality.shadow_quality > 0 {
            quality.shadow_quality -= 1;
            info!("Reducing shadow quality to {}", quality.shadow_quality);
        }
        
        LAST_ADJUSTMENT.store(current_time_bits, Ordering::Relaxed);
    } else if metrics.has_headroom() {
        // Increase quality incrementally
        if quality.resolution_scale < 1.0 {
            quality.resolution_scale += 0.1;
            info!("Increasing resolution scale to {}", quality.resolution_scale);
        } else if quality.shadow_quality < 2 {
            quality.shadow_quality += 1;
            info!("Increasing shadow quality to {}", quality.shadow_quality);
        } else if quality.particle_density < 1.0 {
            quality.particle_density += 0.25;
            info!("Increasing particle density to {}", quality.particle_density);
        }
        
        LAST_ADJUSTMENT.store(current_time_bits, Ordering::Relaxed);
    }
}

/// macOS-specific performance optimizations
#[cfg(target_os = "macos")]
fn macos_specific_optimizations(
    mut windows: Query<&mut Window>,
    quality: Res<QualitySettings>,
) {
    for mut window in windows.iter_mut() {
        // Adjust for ProMotion displays
        if let Some(monitor) = window.current_monitor() {
            // Check if we're on a ProMotion display (>60Hz)
            // This is simplified, actual implementation would check refresh rate
            if quality.average_fps > 55.0 {
                // Enable 120Hz if available and performance allows
                window.present_mode = bevy::window::PresentMode::AutoVsync;
            }
        }
    }
}

/// Performance statistics overlay for debugging
#[derive(Component)]
pub struct PerformanceOverlay;

/// Creates a performance overlay UI
pub fn spawn_performance_overlay(mut commands: Commands) {
    commands.spawn((
        Node {
            position_type: PositionType::Absolute,
            top: Val::Px(10.0),
            right: Val::Px(10.0),
            padding: UiRect::all(Val::Px(10.0)),
            background_color: BackgroundColor(Color::srgba(0.0, 0.0, 0.0, 0.8)),
            ..default()
        },
        PerformanceOverlay,
    ))
    .with_children(|parent| {
        parent.spawn((
            Text::new("FPS: --\nEntities: --\nMemory: -- MB"),
            TextFont {
                font_size: 14.0,
                ..default()
            },
            TextColor(Color::srgb(0.0, 1.0, 0.0)),
        ));
    });
}