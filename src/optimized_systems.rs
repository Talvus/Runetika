// Optimized ECS systems for Runetika
// Demonstrates performance best practices

use bevy::prelude::*;
use bevy::ecs::query::QueryEntityError;

/// Marker for entities that need frequent updates
#[derive(Component)]
pub struct ActiveEntity;

/// Packed component for better cache locality
#[repr(C, align(16))]  // Align for SIMD
#[derive(Component, Clone, Copy)]
pub struct PackedTransform {
    pub position: Vec3,
    pub rotation: f32,  // 2D rotation only
    pub scale: Vec2,
    _padding: [f32; 2],  // Padding for alignment
}

/// Optimized velocity component
#[repr(C, align(16))]
#[derive(Component, Clone, Copy)]
pub struct Velocity {
    pub linear: Vec2,
    pub angular: f32,
    _padding: f32,
}

/// Spatial hash for broad-phase collision detection
#[derive(Resource)]
pub struct SpatialHash {
    cell_size: f32,
    buckets: Vec<Vec<Entity>>,
    width: usize,
    height: usize,
}

impl SpatialHash {
    pub fn new(world_size: Vec2, cell_size: f32) -> Self {
        let width = (world_size.x / cell_size).ceil() as usize;
        let height = (world_size.y / cell_size).ceil() as usize;
        
        Self {
            cell_size,
            buckets: vec![Vec::new(); width * height],
            width,
            height,
        }
    }
    
    #[inline(always)]
    fn hash(&self, position: Vec2) -> usize {
        let x = ((position.x / self.cell_size) as usize).min(self.width - 1);
        let y = ((position.y / self.cell_size) as usize).min(self.height - 1);
        y * self.width + x
    }
    
    pub fn clear(&mut self) {
        for bucket in &mut self.buckets {
            bucket.clear();
        }
    }
    
    pub fn insert(&mut self, entity: Entity, position: Vec2) {
        let index = self.hash(position);
        self.buckets[index].push(entity);
    }
    
    pub fn query_range(&self, position: Vec2, radius: f32) -> Vec<Entity> {
        let mut results = Vec::new();
        
        let min_x = ((position.x - radius) / self.cell_size).floor() as i32;
        let max_x = ((position.x + radius) / self.cell_size).ceil() as i32;
        let min_y = ((position.y - radius) / self.cell_size).floor() as i32;
        let max_y = ((position.y + radius) / self.cell_size).ceil() as i32;
        
        for y in min_y..=max_y {
            for x in min_x..=max_x {
                if x >= 0 && x < self.width as i32 && y >= 0 && y < self.height as i32 {
                    let index = (y as usize) * self.width + (x as usize);
                    results.extend_from_slice(&self.buckets[index]);
                }
            }
        }
        
        results
    }
}

/// Optimized movement system using SIMD-friendly operations
pub fn optimized_movement_system(
    time: Res<Time>,
    mut query: Query<(&mut PackedTransform, &Velocity), With<ActiveEntity>>,
) {
    let dt = time.delta_seconds();
    
    // Use par_iter for parallel processing on multi-core systems
    query.par_iter_mut().for_each(|(mut transform, velocity)| {
        // Vectorized operations
        transform.position.x += velocity.linear.x * dt;
        transform.position.y += velocity.linear.y * dt;
        transform.rotation += velocity.angular * dt;
        
        // Keep rotation in valid range
        if transform.rotation > std::f32::consts::TAU {
            transform.rotation -= std::f32::consts::TAU;
        }
    });
}

/// Optimized collision system using spatial hashing
pub fn optimized_collision_system(
    mut spatial_hash: ResMut<SpatialHash>,
    query: Query<(Entity, &PackedTransform), With<ActiveEntity>>,
) {
    // Clear and rebuild spatial hash
    spatial_hash.clear();
    
    // First pass: insert all entities into spatial hash
    for (entity, transform) in query.iter() {
        spatial_hash.insert(entity, transform.position.truncate());
    }
    
    // Second pass: check collisions using spatial hash
    for (entity, transform) in query.iter() {
        let nearby = spatial_hash.query_range(transform.position.truncate(), 50.0);
        
        // Process only nearby entities
        for &other in &nearby {
            if entity != other {
                // Collision check would go here
                // Using spatial hash reduces checks from O(n²) to O(n·k) where k << n
            }
        }
    }
}

/// Batch spawn entities efficiently
pub fn batch_spawn_entities(mut commands: Commands, count: usize) {
    // Pre-allocate space
    let mut entities = Vec::with_capacity(count);
    
    // Batch spawn for better performance
    commands.spawn_batch((0..count).map(|i| {
        (
            PackedTransform {
                position: Vec3::new(i as f32 * 10.0, 0.0, 0.0),
                rotation: 0.0,
                scale: Vec2::ONE,
                _padding: [0.0; 2],
            },
            Velocity {
                linear: Vec2::new(1.0, 0.0),
                angular: 0.1,
                _padding: 0.0,
            },
            ActiveEntity,
        )
    }));
}

/// Query filtering optimization
pub fn filtered_query_system(
    query: Query<&PackedTransform, (With<ActiveEntity>, Without<Velocity>)>,
) {
    // Using filters in the type system is faster than runtime checks
    for transform in query.iter() {
        // Process only entities that match the filter
    }
}

/// Change detection optimization
pub fn change_detection_system(
    query: Query<&PackedTransform, Changed<PackedTransform>>,
) {
    // Only process entities that changed this frame
    for transform in query.iter() {
        // This dramatically reduces work when most entities are static
    }
}

/// Manual query optimization for hot paths
pub fn manual_query_optimization(
    world: &World,
    entity: Entity,
) -> Result<Vec3, QueryEntityError> {
    // For extremely hot paths, manual world access can be faster
    let transform = world.get::<PackedTransform>(entity)?;
    Ok(transform.position)
}

/// System ordering for cache efficiency
pub struct OptimizedSystemSet;

impl OptimizedSystemSet {
    pub fn configure(app: &mut App) {
        // Group systems that access the same components
        app.add_systems(Update, (
            // These systems access Transform and Velocity
            optimized_movement_system,
            optimized_collision_system,
        ).chain());  // Chain ensures they run in order
        
        // Run independent systems in parallel
        app.add_systems(Update, (
            filtered_query_system,
            change_detection_system,
        ));  // These can run in parallel
    }
}

/// Resource pooling for temporary allocations
#[derive(Resource)]
pub struct VectorPool {
    available: Vec<Vec<Entity>>,
}

impl VectorPool {
    pub fn new(initial_capacity: usize) -> Self {
        let mut available = Vec::with_capacity(initial_capacity);
        for _ in 0..initial_capacity {
            available.push(Vec::with_capacity(100));
        }
        Self { available }
    }
    
    pub fn acquire(&mut self) -> Vec<Entity> {
        self.available.pop().unwrap_or_else(|| Vec::with_capacity(100))
    }
    
    pub fn release(&mut self, mut vec: Vec<Entity>) {
        vec.clear();
        if self.available.len() < 100 {  // Keep pool size reasonable
            self.available.push(vec);
        }
    }
}

/// Compile-time optimization using const generics
pub struct FixedSizeBuffer<const N: usize> {
    data: [f32; N],
}

impl<const N: usize> FixedSizeBuffer<N> {
    pub const fn new() -> Self {
        Self { data: [0.0; N] }
    }
    
    #[inline(always)]
    pub fn process(&mut self) {
        // Compiler can optimize this loop since N is known at compile time
        for i in 0..N {
            self.data[i] *= 2.0;
        }
    }
}