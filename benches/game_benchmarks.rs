use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use bevy::prelude::*;
use bevy::ecs::world::World;
use bevy::app::App;

// Benchmark ECS query performance
fn bench_ecs_queries(c: &mut Criterion) {
    let mut group = c.benchmark_group("ecs_queries");
    
    // Test different entity counts
    for entity_count in [100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(entity_count),
            entity_count,
            |b, &entity_count| {
                let mut world = World::new();
                
                // Spawn entities with components
                for i in 0..entity_count {
                    world.spawn((
                        Transform::from_xyz(i as f32, 0.0, 0.0),
                        GlobalTransform::default(),
                    ));
                }
                
                b.iter(|| {
                    // Benchmark query iteration
                    let mut query = world.query::<(&Transform, &GlobalTransform)>();
                    for (transform, global) in query.iter(&world) {
                        black_box(transform);
                        black_box(global);
                    }
                });
            },
        );
    }
    
    group.finish();
}

// Benchmark asset loading performance
fn bench_asset_loading(c: &mut Criterion) {
    c.bench_function("asset_handle_creation", |b| {
        b.iter(|| {
            // Simulate asset handle creation
            let handles: Vec<Handle<Image>> = (0..100)
                .map(|i| Handle::weak(AssetId::Uuid { 
                    uuid: bevy::utils::Uuid::new_v4() 
                }))
                .collect();
            black_box(handles);
        });
    });
}

// Benchmark math operations common in games
fn bench_math_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_operations");
    
    group.bench_function("vec3_operations", |b| {
        let v1 = Vec3::new(1.0, 2.0, 3.0);
        let v2 = Vec3::new(4.0, 5.0, 6.0);
        
        b.iter(|| {
            let result = black_box(v1)
                .normalize()
                .cross(black_box(v2))
                .dot(black_box(v1));
            black_box(result);
        });
    });
    
    group.bench_function("transform_multiplication", |b| {
        let t1 = Transform::from_xyz(1.0, 2.0, 3.0);
        let t2 = Transform::from_rotation(Quat::from_rotation_x(0.5));
        
        b.iter(|| {
            let result = black_box(t1).mul_transform(black_box(t2));
            black_box(result);
        });
    });
    
    group.finish();
}

// Benchmark text rendering operations
fn bench_text_operations(c: &mut Criterion) {
    c.bench_function("text_creation", |b| {
        b.iter(|| {
            let text = Text::from_section(
                "Benchmark Text",
                TextStyle {
                    font_size: 30.0,
                    color: Color::WHITE,
                    ..default()
                },
            );
            black_box(text);
        });
    });
}

criterion_group!(
    benches,
    bench_ecs_queries,
    bench_asset_loading,
    bench_math_operations,
    bench_text_operations
);
criterion_main!(benches);