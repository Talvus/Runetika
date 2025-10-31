#[cfg(all(test, feature = "debug"))]
mod debug_tests {
    use bevy::prelude::*;
    use std::collections::HashMap;
    use std::any::TypeId;
    use runetika::type_theory_viz_debug::*;
    use runetika::debug_overlay::*;
    use runetika::type_inspector::*;

    #[test]
    fn test_debug_mode_toggle() {
        let mut app = App::new();
        app.add_plugins(MinimalPlugins)
            .add_state::<DebugMode>()
            .insert_resource(DebugContext::default());
        
        let debug_context = app.world.resource::<DebugContext>();
        assert!(!debug_context.enabled);
        
        // Simulate F12 press
        app.world.resource_mut::<DebugContext>().enabled = true;
        let debug_context = app.world.resource::<DebugContext>();
        assert!(debug_context.enabled);
    }

    #[test]
    fn test_performance_profiler() {
        let mut profiler = PerformanceProfiler::default();
        
        // Add frame times
        profiler.frame_times.push_back(16.67); // ~60 FPS
        profiler.frame_times.push_back(16.67);
        profiler.frame_times.push_back(33.33); // ~30 FPS
        
        assert_eq!(profiler.frame_times.len(), 3);
        
        // Calculate average
        let avg: f32 = profiler.frame_times.iter().sum::<f32>() / profiler.frame_times.len() as f32;
        assert!((avg - 22.22).abs() < 0.1);
    }

    #[test]
    fn test_breakpoint_system() {
        let mut debug_context = DebugContext::default();
        
        let breakpoint = Breakpoint {
            id: BreakpointId(0),
            condition: BreakpointCondition::FrameNumber(100),
            enabled: true,
            hit_count: 0,
            action: BreakpointAction::Pause,
        };
        
        debug_context.breakpoints.push(breakpoint);
        assert_eq!(debug_context.breakpoints.len(), 1);
        assert!(debug_context.breakpoints[0].enabled);
    }

    #[test]
    fn test_type_inspector_registration() {
        let mut registry = TypeRegistry::default();
        
        let type_metadata = TypeMetadata {
            type_id: std::any::TypeId::of::<Transform>(),
            name: "Transform".to_string(),
            size: std::mem::size_of::<Transform>(),
            kind: TypeKind::Component,
            fields: vec![],
            methods: vec![],
            traits: vec![],
        };
        
        registry.types.insert(type_metadata.type_id, type_metadata);
        assert_eq!(registry.types.len(), 1);
    }

    #[test]
    fn test_debug_snapshot() {
        let snapshot = DebugSnapshot {
            timestamp: std::time::Instant::now(),
            frame: 42,
            entities: vec![],
            resources: HashMap::new(),
            metrics: PerformanceMetrics::default(),
        };
        
        assert_eq!(snapshot.frame, 42);
        assert!(snapshot.entities.is_empty());
    }

    #[test]
    fn test_overlay_state() {
        let mut overlay = OverlayState::default();
        assert!(!overlay.visible);
        
        overlay.visible = true;
        overlay.position = OverlayPosition::TopLeft;
        
        assert!(overlay.visible);
        assert!(matches!(overlay.position, OverlayPosition::TopLeft));
    }

    #[test]
    fn test_watch_targets() {
        let mut debug_context = DebugContext::default();
        
        debug_context.watch_list.insert(
            "player_position".to_string(),
            WatchTarget::Performance(MetricType::FPS),
        );
        
        assert_eq!(debug_context.watch_list.len(), 1);
        assert!(debug_context.watch_list.contains_key("player_position"));
    }

    #[test]
    fn test_type_constraints() {
        let constraint = TypeConstraint {
            name: "RequireTransform".to_string(),
            predicate: ConstraintPredicate::ComponentRequires(
                "Mesh".to_string(),
                "Transform".to_string(),
            ),
            severity: ConstraintSeverity::Error,
        };
        
        assert_eq!(constraint.name, "RequireTransform");
        assert!(matches!(constraint.severity, ConstraintSeverity::Error));
    }

    #[test]
    fn test_memory_sampling() {
        let mut profiler = PerformanceProfiler::default();
        
        let sample = MemorySample {
            timestamp: std::time::Instant::now(),
            heap_usage: 1024 * 1024, // 1MB
            entity_count: 100,
            component_pools: HashMap::new(),
        };
        
        profiler.memory_samples.push_back(sample);
        assert_eq!(profiler.memory_samples.len(), 1);
        assert_eq!(profiler.memory_samples[0].entity_count, 100);
    }

    #[test]
    fn test_debug_verbosity_levels() {
        let verbosity = DebugVerbosity::Verbose;
        assert!(matches!(verbosity, DebugVerbosity::Verbose));
        
        let minimal = DebugVerbosity::Minimal;
        assert!(matches!(minimal, DebugVerbosity::Minimal));
    }

    #[test]
    fn test_debug_context_bounds_checking() {
        let mut debug_context = DebugContext::default();
        
        // Test watch list bounds
        for i in 0..DebugContext::MAX_WATCHES {
            let result = debug_context.add_watch(
                format!("watch_{}", i),
                WatchTarget::Performance(MetricType::FPS),
            );
            assert!(result.is_ok());
        }
        
        // Adding one more should fail
        let result = debug_context.add_watch(
            "overflow".to_string(),
            WatchTarget::Performance(MetricType::FPS),
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_performance_profiler_bounds() {
        let mut profiler = PerformanceProfiler::default();
        
        // Test frame times bounds
        for i in 0..150 {
            profiler.add_frame_time(16.67);
        }
        
        // Should maintain max size
        assert_eq!(profiler.frame_times.len(), PerformanceProfiler::MAX_FRAME_TIMES);
        
        // Test system time bounds
        for i in 0..PerformanceProfiler::MAX_SYSTEMS {
            let result = profiler.add_system_time(format!("system_{}", i), 1.0);
            assert!(result.is_ok());
        }
        
        // Adding one more system should fail
        let result = profiler.add_system_time("overflow_system".to_string(), 1.0);
        assert!(result.is_err());
    }

    #[test]
    fn test_debug_history_cleanup() {
        let mut debug_context = DebugContext::default();
        
        // Add more snapshots than the limit
        for i in 0..600 {
            let snapshot = DebugSnapshot {
                timestamp: std::time::Instant::now(),
                frame: i,
                entities: vec![],
                resources: HashMap::new(),
                metrics: PerformanceMetrics::default(),
            };
            debug_context.history.push_back(snapshot);
        }
        
        // Cleanup should reduce to max size
        debug_context.cleanup_history();
        assert_eq!(debug_context.history.len(), DebugContext::MAX_HISTORY);
    }

    #[test]
    fn test_breakpoint_bounds_checking() {
        let mut debug_context = DebugContext::default();
        
        // Add breakpoints up to the limit
        for i in 0..DebugContext::MAX_BREAKPOINTS {
            let breakpoint = Breakpoint {
                id: BreakpointId(i as u32),
                condition: BreakpointCondition::FrameNumber(i as u64),
                enabled: true,
                hit_count: 0,
                action: BreakpointAction::Pause,
            };
            let result = debug_context.add_breakpoint(breakpoint);
            assert!(result.is_ok());
        }
        
        // Adding one more should fail
        let overflow_breakpoint = Breakpoint {
            id: BreakpointId(999),
            condition: BreakpointCondition::FrameNumber(999),
            enabled: true,
            hit_count: 0,
            action: BreakpointAction::Pause,
        };
        let result = debug_context.add_breakpoint(overflow_breakpoint);
        assert!(result.is_err());
    }

    #[test] 
    fn test_memory_sample_limits() {
        let mut profiler = PerformanceProfiler::default();
        
        // Add more memory samples than the limit
        for i in 0..100 {
            let sample = MemorySample {
                timestamp: std::time::Instant::now(),
                heap_usage: i * 1024,
                entity_count: i,
                component_pools: HashMap::new(),
            };
            profiler.add_memory_sample(sample);
        }
        
        // Should maintain max size
        assert_eq!(profiler.memory_samples.len(), PerformanceProfiler::MAX_MEMORY_SAMPLES);
    }
    
    #[test]
    fn test_debug_system_integration() {
        let mut app = App::new();
        app.add_plugins(MinimalPlugins)
            .add_plugins(TypeTheoryDebugPlugin)
            .insert_resource(ButtonInput::<KeyCode>::default());
        
        // Test that debug systems are properly registered
        let debug_context = app.world.resource::<DebugContext>();
        assert!(!debug_context.enabled);
        
        let profiler = app.world.resource::<PerformanceProfiler>();
        assert!(!profiler.recording);
        
        // Run one update to ensure systems work without panicking
        app.update();
    }
}