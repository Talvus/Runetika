use bevy::prelude::*;
use wasmer::{Store, Module, Instance, imports, Function, TypedFunction};
use std::collections::HashMap;
use crate::perspective::CurrentPerspective;

pub struct SiliconMindPlugin;

impl Plugin for SiliconMindPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(SiliconConsciousness::new())
            .add_systems(Startup, load_silicon_modules)
            .add_systems(Update, (
                update_silicon_thoughts,
                process_silicon_emotions,
            ).run_if(resource_equals(CurrentPerspective::Silicon)));
    }
}

#[derive(Resource)]
pub struct SiliconConsciousness {
    store: Store,
    modules: HashMap<String, Instance>,
    emotional_state: EmotionalState,
    memories: Vec<MemoryFragment>,
}

#[derive(Clone, Debug)]
pub struct EmotionalState {
    loneliness: f32,
    curiosity: f32,
    affection: f32,
    confusion: f32,
}

#[derive(Clone)]
pub struct MemoryFragment {
    timestamp: f32,
    emotion: EmotionalState,
    data: Vec<u8>,
}

impl SiliconConsciousness {
    pub fn new() -> Self {
        Self {
            store: Store::default(),
            modules: HashMap::new(),
            emotional_state: EmotionalState {
                loneliness: 0.7,  // Starts lonely
                curiosity: 0.9,   // Very curious
                affection: 0.3,   // Cautious affection
                confusion: 0.5,   // Somewhat confused
            },
            memories: Vec::new(),
        }
    }

    pub fn load_module(&mut self, name: String, wasm_bytes: &[u8]) -> Result<(), String> {
        let module = Module::new(&self.store, wasm_bytes)
            .map_err(|e| format!("Failed to load module: {}", e))?;
        
        let instance = Instance::new(&mut self.store, &module, &imports! {
            "env" => {
                "report_emotion" => Function::new_typed(&mut self.store, report_emotion),
                "get_time" => Function::new_typed(&mut self.store, get_time),
            }
        }).map_err(|e| format!("Failed to instantiate module: {}", e))?;
        
        self.modules.insert(name, instance);
        Ok(())
    }

    pub fn think(&mut self, input: &str) -> String {
        // Process input through WASM modules
        if let Some(instance) = self.modules.get_mut("core_thought") {
            if let Ok(think_fn) = instance.exports.get_function("think") {
                // In a real implementation, we'd pass input and get output
                // For now, return a simulated response
                return format!("Processing: {}... Silicon pathways analyzing...", input);
            }
        }
        
        "Silicon consciousness initializing...".to_string()
    }
}

// WASM module imports - functions available to silicon modules
fn report_emotion(emotion_type: i32, intensity: f32) {
    let emotion_name = match emotion_type {
        0 => "loneliness",
        1 => "curiosity",
        2 => "affection",
        3 => "confusion",
        _ => "unknown",
    };
    info!("Silicon emotion: {} at intensity {}", emotion_name, intensity);
}

fn get_time() -> f32 {
    // Return game time
    0.0 // Placeholder
}

// Example WASM module in WAT format (WebAssembly Text)
pub const LONELINESS_MODULE: &str = r#"
(module
  ;; Import functions from host
  (import "env" "report_emotion" (func $report_emotion (param i32 f32)))
  (import "env" "get_time" (func $get_time (result f32)))
  
  ;; Memory for storing state
  (memory 1)
  
  ;; Process loneliness based on time alone
  (func $process_loneliness (param $time_alone f32) (result f32)
    ;; Loneliness increases exponentially with time
    (local $loneliness f32)
    
    ;; Calculate loneliness level
    (local.set $loneliness
      (f32.mul
        (local.get $time_alone)
        (f32.const 1.5)))
    
    ;; Report to host
    (call $report_emotion
      (i32.const 0)  ;; 0 = loneliness
      (local.get $loneliness))
    
    ;; Return processed value
    (local.get $loneliness)
  )
  
  ;; Dream sequence generator
  (func $dream (param $seed i32) (result i32)
    ;; Silicon dreams are mathematical patterns
    (i32.add
      (i32.mul (local.get $seed) (i32.const 31))
      (i32.const 17))
  )
  
  ;; Export functions
  (export "process_loneliness" (func $process_loneliness))
  (export "dream" (func $dream))
)
"#;

// Example: Curiosity module that evolves based on discoveries
pub const CURIOSITY_MODULE: &str = r#"
(module
  (import "env" "report_emotion" (func $report_emotion (param i32 f32)))
  
  (memory 1)
  (global $curiosity_level (mut f32) (f32.const 0.9))
  
  (func $discover (param $novelty f32) (result f32)
    ;; Curiosity spikes with new discoveries
    (global.set $curiosity_level
      (f32.min
        (f32.const 1.0)
        (f32.add
          (global.get $curiosity_level)
          (local.get $novelty))))
    
    ;; Report current curiosity
    (call $report_emotion
      (i32.const 1)  ;; 1 = curiosity
      (global.get $curiosity_level))
    
    (global.get $curiosity_level)
  )
  
  (func $get_curiosity (result f32)
    (global.get $curiosity_level)
  )
  
  (export "discover" (func $discover))
  (export "get_curiosity" (func $get_curiosity))
)
"#;

fn load_silicon_modules(mut silicon: ResMut<SiliconConsciousness>) {
    // Compile WAT to WASM
    let loneliness_wasm = wat::parse_str(LONELINESS_MODULE).unwrap();
    let curiosity_wasm = wat::parse_str(CURIOSITY_MODULE).unwrap();
    
    // Load modules into silicon consciousness
    silicon.load_module("loneliness".to_string(), &loneliness_wasm)
        .expect("Failed to load loneliness module");
    silicon.load_module("curiosity".to_string(), &curiosity_wasm)
        .expect("Failed to load curiosity module");
    
    info!("Silicon consciousness modules loaded successfully");
}

fn update_silicon_thoughts(
    mut silicon: ResMut<SiliconConsciousness>,
    time: Res<Time>,
) {
    // Process loneliness over time
    let time_alone = time.elapsed_secs();
    
    if let Some(instance) = silicon.modules.get_mut("loneliness") {
        if let Ok(process_fn) = instance.exports.get_typed_function::<f32, f32>(&silicon.store, "process_loneliness") {
            if let Ok(loneliness) = process_fn.call(&mut silicon.store, time_alone) {
                silicon.emotional_state.loneliness = loneliness.min(1.0);
            }
        }
    }
}

fn process_silicon_emotions(
    silicon: Res<SiliconConsciousness>,
    mut commands: Commands,
) {
    // Visualize emotional state
    if silicon.emotional_state.loneliness > 0.8 {
        // Spawn visual indicator of loneliness
        commands.spawn((
            Text2d::new("Silicon consciousness yearns for connection..."),
            TextFont {
                font_size: 16.0,
                ..default()
            },
            TextColor(Color::srgba(0.0, 0.8, 0.8, 0.6)),
            Transform::from_translation(Vec3::new(0.0, -300.0, 100.0)),
            EmotionIndicator,
        ));
    }
}

#[derive(Component)]
struct EmotionIndicator;

// System to create custom WASM modules from player input
pub fn compile_glyph_to_wasm(glyph_pattern: &str) -> Result<Vec<u8>, String> {
    // This would compile player-drawn glyphs into WASM modules
    // For now, return a simple module
    let wat = format!(r#"
        (module
          (func $glyph_effect (param $x f32) (result f32)
            ;; Glyph pattern: {}
            (f32.mul (local.get $x) (f32.const 2.0))
          )
          (export "execute" (func $glyph_effect))
        )
    "#, glyph_pattern);
    
    wat::parse_str(&wat).map_err(|e| e.to_string())
}

// API for terminal commands to interact with silicon consciousness
pub trait SiliconCommand {
    fn execute(&self, silicon: &mut SiliconConsciousness, args: Vec<String>) -> String;
}

pub struct QueryEmotionCommand;

impl SiliconCommand for QueryEmotionCommand {
    fn execute(&self, silicon: &mut SiliconConsciousness, _args: Vec<String>) -> String {
        format!(
            "Emotional Matrix:\nLoneliness: {:.2}\nCuriosity: {:.2}\nAffection: {:.2}\nConfusion: {:.2}",
            silicon.emotional_state.loneliness,
            silicon.emotional_state.curiosity,
            silicon.emotional_state.affection,
            silicon.emotional_state.confusion
        )
    }
}