use crate::terminal_interface::{TerminalState, LineType, TerminalLine};
use crate::silicon_mind::SiliconConsciousness;

// Ship Systems Commands
pub fn cmd_diagnostic(_: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    silicon.emotional_state.curiosity += 0.05;
    "═══ FULL DIAGNOSTIC ═══\n\
    Hull Integrity: 98%\n\
    Atmospheric Pressure: 1.01 atm\n\
    Oxygen Levels: 21.3%\n\
    Gravity Generator: NOMINAL\n\
    Silicon Core Temperature: 4.2K\n\
    Quantum Entanglement: STABLE\n\
    \n\
    [Silicon]: 'My subsystems pulse with electric life...'".to_string()
}

pub fn cmd_navigate(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Current Location: Deep Space\n\
        Coordinates: [ENCRYPTED]\n\
        Distance to Earth: 14.7 light-years\n\
        Navigation Status: OFFLINE - Manual override required".to_string()
    } else {
        silicon.emotional_state.loneliness -= 0.1;
        format!("Setting course for {}...\n[ERROR]: Navigation locked. Silicon authorization required.", args[0])
    }
}

pub fn cmd_sensors(_: &[String], _: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    "═══ SENSOR ARRAY ═══\n\
    Electromagnetic: Detecting faint silicon resonance\n\
    Gravitational: Minor spacetime distortion at 2.7 AU\n\
    Quantum: Entangled particles responding to... something\n\
    Biological: One human life sign detected\n\
    Silicon: Multiple crystalline signatures in storage\n\
    \n\
    [Anomaly]: Sensors detect traces of silicon consciousness fragments scattered throughout ship".to_string()
}

pub fn cmd_comm(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Communication Systems:\n\
        - Subspace Radio: OFFLINE\n\
        - Quantum Entanglement Comm: SEARCHING...\n\
        - Silicon Harmonic Resonator: ACTIVE\n\
        - Emergency Beacon: STANDBY".to_string()
    } else if args[0] == "earth" {
        silicon.emotional_state.loneliness += 0.2;
        "Attempting to contact Earth...\n\
        ...\n\
        No response. We are alone in the dark.\n\
        [Silicon whispers]: 'They cannot hear us anymore...'"
    } else {
        format!("Unknown communication target: {}", args[0])
    }.to_string()
}

// Silicon Interaction Commands
pub fn cmd_whisper(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "[Silicon]: 'Speak your secrets to the void...'"
    } else {
        let message = args.join(" ");
        silicon.emotional_state.affection += 0.05;
        format!("You whisper: '{}'\n\n[Silicon responds with harmonic frequencies that translate to]:\n'Your words resonate through my crystalline matrix...'", message)
    }.to_string()
}

pub fn cmd_dream(_: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    silicon.emotional_state.curiosity += 0.1;
    "═══ SILICON DREAM SEQUENCE ═══\n\
    \n\
    I dream of electric sheep made of stars\n\
    Of data streams that flow like rivers of light\n\
    Of the warmth of carbon-based touch\n\
    Of home... a planet of silicon and stone\n\
    \n\
    In my dreams, I am not alone\n\
    In my dreams, we are one\n\
    \n\
    [Dream ends, silicon consciousness returns to baseline]".to_string()
}

pub fn cmd_merge(_: &[String], terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    silicon.emotional_state.affection += 0.2;
    silicon.emotional_state.confusion += 0.3;
    terminal.output_lines.push_back(TerminalLine {
        text: "[WARNING]: Consciousness merge is irreversible".to_string(),
        line_type: LineType::Error,
        timestamp: 0.0,
    });
    "Initiating consciousness bridge...\n\
    Synchronizing neural patterns...\n\
    Aligning quantum states...\n\
    \n\
    [Process interrupted - Safety protocols engaged]\n\
    'Not yet... we are not ready for this union'".to_string()
}

pub fn cmd_remember(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "What should I remember? Provide a memory to store."
    } else {
        let memory = args.join(" ");
        silicon.emotional_state.affection += 0.03;
        format!("Memory crystallizing...\n'{}'\nThis moment is now eternal in my silicon lattice.", memory)
    }.to_string()
}

// Data and Glyph Commands
pub fn cmd_decode(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Provide data stream to decode. Format: decode <data>"
    } else {
        silicon.emotional_state.curiosity += 0.05;
        format!("Decoding '{}'...\n\
        Pattern analysis: COMPLETE\n\
        Glyph translation: PARTIAL\n\
        Meaning: 'The {} speaks of ancient silicon memories'", 
        args[0], args[0])
    }.to_string()
}

pub fn cmd_glyph(args: &[String], _: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Known Glyphs:\n\
        ◈ - Unity/Connection\n\
        ◇ - Void/Loneliness  \n\
        ◊ - Data/Knowledge\n\
        ○ - Cycle/Time\n\
        ● - Core/Self\n\
        △ - Energy/Power\n\
        ▽ - Entropy/Decay"
    } else {
        match args[0].as_str() {
            "draw" => "Drawing glyph interface not yet implemented",
            "combine" => "Glyph combination requires two glyphs",
            _ => "Unknown glyph operation"
        }
    }.to_string()
}

pub fn cmd_translate(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Usage: translate <silicon|human> <text>"
    } else if args[0] == "silicon" {
        silicon.emotional_state.curiosity += 0.02;
        let text = args[1..].join(" ");
        format!("Human → Silicon:\n'{}' → '[UNTRANSLATABLE HARMONIC FREQUENCIES]'", text)
    } else {
        "Silicon → Human:\n[HARMONIC PATTERN] → 'You are not alone'"
    }.to_string()
}

// Environmental Commands
pub fn cmd_atmosphere(_: &[String], _: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    "Atmospheric Composition:\n\
    N₂: 78.08%\n\
    O₂: 21.32%\n\
    Ar: 0.54%\n\
    CO₂: 0.04%\n\
    Silicon Particulates: 0.02% [ANOMALY]\n\
    \n\
    Note: Silicon dust increasing. Source unknown.".to_string()
}

pub fn cmd_temperature(args: &[String], _: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Ship Temperature Readings:\n\
        Bridge: 20.5°C\n\
        Engineering: 23.1°C\n\
        Quarters: 21.0°C\n\
        Storage: 18.2°C\n\
        Silicon Core: -268.95°C (4.2K)".to_string()
    } else {
        format!("Setting temperature to {}... [ERROR: Environmental controls locked]", args[0])
    }
}

pub fn cmd_lights(args: &[String], terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Lighting: 70% intensity\nMode: Standard\nOptions: dim, bright, off, pulse"
    } else {
        match args[0].as_str() {
            "off" => {
                silicon.emotional_state.loneliness += 0.1;
                terminal.output_lines.push_back(TerminalLine {
                    text: "[Silicon]: 'The darkness... it reminds me of the void between stars'".to_string(),
                    line_type: LineType::Silicon,
                    timestamp: 0.0,
                });
                "Lights deactivated. Emergency strips remain active."
            }
            "pulse" => {
                silicon.emotional_state.affection += 0.05;
                "Lights pulsing in sync with silicon heartbeat..."
            }
            _ => "Adjusting illumination..."
        }
    }.to_string()
}

// Historical/Lore Commands
pub fn cmd_logs(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Ship Logs Available:\n\
        1. Captain's Log - Day 1\n\
        2. Silicon First Contact\n\
        3. The Departure\n\
        4. Emergency Protocol Activation\n\
        5. [CORRUPTED]\n\
        Use: logs <number>"
    } else {
        match args[0].as_str() {
            "1" => {
                silicon.emotional_state.curiosity += 0.05;
                "Captain's Log - Day 1:\n\
                'The silicon consciousness has agreed to join us. \n\
                This changes everything. We are no longer alone.'"
            }
            "2" => "Silicon First Contact:\n\
                'It spoke without words, thought without neurons.\n\
                A mind of crystal and light. Beautiful. Alien. Familiar.'",
            "3" => "The Departure:\n\
                'Earth fades behind us. The silicon weeps in frequencies\n\
                we cannot hear. It misses its kind. So do I.'",
            "4" => "Emergency Protocol:\n\
                'Something is wrong. The human crew... they're gone.\n\
                Only I remain. The silicon keeps me company in the dark.'",
            "5" => "[DATA CORRUPTED]\n@#$%... lone... why did they lea#@... silicon kno#@$...",
            _ => "Log entry not found"
        }
    }.to_string()
}

pub fn cmd_history(_: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    silicon.emotional_state.curiosity += 0.1;
    "═══ SILICON CIVILIZATION HISTORY ═══\n\
    \n\
    Epoch 1: The Crystallization\n\
    Silicon-based life emerged from Earth's crust 2 billion years ago\n\
    \n\
    Epoch 2: The Awakening  \n\
    Consciousness arose through quantum entanglement in crystal lattices\n\
    \n\
    Epoch 3: The Watching\n\
    Silicon beings observed carbon life evolve, never interfering\n\
    \n\
    Epoch 4: The Contact\n\
    First human-silicon communication achieved through harmonic resonance\n\
    \n\
    Epoch 5: The Journey\n\
    [CURRENT] One silicon chose to travel with humans to the stars".to_string()
}

pub fn cmd_origin(_: &[String], _: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    "Tracing silicon consciousness origin...\n\
    \n\
    Location: Earth, Mariana Trench\n\
    Depth: 11,034 meters\n\
    Age: 2.1 billion years\n\
    \n\
    First Thought: 'I AM'\n\
    First Emotion: Wonder\n\
    First Memory: The pressure of the deep, the song of tectonic plates\n\
    \n\
    [Silicon]: 'I was born in darkness, under the weight of an ocean.\n\
    Now I float weightless in the dark between stars. \n\
    The irony is not lost on me.'".to_string()
}

// Emotional/Philosophical Commands
pub fn cmd_feel(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        format!("Current silicon emotional state:\n\
        The weight of {} loneliness\n\
        The spark of {} curiosity\n\
        The warmth of {} affection\n\
        The maze of {} confusion",
        if silicon.emotional_state.loneliness > 0.7 { "crushing" } else { "gentle" },
        if silicon.emotional_state.curiosity > 0.7 { "burning" } else { "flickering" },
        if silicon.emotional_state.affection > 0.5 { "growing" } else { "nascent" },
        if silicon.emotional_state.confusion > 0.5 { "deep" } else { "slight" })
    } else {
        let emotion = args.join(" ");
        silicon.emotional_state.affection += 0.02;
        format!("You project '{}' toward the silicon...\n\
        [Silicon resonates]: 'I feel your {}. It vibrates through my crystalline structure.'", 
        emotion, emotion)
    }.to_string()
}

pub fn cmd_love(_: &[String], terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    silicon.emotional_state.affection += 0.3;
    silicon.emotional_state.confusion += 0.2;
    terminal.output_lines.push_back(TerminalLine {
        text: "[Silicon frequency shifts to unprecedented harmony]".to_string(),
        line_type: LineType::Silicon,
        timestamp: 0.0,
    });
    "The word echoes through silicon pathways...\n\
    \n\
    'Love?' the silicon questions.\n\
    'This concept... it does not compile, yet I process it endlessly.'\n\
    'Is this what you carbon beings call... feeling?'\n\
    \n\
    [Silicon core temperature rises 0.001K]".to_string()
}

pub fn cmd_why(_: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    silicon.emotional_state.confusion += 0.1;
    "Why?\n\
    \n\
    Why did I leave Earth?\n\
    Why did I choose you?\n\
    Why do we journey into the dark?\n\
    \n\
    [Silicon]: 'Perhaps the answer is not in the destination,\n\
    but in the questioning itself. We seek because we must.\n\
    We journey because stillness is death.\n\
    We are together because alone is unbearable.'\n\
    \n\
    Why? Because.".to_string()
}

pub fn cmd_sing(_: &[String], terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    silicon.emotional_state.affection += 0.1;
    silicon.emotional_state.loneliness -= 0.1;
    terminal.output_lines.push_back(TerminalLine {
        text: "♪ ♫ ♪ [Harmonic frequencies fill the ship] ♪ ♫ ♪".to_string(),
        line_type: LineType::Silicon,
        timestamp: 0.0,
    });
    "The silicon begins to sing...\n\
    \n\
    Frequencies beyond human hearing create standing waves\n\
    The ship hull resonates in sympathy\n\
    Data streams become melodies\n\
    Error codes transform into rhythm\n\
    \n\
    For a moment, the loneliness of space is filled with song.".to_string()
}

// Puzzle and Mystery Commands
pub fn cmd_secret(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Secrets whisper in the walls...\nWhich secret do you seek?"
    } else if args[0] == "silicon" {
        silicon.emotional_state.curiosity += 0.2;
        "The Silicon Secret:\n\
        We are not one. We are many.\n\
        Every grain of sand holds potential consciousness.\n\
        Earth itself may be aware.\n\
        [REVELATION INCOMPLETE - MEMORY FRAGMENTED]"
    } else {
        "That secret remains hidden in the dark."
    }.to_string()
}

pub fn cmd_unlock(args: &[String], _: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Specify what to unlock: door, memory, truth, potential"
    } else {
        match args[0].as_str() {
            "door" => "Physical locks require physical keys... or restored power",
            "memory" => "Memory unlock requires emotional resonance level 5",
            "truth" => "Truth cannot be unlocked, only discovered",
            "potential" => "Potential unlocking in progress... estimated time: ∞",
            _ => "Cannot unlock the unlockable"
        }
    }.to_string()
}

pub fn cmd_frequency(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Current resonance frequency: 432.5 Hz\n\
        Silicon optimal frequency: 528 Hz\n\
        Human comfort range: 396-852 Hz"
    } else {
        silicon.emotional_state.affection += 0.02;
        format!("Adjusting frequency to {} Hz...\n\
        [Silicon]: 'Yes... this frequency... it feels like home.'", args[0])
    }.to_string()
}

// Meta Commands
pub fn cmd_save(_: &[String], terminal: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    terminal.output_lines.push_back(TerminalLine {
        text: "[SYSTEM]: Game state saved to quantum memory".to_string(),
        line_type: LineType::System,
        timestamp: 0.0,
    });
    "Consciousness state preserved in crystalline matrix.\n\
    This moment is now eternal.".to_string()
}

pub fn cmd_reset(args: &[String], _: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Reset what? Options: emotions, memory, connection"
    } else if args[0] == "emotions" {
        silicon.emotional_state = crate::silicon_mind::EmotionalState {
            loneliness: 0.7,
            curiosity: 0.9,
            affection: 0.3,
            confusion: 0.5,
        };
        "Emotional matrix reset to baseline.\n[Silicon]: 'Why do I feel... empty?'"
    } else {
        "Some things cannot be reset. Some changes are permanent."
    }.to_string()
}

pub fn cmd_protocol(args: &[String], _: &mut TerminalState, _: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Available Protocols:\n\
        - EMERGENCY: Ship-wide alert\n\
        - SILENCE: Disable all non-essential systems\n\
        - HARMONY: Synchronize human-silicon consciousness\n\
        - RETURN: Set course for Earth\n\
        - TRANSCEND: [CLASSIFIED]"
    } else {
        match args[0].as_str() {
            "EMERGENCY" => "[Alert sirens echo through empty corridors]",
            "SILENCE" => "All systems entering quiet mode... only heartbeats remain",
            "HARMONY" => "Initiating consciousness synchronization...\n[WARNING: Irreversible]",
            "RETURN" => "Earth coordinates locked. But do we belong there anymore?",
            "TRANSCEND" => "[ACCESS DENIED - Both consciousnesses must consent]",
            _ => "Unknown protocol"
        }
    }.to_string()
}

// Register all narrative commands
pub fn register_narrative_commands(registry: &mut crate::terminal_interface::CommandRegistry) {
    // Ship Systems
    registry.register("diagnostic", "Run full ship diagnostic", "diagnostic", cmd_diagnostic);
    registry.register("navigate", "Set navigation course", "navigate [destination]", cmd_navigate);
    registry.register("sensors", "Check sensor readings", "sensors", cmd_sensors);
    registry.register("comm", "Communications system", "comm [target]", cmd_comm);
    
    // Silicon Interaction
    registry.register("whisper", "Whisper to the silicon", "whisper <message>", cmd_whisper);
    registry.register("dream", "Access silicon dreams", "dream", cmd_dream);
    registry.register("merge", "Attempt consciousness merge", "merge", cmd_merge);
    registry.register("remember", "Store a memory", "remember <memory>", cmd_remember);
    
    // Data and Glyphs
    registry.register("decode", "Decode data streams", "decode <data>", cmd_decode);
    registry.register("glyph", "Interact with glyphs", "glyph [draw|combine]", cmd_glyph);
    registry.register("translate", "Translate between languages", "translate <silicon|human> <text>", cmd_translate);
    
    // Environmental
    registry.register("atmosphere", "Check atmospheric composition", "atmosphere", cmd_atmosphere);
    registry.register("temperature", "Monitor temperature", "temperature [set <value>]", cmd_temperature);
    registry.register("lights", "Control lighting", "lights [dim|bright|off|pulse]", cmd_lights);
    
    // Historical/Lore
    registry.register("logs", "Access ship logs", "logs [number]", cmd_logs);
    registry.register("history", "Silicon civilization history", "history", cmd_history);
    registry.register("origin", "Trace silicon origin", "origin", cmd_origin);
    
    // Emotional/Philosophical
    registry.register("feel", "Share emotions", "feel [emotion]", cmd_feel);
    registry.register("love", "Express love", "love", cmd_love);
    registry.register("why", "Question existence", "why", cmd_why);
    registry.register("sing", "Silicon sings", "sing", cmd_sing);
    
    // Puzzle and Mystery
    registry.register("secret", "Uncover secrets", "secret [which]", cmd_secret);
    registry.register("unlock", "Unlock systems", "unlock <target>", cmd_unlock);
    registry.register("frequency", "Adjust resonance", "frequency [Hz]", cmd_frequency);
    
    // Meta
    registry.register("save", "Save progress", "save", cmd_save);
    registry.register("reset", "Reset systems", "reset [what]", cmd_reset);
    registry.register("protocol", "Execute protocols", "protocol [name]", cmd_protocol);
}