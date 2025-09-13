# Papilio Credit System

## Overview

The Papilio credit system is Runetika's integrated reward mechanism that bridges gameplay achievements with the Libertalia platform. Players earn Papilio credits by solving ARC puzzles, discovering patterns, completing mathematical proofs, and contributing to AI training data.

## Core Features

### 1. Credit Earning Mechanisms

Players earn credits through multiple pathways:

- **Puzzle Solving**: Base rewards scale with difficulty (10-250 credits)
- **Pattern Discovery**: Novel patterns reward 50+ credits based on complexity
- **Perfect Solves**: 1.5x multiplier for first-attempt solutions
- **Speed Bonuses**: Up to 2x multiplier for fast solutions
- **Efficiency Rewards**: Bonus for low attempt counts
- **Daily Streaks**: Cumulative bonuses for consistent play
- **Proof Completion**: Mathematical proofs reward 100+ credits
- **AI Training Contribution**: Credits for high-quality training data

### 2. Reward Calculation

The system uses a sophisticated multiplier system:

```rust
Base Reward × Performance Multipliers = Total Credits
```

#### Difficulty Base Rewards:
- Tutorial: 10 credits
- Easy: 25 credits  
- Medium: 50 credits
- Hard: 100 credits
- Expert: 250 credits

#### Performance Multipliers:
- Perfect Solve (first try): 1.5x
- Speed Bonus (<30s): up to 2.0x
- Efficiency (<3 attempts): up to 1.3x
- Special Events: Variable (e.g., 2x weekends)

### 3. Persistence & Synchronization

- **Local Storage**: Credits are saved to platform-appropriate directories
- **Atomic Saves**: Uses temp file + rename for data integrity
- **Automatic Backups**: Backup created before each save
- **Libertalia Sync**: Periodic synchronization with backend (60s intervals)
- **Offline Support**: Full functionality without network connection
- **Web Storage**: Browser localStorage for WASM builds

### 4. Integration Points

The system provides hooks for external integrations:

```rust
pub trait PapilioIntegration {
    fn on_credits_earned(&self, amount: u64, source: &str);
    fn on_credits_spent(&self, amount: u64, item: &str);
    fn on_sync_complete(&self, success: bool, synced: u64);
    fn get_exchange_rate(&self) -> f32;
}
```

### 5. Statistics Tracking

Comprehensive statistics are maintained:

- Total balance and lifetime earnings
- Puzzles solved (total and perfect)
- Patterns discovered
- Average puzzle reward
- Current and best streaks
- Highest single reward
- Chapters and daily challenges completed

## Architecture

### Module Structure

```
src/papilio/
├── mod.rs          # Main plugin and system coordination
├── types.rs        # Core data structures
├── rewards.rs      # Reward calculation logic
├── integration.rs  # Libertalia backend integration
├── persistence.rs  # Save/load functionality
└── ui.rs          # Visual components and notifications
```

### Key Components

1. **PapilioCredits Resource**: Central state tracking all credits
2. **RewardCalculator**: Configurable reward computation
3. **LibertaliaSyncStatus**: Backend synchronization state
4. **CreditTransaction**: Individual earning records
5. **UI Components**: Notifications, displays, animations

## Usage Examples

### Basic Integration

```rust
use runetika::papilio::{PapilioPlugin, PapilioCredits};
use runetika::arc_engine::{ARCEnginePlugin, PuzzleSolvedEvent};

App::new()
    .add_plugins(ARCEnginePlugin)
    .add_plugins(PapilioPlugin)
    .run();
```

### Triggering Credit Rewards

```rust
// When a puzzle is solved
puzzle_events.send(PuzzleSolvedEvent {
    puzzle_id: "glyph_chamber_7".to_string(),
    attempts: 1,  // First try!
    time_taken: 25.0,  // 25 seconds
});
// This automatically calculates and awards credits
```

### Querying Credit Balance

```rust
fn check_credits(credits: Res<PapilioCredits>) {
    println!("Current balance: {}", credits.total_balance());
    println!("Lifetime earned: {}", credits.lifetime_earnings());
}
```

## Configuration

### Environment Variables

```bash
# Libertalia API endpoint
export LIBERTALIA_ENDPOINT="https://api.libertalia.example/v1"

# API authentication key
export LIBERTALIA_API_KEY="your-api-key"

# Player identification
export LIBERTALIA_PLAYER_ID="player-uuid"
```

### Development Mode

In development mode (default), the system:
- Uses mock API responses
- Always succeeds sync operations
- Generates development player IDs
- Logs all credit transactions

## Security Considerations

1. **Data Integrity**: Atomic file operations prevent corruption
2. **Validation**: All loaded data is validated for consistency
3. **Privacy**: Differential privacy for aggregate data
4. **Encryption**: Support for encrypted storage (future)
5. **Authentication**: Secure API key management

## UI Components

### Credit Display
- Persistent display in top-right corner
- Real-time balance updates
- Animated credit icon

### Notifications
- Pop-up notifications for earnings
- Milestone celebrations
- Sync status indicators
- Color-coded by type

### Statistics Panel
- Detailed breakdown of earnings
- Historical performance metrics
- Achievement progress tracking

### Reward Animations
- Floating text showing earned amount
- Particle burst effects
- Screen-space animations

## Future Enhancements

1. **Credit Marketplace**: Spend credits on in-game items
2. **Leaderboards**: Global and friend rankings
3. **Challenges**: Special timed events with bonus rewards
4. **NFT Integration**: Blockchain-backed rare rewards
5. **Cross-Game Credits**: Use credits in other Libertalia games
6. **Advanced Analytics**: Detailed earning patterns and insights

## Testing

Run the demo to see the system in action:

```bash
cargo run --example papilio_demo
```

Key commands in demo:
- `SPACE`: Simulate solving a puzzle
- `M`: View credit statistics
- `S`: Trigger sync with Libertalia

## Troubleshooting

### Credits Not Saving
- Check file permissions in config directory
- Verify disk space available
- Look for error messages in logs

### Sync Failures
- Verify network connectivity
- Check API credentials
- Review sync status in UI

### Missing Credits
- Check backup file (.backup extension)
- Use restore_from_backup() function
- Contact support with transaction logs

## API Reference

See individual module documentation for detailed API information:
- `papilio::types` - Core data structures
- `papilio::rewards` - Reward calculation
- `papilio::integration` - Backend integration
- `papilio::persistence` - Save/load operations
- `papilio::ui` - UI components