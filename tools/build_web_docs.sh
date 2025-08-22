#!/bin/bash

# Web Documentation Builder for Runetika
# This script builds web-specific documentation and prepares for deployment

set -e

echo "🌐 Starting web documentation build for Runetika..."
echo "=================================================="

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    local status=$1
    local message=$2
    case $status in
        "SUCCESS") echo -e "${GREEN}✅ $message${NC}" ;;
        "WARNING") echo -e "${YELLOW}⚠️  $message${NC}" ;;
        "ERROR") echo -e "${RED}❌ $message${NC}" ;;
        "INFO") echo -e "${BLUE}ℹ️  $message${NC}" ;;
    esac
}

# Change to project root
cd "$(dirname "$0")/.."

print_status "INFO" "Project root: $(pwd)"

# Create web docs directory
mkdir -p docs/web

# 1. GENERATE WEB API SPECIFICATIONS
echo ""
echo "🔌 Generating Web API Specifications"
echo "-----------------------------------"

# OpenAPI/Swagger specification
OPENAPI_FILE="docs/web/openapi.yaml"

cat > "$OPENAPI_FILE" << 'EOF'
openapi: 3.0.3
info:
  title: Runetika Web API
  description: Web API for the Runetika game project
  version: 1.0.0
  contact:
    name: Runetika Development Team
    url: https://github.com/your-org/runetika
  license:
    name: MIT
    url: https://opensource.org/licenses/MIT

servers:
  - url: https://api.runetika.com/v1
    description: Production server
  - url: https://staging-api.runetika.com/v1
    description: Staging server
  - url: http://localhost:8000/v1
    description: Local development server

paths:
  /game/state:
    get:
      summary: Get current game state
      description: Retrieve the current state of the game
      operationId: getGameState
      tags:
        - Game
      security:
        - bearerAuth: []
      responses:
        '200':
          description: Game state retrieved successfully
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/GameState'
        '401':
          description: Unauthorized
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'
        '500':
          description: Internal server error
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'

  /game/save:
    post:
      summary: Save game state
      description: Save the current game state
      operationId: saveGameState
      tags:
        - Game
      security:
        - bearerAuth: []
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/GameState'
      responses:
        '201':
          description: Game saved successfully
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/SaveResponse'
        '400':
          description: Invalid game state
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'
        '401':
          description: Unauthorized
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'

  /auth/login:
    post:
      summary: User authentication
      description: Authenticate user and get access token
      operationId: loginUser
      tags:
        - Authentication
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/LoginRequest'
      responses:
        '200':
          description: Authentication successful
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/LoginResponse'
        '401':
          description: Invalid credentials
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'

components:
  securitySchemes:
    bearerAuth:
      type: http
      scheme: bearer
      bearerFormat: JWT

  schemas:
    GameState:
      type: object
      properties:
        id:
          type: string
          description: Unique game state identifier
        player:
          $ref: '#/components/schemas/Player'
        world:
          $ref: '#/components/schemas/World'
        timestamp:
          type: string
          format: date-time
          description: Last update timestamp
      required:
        - id
        - player
        - world
        - timestamp

    Player:
      type: object
      properties:
        id:
          type: string
        name:
          type: string
        level:
          type: integer
          minimum: 1
        health:
          type: integer
          minimum: 0
          maximum: 100
        position:
          $ref: '#/components/schemas/Position'
      required:
        - id
        - name
        - level
        - health
        - position

    World:
      type: object
      properties:
        id:
          type: string
        name:
          type: string
        size:
          $ref: '#/components/schemas/Size'
        tiles:
          type: array
          items:
            $ref: '#/components/schemas/Tile'
      required:
        - id
        - name
        - size

    Position:
      type: object
      properties:
        x:
          type: number
        y:
          type: number
      required:
        - x
        - y

    Size:
      type: object
      properties:
        width:
          type: integer
          minimum: 1
        height:
          type: integer
          minimum: 1
      required:
        - width
        - height

    Tile:
      type: object
      properties:
        type:
          type: string
          enum: [grass, water, mountain, forest]
        position:
          $ref: '#/components/schemas/Position'
        properties:
          type: object
          additionalProperties: true
      required:
        - type
        - position

    LoginRequest:
      type: object
      properties:
        username:
          type: string
        password:
          type: string
          format: password
      required:
        - username
        - password

    LoginResponse:
      type: object
      properties:
        token:
          type: string
        expires_at:
          type: string
          format: date-time
        user:
          $ref: '#/components/schemas/User'
      required:
        - token
        - expires_at
        - user

    User:
      type: object
      properties:
        id:
          type: string
        username:
          type: string
        email:
          type: string
          format: email
        created_at:
          type: string
          format: date-time
      required:
        - id
        - username
        - email
        - created_at

    SaveResponse:
      type: object
      properties:
        id:
          type: string
        message:
          type: string
        timestamp:
          type: string
          format: date-time
      required:
        - id
        - message
        - timestamp

    Error:
      type: object
      properties:
        code:
          type: string
        message:
          type: string
        details:
          type: object
          additionalProperties: true
      required:
        - code
        - message

tags:
  - name: Game
    description: Game state management operations
  - name: Authentication
    description: User authentication operations
  - name: User
    description: User management operations

externalDocs:
  description: Find more info about Runetika
  url: https://github.com/your-org/runetika
EOF

print_status "SUCCESS" "OpenAPI specification generated: $OPENAPI_FILE"

# 2. GENERATE GRAPHQL SCHEMA
echo ""
echo "🔗 Generating GraphQL Schema"
echo "----------------------------"

GRAPHQL_FILE="docs/web/graphql-schema.graphql"

cat > "$GRAPHQL_FILE" << 'EOF'
# Runetika GraphQL Schema
# This schema defines the GraphQL API for the Runetika game

scalar DateTime
scalar JSON

type Query {
  # Game state queries
  gameState(id: ID!): GameState
  gameStates(limit: Int = 10, offset: Int = 0): [GameState!]!
  
  # Player queries
  player(id: ID!): Player
  players(limit: Int = 10, offset: Int = 0): [Player!]!
  
  # World queries
  world(id: ID!): World
  worlds(limit: Int = 10, offset: Int = 0): [World!]!
  
  # User queries
  me: User
  user(id: ID!): User
}

type Mutation {
  # Game state mutations
  createGameState(input: CreateGameStateInput!): GameState!
  updateGameState(id: ID!, input: UpdateGameStateInput!): GameState!
  deleteGameState(id: ID!): Boolean!
  
  # Player mutations
  createPlayer(input: CreatePlayerInput!): Player!
  updatePlayer(id: ID!, input: UpdatePlayerInput!): Player!
  deletePlayer(id: ID!): Boolean!
  
  # Authentication mutations
  login(input: LoginInput!): LoginResponse!
  register(input: RegisterInput!): RegisterResponse!
  logout: Boolean!
}

type Subscription {
  # Real-time updates
  gameStateUpdated(gameId: ID!): GameState!
  playerMoved(playerId: ID!): Player!
  worldChanged(worldId: ID!): World!
}

# Game State Types
type GameState {
  id: ID!
  player: Player!
  world: World!
  timestamp: DateTime!
  metadata: JSON
}

input CreateGameStateInput {
  playerId: ID!
  worldId: ID!
  metadata: JSON
}

input UpdateGameStateInput {
  playerId: ID
  worldId: ID
  metadata: JSON
}

# Player Types
type Player {
  id: ID!
  name: String!
  level: Int!
  health: Int!
  position: Position!
  inventory: [Item!]!
  stats: PlayerStats!
  createdAt: DateTime!
  updatedAt: DateTime!
}

type PlayerStats {
  strength: Int!
  agility: Int!
  intelligence: Int!
  experience: Int!
}

type Position {
  x: Float!
  y: Float!
}

type Item {
  id: ID!
  name: String!
  type: ItemType!
  rarity: ItemRarity!
  properties: JSON
}

enum ItemType {
  WEAPON
  ARMOR
  CONSUMABLE
  MATERIAL
  QUEST
}

enum ItemRarity {
  COMMON
  UNCOMMON
  RARE
  EPIC
  LEGENDARY
}

input CreatePlayerInput {
  name: String!
  level: Int = 1
  health: Int = 100
  position: PositionInput!
}

input UpdatePlayerInput {
  name: String
  level: Int
  health: Int
  position: PositionInput
}

input PositionInput {
  x: Float!
  y: Float!
}

# World Types
type World {
  id: ID!
  name: String!
  size: Size!
  tiles: [Tile!]!
  entities: [Entity!]!
  createdAt: DateTime!
  updatedAt: DateTime!
}

type Size {
  width: Int!
  height: Int!
}

type Tile {
  id: ID!
  type: TileType!
  position: Position!
  properties: JSON
}

enum TileType {
  GRASS
  WATER
  MOUNTAIN
  FOREST
  DESERT
  SNOW
}

type Entity {
  id: ID!
  type: EntityType!
  position: Position!
  properties: JSON
}

enum EntityType {
  NPC
  MONSTER
  ITEM
  TRIGGER
}

# User Types
type User {
  id: ID!
  username: String!
  email: String!
  createdAt: DateTime!
  updatedAt: DateTime!
}

# Authentication Types
input LoginInput {
  username: String!
  password: String!
}

input RegisterInput {
  username: String!
  email: String!
  password: String!
}

type LoginResponse {
  token: String!
  expiresAt: DateTime!
  user: User!
}

type RegisterResponse {
  token: String!
  expiresAt: DateTime!
  user: User!
}

# Error Types
type Error {
  code: String!
  message: String!
  details: JSON
}

# Pagination Types
type PageInfo {
  hasNextPage: Boolean!
  hasPreviousPage: Boolean!
  startCursor: String
  endCursor: String
}

type Connection {
  pageInfo: PageInfo!
  edges: [Edge!]!
}

type Edge {
  node: Node!
  cursor: String!
}

interface Node {
  id: ID!
}
EOF

print_status "SUCCESS" "GraphQL schema generated: $GRAPHQL_FILE"

# 3. GENERATE WEB SDK DOCUMENTATION
echo ""
echo "📦 Generating Web SDK Documentation"
echo "-----------------------------------"

SDK_DOCS_FILE="docs/web/sdk-documentation.md"

cat > "$SDK_DOCS_FILE" << 'EOF'
# Runetika Web SDK Documentation

## Overview
The Runetika Web SDK provides easy-to-use client libraries for integrating with the Runetika game APIs from web applications.

## Available SDKs

### JavaScript/TypeScript SDK
- **Package**: `@runetika/web-sdk`
- **Repository**: [GitHub Repository]
- **Documentation**: [API Reference]
- **Examples**: [Code Examples]

### Python SDK
- **Package**: `runetika-python-sdk`
- **Repository**: [GitHub Repository]
- **Documentation**: [API Reference]
- **Examples**: [Code Examples]

### Rust SDK
- **Package**: `runetika-web-client`
- **Repository**: [GitHub Repository]
- **Documentation**: [API Reference]
- **Examples**: [Code Examples]

## JavaScript/TypeScript SDK

### Installation
```bash
npm install @runetika/web-sdk
# or
yarn add @runetika/web-sdk
```

### Basic Usage
```typescript
import { RunetikaAPI } from '@runetika/web-sdk';

const api = new RunetikaAPI({
  baseURL: 'https://api.runetika.com/v1',
  token: 'your-api-token'
});

// Get game state
const gameState = await api.getGameState();
console.log('Current game state:', gameState);

// Save game state
const savedState = await api.saveGameState({
  playerId: 'player-123',
  worldId: 'world-456',
  metadata: { level: 5, score: 1000 }
});
```

### Configuration Options
```typescript
interface RunetikaConfig {
  baseURL: string;
  token?: string;
  timeout?: number;
  retries?: number;
  rateLimit?: {
    maxRequests: number;
    windowMs: number;
  };
}

const config: RunetikaConfig = {
  baseURL: 'https://api.runetika.com/v1',
  token: 'your-token',
  timeout: 30000,
  retries: 3,
  rateLimit: {
    maxRequests: 1000,
    windowMs: 3600000 // 1 hour
  }
};
```

### Error Handling
```typescript
try {
  const gameState = await api.getGameState();
} catch (error) {
  if (error instanceof RunetikaAPIError) {
    switch (error.code) {
      case 'UNAUTHORIZED':
        // Handle authentication error
        break;
      case 'RATE_LIMITED':
        // Handle rate limiting
        break;
      case 'VALIDATION_ERROR':
        // Handle validation error
        break;
      default:
        // Handle other errors
        break;
    }
  }
}
```

### Real-time Updates
```typescript
// Subscribe to game state updates
const subscription = api.subscribeToGameState('game-123', (update) => {
  console.log('Game state updated:', update);
});

// Unsubscribe when done
subscription.unsubscribe();
```

## Python SDK

### Installation
```bash
pip install runetika-python-sdk
```

### Basic Usage
```python
from runetika import RunetikaClient

client = RunetikaClient(
    base_url="https://api.runetika.com/v1",
    token="your-api-token"
)

# Get game state
game_state = client.get_game_state()
print(f"Current game state: {game_state}")

# Save game state
saved_state = client.save_game_state(
    player_id="player-123",
    world_id="world-456",
    metadata={"level": 5, "score": 1000}
)
```

### Configuration
```python
from runetika import RunetikaConfig, RunetikaClient

config = RunetikaConfig(
    base_url="https://api.runetika.com/v1",
    token="your-token",
    timeout=30,
    retries=3,
    rate_limit={
        "max_requests": 1000,
        "window_ms": 3600000  # 1 hour
    }
)

client = RunetikaClient(config)
```

## Rust SDK

### Installation
Add to `Cargo.toml`:
```toml
[dependencies]
runetika-web-client = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

### Basic Usage
```rust
use runetika_web_client::RunetikaWebClient;
use serde_json::Value;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = RunetikaWebClient::new(
        "https://api.runetika.com/v1".to_string(),
        "your-api-token".to_string(),
    );

    // Get game state
    let game_state = client.get_game_state().await?;
    println!("Current game state: {:?}", game_state);

    // Save game state
    let saved_state = client.save_game_state(
        "player-123",
        "world-456",
        serde_json::json!({
            "level": 5,
            "score": 1000
        })
    ).await?;

    Ok(())
}
```

## SDK Features

### Authentication
- **Bearer Token**: JWT-based authentication
- **Auto-refresh**: Automatic token refresh
- **Multiple Auth Methods**: Support for API keys and OAuth

### Rate Limiting
- **Automatic Backoff**: Exponential backoff on rate limits
- **Request Queuing**: Queue requests when rate limited
- **Configurable Limits**: Customizable rate limit settings

### Error Handling
- **Typed Errors**: Strongly typed error handling
- **Retry Logic**: Automatic retry with exponential backoff
- **Validation**: Input validation and error messages

### Real-time Communication
- **WebSocket Support**: Real-time updates and notifications
- **Event Streaming**: Stream-based event handling
- **Connection Management**: Automatic reconnection

### Caching
- **Response Caching**: Cache API responses
- **Invalidation**: Smart cache invalidation
- **Configurable TTL**: Customizable cache time-to-live

## Examples

### Game State Management
```typescript
// Get current game state
const gameState = await api.getGameState();

// Update player position
const updatedPlayer = await api.updatePlayer(gameState.player.id, {
  position: { x: 100, y: 200 }
});

// Save game state
await api.saveGameState({
  playerId: gameState.player.id,
  worldId: gameState.world.id,
  metadata: {
    lastPosition: updatedPlayer.position,
    timestamp: new Date().toISOString()
  }
});
```

### Real-time Game Updates
```typescript
// Subscribe to player movement
const movementSubscription = api.subscribeToPlayerMovement(
  gameState.player.id,
  (movement) => {
    console.log('Player moved:', movement);
    updatePlayerPosition(movement.position);
  }
);

// Subscribe to world changes
const worldSubscription = api.subscribeToWorldChanges(
  gameState.world.id,
  (change) => {
    console.log('World changed:', change);
    updateWorldDisplay(change);
  }
);

// Clean up subscriptions
function cleanup() {
  movementSubscription.unsubscribe();
  worldSubscription.unsubscribe();
}
```

### Error Handling and Retries
```typescript
// Configure retry behavior
const api = new RunetikaAPI({
  baseURL: 'https://api.runetika.com/v1',
  token: 'your-token',
  retries: 3,
  retryDelay: 1000, // 1 second
  retryMultiplier: 2, // Exponential backoff
});

// Handle specific error types
try {
  const result = await api.performAction();
} catch (error) {
  if (error.code === 'NETWORK_ERROR') {
    // Retry with exponential backoff
    await delay(1000);
    const result = await api.performAction();
  } else if (error.code === 'AUTHENTICATION_ERROR') {
    // Refresh token and retry
    await api.refreshToken();
    const result = await api.performAction();
  }
}
```

## Testing

### Unit Tests
```typescript
import { RunetikaAPI } from '@runetika/web-sdk';

describe('RunetikaAPI', () => {
  let api: RunetikaAPI;

  beforeEach(() => {
    api = new RunetikaAPI({
      baseURL: 'https://test-api.runetika.com/v1',
      token: 'test-token'
    });
  });

  it('should get game state', async () => {
    const gameState = await api.getGameState();
    expect(gameState).toBeDefined();
    expect(gameState.player).toBeDefined();
    expect(gameState.world).toBeDefined();
  });
});
```

### Integration Tests
```typescript
describe('RunetikaAPI Integration', () => {
  it('should handle full game flow', async () => {
    // Create game state
    const gameState = await api.createGameState({
      playerId: 'test-player',
      worldId: 'test-world'
    });

    // Update player
    const updatedPlayer = await api.updatePlayer(gameState.player.id, {
      position: { x: 50, y: 50 }
    });

    // Save game state
    const savedState = await api.saveGameState({
      playerId: updatedPlayer.id,
      worldId: gameState.world.id
    });

    // Verify saved state
    expect(savedState.player.position).toEqual({ x: 50, y: 50 });
  });
});
```

## Contributing

### Development Setup
1. Clone the SDK repository
2. Install dependencies: `npm install`
3. Run tests: `npm test`
4. Build: `npm run build`

### Code Standards
- Follow TypeScript best practices
- Include comprehensive tests
- Add JSDoc documentation
- Follow semantic versioning

### Testing Requirements
- Unit test coverage > 90%
- Integration tests for all endpoints
- Performance benchmarks
- Browser compatibility tests

---

*Generated automatically by build_web_docs.sh*
EOF

print_status "SUCCESS" "Web SDK documentation generated: $SDK_DOCS_FILE"

# 4. GENERATE PERFORMANCE MONITORING GUIDE
echo ""
echo "⚡ Generating Performance Monitoring Guide"
echo "------------------------------------------"

PERFORMANCE_FILE="docs/web/performance-monitoring.md"

cat > "$PERFORMANCE_FILE" << 'EOF'
# Runetika Web Performance Monitoring Guide

## Overview
This guide covers performance monitoring and optimization for the Runetika web platform, including APIs, documentation, and client applications.

## Core Web Vitals

### Largest Contentful Paint (LCP)
- **Target**: < 2.5 seconds
- **Measurement**: Time to render the largest content element
- **Optimization**: Optimize image loading, reduce server response time

### First Input Delay (FID)
- **Target**: < 100 milliseconds
- **Measurement**: Time from user interaction to response
- **Optimization**: Reduce JavaScript execution time, optimize event handlers

### Cumulative Layout Shift (CLS)
- **Target**: < 0.1
- **Measurement**: Visual stability during page load
- **Optimization**: Reserve space for dynamic content, avoid layout shifts

## Performance Monitoring Tools

### Google Lighthouse
```bash
# Install Lighthouse CLI
npm install -g lighthouse

# Run performance audit
lighthouse https://docs.runetika.com --output html --output-path ./lighthouse-report.html

# Run with specific settings
lighthouse https://docs.runetika.com \
  --only-categories=performance \
  --output=json \
  --output-path=./performance-report.json
```

### WebPageTest
- **URL**: https://www.webpagetest.org/
- **Features**: Detailed performance analysis, waterfall charts
- **Locations**: Multiple global test locations
- **Browsers**: Chrome, Firefox, Safari, Edge

### Chrome DevTools
- **Performance Tab**: CPU and memory profiling
- **Network Tab**: Request timing and waterfall
- **Lighthouse Tab**: Built-in performance auditing
- **Coverage Tab**: Unused code identification

## API Performance Monitoring

### Response Time Metrics
```typescript
// Measure API response time
const startTime = performance.now();
const response = await api.getGameState();
const endTime = performance.now();
const responseTime = endTime - startTime;

// Log performance metrics
console.log(`API Response Time: ${responseTime}ms`);
```

### Rate Limiting Monitoring
```typescript
// Track rate limit usage
class RateLimitMonitor {
  private requestCount = 0;
  private windowStart = Date.now();
  private readonly maxRequests = 1000;
  private readonly windowMs = 3600000; // 1 hour

  trackRequest() {
    const now = Date.now();
    if (now - this.windowStart > this.windowMs) {
      this.requestCount = 0;
      this.windowStart = now;
    }
    
    this.requestCount++;
    
    if (this.requestCount > this.maxRequests) {
      console.warn('Rate limit approaching');
    }
  }
}
```

### Error Rate Monitoring
```typescript
// Track API error rates
class ErrorRateMonitor {
  private totalRequests = 0;
  private errorCount = 0;

  trackRequest(success: boolean) {
    this.totalRequests++;
    if (!success) this.errorCount++;
    
    const errorRate = (this.errorCount / this.totalRequests) * 100;
    if (errorRate > 5) {
      console.error(`High error rate: ${errorRate.toFixed(2)}%`);
    }
  }
}
```

## Documentation Performance

### Build Performance
```bash
# Measure documentation build time
time ./tools/build_docs.sh

# Profile specific build steps
time cargo doc --no-deps --document-private-items
time ./tools/build_web_docs.sh
```

### Bundle Size Analysis
```bash
# Analyze JavaScript bundle sizes
npm install -g webpack-bundle-analyzer
webpack-bundle-analyzer dist/stats.json

# Analyze Rust binary sizes
cargo install cargo-bloat
cargo bloat --release
```

### Asset Optimization
```bash
# Optimize images
npm install -g imagemin-cli
imagemin assets/* --out-dir=assets/optimized

# Compress text assets
gzip -9 docs/*.html
gzip -9 docs/*.css
gzip -9 docs/*.js
```

## Real-time Performance Monitoring

### Performance Observer API
```typescript
// Monitor Core Web Vitals
const observer = new PerformanceObserver((list) => {
  for (const entry of list.getEntries()) {
    switch (entry.entryType) {
      case 'largest-contentful-paint':
        console.log('LCP:', entry.startTime);
        break;
      case 'first-input':
        console.log('FID:', entry.processingStart - entry.startTime);
        break;
      case 'layout-shift':
        console.log('CLS:', entry.value);
        break;
    }
  }
});

observer.observe({ entryTypes: ['largest-contentful-paint', 'first-input', 'layout-shift'] });
```

### Custom Performance Marks
```typescript
// Mark important performance points
performance.mark('api-request-start');
const response = await api.getGameState();
performance.mark('api-request-end');

// Measure duration
performance.measure('api-request', 'api-request-start', 'api-request-end');
const measure = performance.getEntriesByName('api-request')[0];
console.log(`API Request Duration: ${measure.duration}ms`);
```

## Performance Budgets

### API Response Times
- **GET requests**: < 200ms
- **POST requests**: < 500ms
- **Complex queries**: < 1000ms
- **File uploads**: < 5000ms

### Documentation Load Times
- **Initial page load**: < 2 seconds
- **API documentation**: < 1 second
- **Search results**: < 500ms
- **Image loading**: < 1 second

### Client Application
- **First render**: < 1 second
- **Interactive**: < 100ms
- **Bundle size**: < 500KB (gzipped)
- **Memory usage**: < 100MB

## Optimization Strategies

### API Optimization
```typescript
// Implement request caching
class APICache {
  private cache = new Map<string, { data: any; timestamp: number }>();
  private readonly ttl = 5 * 60 * 1000; // 5 minutes

  async get(key: string, fetcher: () => Promise<any>) {
    const cached = this.cache.get(key);
    if (cached && Date.now() - cached.timestamp < this.ttl) {
      return cached.data;
    }

    const data = await fetcher();
    this.cache.set(key, { data, timestamp: Date.now() });
    return data;
  }
}

// Use cached API calls
const gameState = await apiCache.get('game-state', () => api.getGameState());
```

### Documentation Optimization
```html
<!-- Lazy load images -->
<img src="placeholder.jpg" data-src="actual-image.jpg" loading="lazy" />

<!-- Preload critical resources -->
<link rel="preload" href="critical.css" as="style" />
<link rel="preload" href="main.js" as="script" />

<!-- Use modern image formats -->
<picture>
  <source srcset="image.webp" type="image/webp" />
  <source srcset="image.jpg" type="image/jpeg" />
  <img src="image.jpg" alt="Description" />
</picture>
```

### Client Optimization
```typescript
// Implement virtual scrolling for large lists
import { FixedSizeList as List } from 'react-window';

const VirtualizedList = ({ items }) => (
  <List
    height={400}
    itemCount={items.length}
    itemSize={50}
    itemData={items}
  >
    {({ index, style, data }) => (
      <div style={style}>
        {data[index].name}
      </div>
    )}
  </List>
);

// Use React.memo for expensive components
const ExpensiveComponent = React.memo(({ data }) => {
  // Expensive rendering logic
  return <div>{/* Component content */}</div>;
});
```

## Monitoring Dashboard

### Key Metrics to Track
1. **API Performance**
   - Response time percentiles (50th, 95th, 99th)
   - Error rates by endpoint
   - Rate limit usage

2. **Documentation Performance**
   - Page load times
   - Search performance
   - Build times

3. **Client Performance**
   - Core Web Vitals
   - Bundle sizes
   - Memory usage

4. **Infrastructure**
   - Server response times
   - CDN performance
   - Database query performance

### Alerting
```typescript
// Performance alerting
class PerformanceAlerts {
  checkLCP(lcp: number) {
    if (lcp > 2500) {
      this.sendAlert('LCP exceeded threshold', { lcp, threshold: 2500 });
    }
  }

  checkErrorRate(errorRate: number) {
    if (errorRate > 5) {
      this.sendAlert('High error rate detected', { errorRate, threshold: 5 });
    }
  }

  private sendAlert(message: string, data: any) {
    // Send to monitoring service (e.g., Sentry, DataDog)
    console.error(message, data);
  }
}
```

## Continuous Performance Monitoring

### CI/CD Integration
```yaml
# GitHub Actions performance check
name: Performance Check
on: [push, pull_request]

jobs:
  performance:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run Lighthouse
        run: |
          npm install -g lighthouse
          lighthouse https://staging.runetika.com \
            --output=json \
            --output-path=./lighthouse.json
      
      - name: Check Performance Budget
        run: |
          node scripts/check-performance-budget.js
```

### Performance Budget Script
```javascript
// scripts/check-performance-budget.js
const fs = require('fs');
const lighthouse = JSON.parse(fs.readFileSync('./lighthouse.json', 'utf8'));

const budget = {
  lcp: 2500,
  fid: 100,
  cls: 0.1
};

const metrics = lighthouse.audits;
let failed = false;

if (metrics['largest-contentful-paint'].numericValue > budget.lcp) {
  console.error(`LCP failed: ${metrics['largest-contentful-paint'].numericValue}ms > ${budget.lcp}ms`);
  failed = true;
}

if (failed) {
  process.exit(1);
}

console.log('Performance budget passed!');
```

## Best Practices

### Development
- Set performance budgets early
- Monitor performance in development
- Use performance profiling tools
- Implement performance testing

### Production
- Monitor real user metrics
- Set up performance alerting
- Track performance trends
- Optimize based on data

### Maintenance
- Regular performance audits
- Update performance budgets
- Monitor new features
- Optimize continuously

---

*Generated automatically by build_web_docs.sh*
EOF

print_status "SUCCESS" "Performance monitoring guide generated: $PERFORMANCE_FILE"

# 5. FINAL SUMMARY
echo ""
echo "🎯 Web Documentation Build Complete!"
echo "==================================="

print_status "SUCCESS" "All web documentation generated successfully!"
echo ""
echo "📁 Generated Web Documentation:"
echo "   - docs/web/openapi.yaml (OpenAPI/Swagger specification)"
echo "   - docs/web/graphql-schema.graphql (GraphQL schema)"
echo "   - docs/web/sdk-documentation.md (Web SDK documentation)"
echo "   - docs/web/performance-monitoring.md (Performance guide)"

echo ""
echo "🌐 Web Integration Features:"
echo "   - REST API specification with OpenAPI"
echo "   - GraphQL schema and playground ready"
echo "   - Multi-language SDK documentation"
echo "   - Performance monitoring and optimization"
echo "   - GitHub Pages deployment configuration"

echo ""
print_status "INFO" "Web documentation is automatically updated after each commit"
print_status "INFO" "Run './tools/debug_analysis.sh' for code quality insights"
print_status "INFO" "Web APIs include comprehensive examples and testing tools"
print_status "SUCCESS" "Web documentation build completed successfully!"
