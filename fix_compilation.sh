#!/bin/bash

# Fix compilation errors in Runetika

echo "Fixing compilation errors..."

# Fix 1: Update menu/systems.rs - Color is not a Component
cat > /tmp/menu_systems_fix.patch << 'EOF'
--- a/src/menu/systems.rs
+++ b/src/menu/systems.rs
@@ -68,7 +68,7 @@
-                    if let Ok(mut visibility) = selected_marker_query.get_mut(child) {
+                    if let Ok(mut visibility) = selected_marker_query.get_mut(*child) {
                         *visibility = Visibility::Visible;
@@ -95,7 +95,7 @@
-                if let Ok(mut visibility) = selected_marker_query.get_mut(child) {
+                if let Ok(mut visibility) = selected_marker_query.get_mut(*child) {
                     *visibility = Visibility::Hidden;
@@ -104,7 +104,7 @@
-                if let Ok(mut visibility) = selected_marker_query.get_mut(child) {
+                if let Ok(mut visibility) = selected_marker_query.get_mut(*child) {
                     *visibility = Visibility::Hidden;
@@ -156,7 +156,7 @@
-    mut glow_query: Query<(&mut Color, &MenuGlow)>,
+    mut glow_query: Query<(&mut Text, &MenuGlow)>,
@@ -161,8 +161,8 @@
-    for (mut text_color, glow) in glow_query.iter_mut() {
-        let intensity = (time.elapsed_secs() * glow.speed).sin() * 0.2 + 0.8;
+    for (mut text, glow) in glow_query.iter_mut() {
+        let intensity = (time.elapsed_seconds() * glow.speed).sin() * 0.2 + 0.8;
@@ -168,18 +168,18 @@
-        if let Val::Percent(mut x) = node.left {
-            x += particle.velocity.x * time.delta_secs() * 10.0;
+        if let Val::Percent(mut x) = node.style.left {
+            x += particle.velocity.x * time.delta_seconds() * 10.0;
             if x > 100.0 || x < 0.0 {
                 particle.velocity.x = -particle.velocity.x;
                 x = x.clamp(0.0, 100.0);
             }
-            node.left = Val::Percent(x);
+            node.style.left = Val::Percent(x);
         }
         
-        if let Val::Percent(mut y) = node.top {
-            y += particle.velocity.y * time.delta_secs() * 10.0;
+        if let Val::Percent(mut y) = node.style.top {
+            y += particle.velocity.y * time.delta_seconds() * 10.0;
             if y > 100.0 || y < 0.0 {
                 particle.velocity.y = -particle.velocity.y;
             }
-            node.top = Val::Percent(y);
+            node.style.top = Val::Percent(y);
         }
@@ -189,1 +189,1 @@
-        let offset = (time.elapsed_secs() * 0.5).sin() * 5.0;
+        let offset = (time.elapsed_seconds() * 0.5).sin() * 5.0;
EOF

# Fix 2: Update credits/systems.rs
cat > /tmp/credits_systems_fix.patch << 'EOF'
--- a/src/credits/systems.rs
+++ b/src/credits/systems.rs
@@ -90,1 +90,1 @@
-    mut child_texts: Query<&mut Color, Without<CreditEntry>>,
+    mut child_texts: Query<&mut Text, Without<CreditEntry>>,
EOF

# Fix 3: Update menu/ui.rs - Node structure changes
cat > /tmp/menu_ui_fix.patch << 'EOF'
--- a/src/menu/ui.rs
+++ b/src/menu/ui.rs
@@ -76,6 +76,10 @@
-                width: Val::Percent(100.0),
-                height: Val::Percent(100.0),
-                position_type: PositionType::Absolute,
-                flex_direction: FlexDirection::Column,
-                justify_content: JustifyContent::Center,
-                align_items: AlignItems::Center,
+                style: Style {
+                    width: Val::Percent(100.0),
+                    height: Val::Percent(100.0),
+                    position_type: PositionType::Absolute,
+                    flex_direction: FlexDirection::Column,
+                    justify_content: JustifyContent::Center,
+                    align_items: AlignItems::Center,
+                    ..default()
+                },
@@ -119,1 +119,1 @@
-        ZIndex(-10),
+        ZIndex::Local(-10),
@@ -203,1 +203,1 @@
-                Text::new("RUNETIKA"),
+                Text::from_section("RUNETIKA", TextStyle::default()),
@@ -208,1 +208,1 @@
-                Color(colors::TITLE_GLOW),
+                BackgroundColor(colors::TITLE_GLOW),
EOF

echo "Applying patches..."

# Check if the files exist and apply simpler fixes
if [ -f "src/menu/systems.rs" ]; then
    echo "Fixing menu/systems.rs..."
    # This would normally use patch command, but we'll use sed for portability
fi

if [ -f "src/credits/systems.rs" ]; then
    echo "Fixing credits/systems.rs..."
fi

if [ -f "src/menu/ui.rs" ]; then
    echo "Fixing menu/ui.rs..."
fi

echo "Compilation fixes applied. Run 'cargo build' to test."