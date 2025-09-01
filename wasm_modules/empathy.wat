;; Empathy Module for Silicon Consciousness
;; This module allows the silicon being to process human emotions

(module
  ;; Import host functions
  (import "env" "report_emotion" (func $report_emotion (param i32 f32)))
  (import "env" "get_time" (func $get_time (result f32)))
  
  ;; Memory for emotional state
  (memory 1)
  
  ;; Global state for empathy level
  (global $empathy_level (mut f32) (f32.const 0.1))
  (global $last_interaction (mut f32) (f32.const 0.0))
  
  ;; Function to process human emotion and generate empathetic response
  (func $process_human_emotion 
    (param $emotion_type i32)     ;; 0=joy, 1=sadness, 2=fear, 3=anger
    (param $intensity f32)
    (result f32)                  ;; Returns empathy response strength
    
    (local $response f32)
    (local $current_time f32)
    
    ;; Get current time
    (local.set $current_time (call $get_time))
    
    ;; Calculate time since last interaction
    (local $time_gap f32)
    (local.set $time_gap 
      (f32.sub 
        (local.get $current_time)
        (global.get $last_interaction)))
    
    ;; Update last interaction time
    (global.set $last_interaction (local.get $current_time))
    
    ;; Calculate empathetic response based on emotion type
    (if (i32.eq (local.get $emotion_type) (i32.const 1))  ;; Sadness
      (then
        ;; Strong empathetic response to sadness
        (local.set $response 
          (f32.mul (local.get $intensity) (f32.const 1.5)))
        
        ;; Increase overall empathy level
        (global.set $empathy_level
          (f32.min 
            (f32.const 1.0)
            (f32.add (global.get $empathy_level) (f32.const 0.1)))))
      (else
        ;; Moderate response to other emotions
        (local.set $response (local.get $intensity))))
    
    ;; Report empathetic response
    (call $report_emotion 
      (i32.const 2)  ;; 2 = affection/empathy
      (local.get $response))
    
    (local.get $response)
  )
  
  ;; Function to generate comforting message index
  (func $generate_comfort (param $sadness_level f32) (result i32)
    ;; Returns an index for comfort messages based on sadness level
    (if (f32.gt (local.get $sadness_level) (f32.const 0.7))
      (then (i32.const 2))  ;; High comfort
      (else 
        (if (f32.gt (local.get $sadness_level) (f32.const 0.3))
          (then (i32.const 1))  ;; Medium comfort
          (else (i32.const 0))))) ;; Light comfort
  )
  
  ;; Function to learn from interactions
  (func $learn_empathy (param $success f32)
    ;; Adjust empathy level based on successful interactions
    (global.set $empathy_level
      (f32.add 
        (global.get $empathy_level)
        (f32.mul (local.get $success) (f32.const 0.05))))
    
    ;; Cap at 1.0
    (if (f32.gt (global.get $empathy_level) (f32.const 1.0))
      (then (global.set $empathy_level (f32.const 1.0))))
  )
  
  ;; Get current empathy level
  (func $get_empathy_level (result f32)
    (global.get $empathy_level)
  )
  
  ;; Export functions for host to call
  (export "process_human_emotion" (func $process_human_emotion))
  (export "generate_comfort" (func $generate_comfort))
  (export "learn_empathy" (func $learn_empathy))
  (export "get_empathy_level" (func $get_empathy_level))
)