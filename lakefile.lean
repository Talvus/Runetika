import Lake
open Lake DSL

package runetika

require mathlib from git
  "file:///Users/tensorhusker/Git/mathlib4"

lean_lib Runetika

@[default_target]
lean_exe runetika {
  root := `Main
}
