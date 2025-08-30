import Lake
open Lake DSL

package runetika

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Runetika

@[default_target]
lean_exe runetika {
  root := `Main
}
