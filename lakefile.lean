import Lake
open Lake DSL

package EBPFSpec

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.7.0"

@[default_target]
lean_lib «EBPFSpec» where
  -- add any library configuration options here
