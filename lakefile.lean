import Lake
open Lake DSL

package "ai-planning" where
  version := v!"0.1.0"
  keywords := #[]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «AIPlanning» where
  -- add any library configuration options here
