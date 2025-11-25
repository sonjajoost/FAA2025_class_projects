import Lake
open Lake DSL

package «FAA2025_class_projects» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"

@[default_target]
lean_lib «Projects» where
  globs := #[.submodules `Projects]
