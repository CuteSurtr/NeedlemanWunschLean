import Lake
open Lake DSL

package "NeedlemanWunschLean" where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

@[default_target]
lean_lib «NeedlemanWunschLean» where
