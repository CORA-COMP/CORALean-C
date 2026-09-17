import Lake
open Lake DSL

/-! `CORALean/` is the part of [CORALean](https://gitlab.lrz.de/cps/coralean) that
`Main.lean` reaches, copied unchanged; see the README for the commit. -/

package CORALeanC where
  -- CORALean's own options, so its proofs check here as they do there
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxHeartbeats, (40000 : Nat)⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

lean_lib CORALean where
  globs := #[.submodules `CORALean]

lean_lib CoraleanC where
  globs := #[.submodules `CoraleanC]

@[default_target]
lean_exe «coralean-c» where
  root := `Main
