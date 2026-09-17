import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.intersection`

CORA's `@polytope/and_`: the constraint lists concatenate, so an intersection
costs nothing and loses nothing. The operation halfspaces are for.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.intersection (P₁ P₂ : HPolytope α) : HPolytope α where
  m := P₁.m + P₂.m
  A := Fin.append P₁.A P₂.A
  b := Fin.append P₁.b P₂.b
  me := P₁.me + P₂.me
  Ae := Fin.append P₁.Ae P₂.Ae
  be := Fin.append P₁.be P₂.be

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
