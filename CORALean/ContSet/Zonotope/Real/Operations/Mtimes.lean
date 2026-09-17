import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.mtimes`

CORA's `@zonotope/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.mtimes (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ m) where
  h := Z.h
  c := M *ᵥ Z.c
  G := fun j => M *ᵥ Z.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
