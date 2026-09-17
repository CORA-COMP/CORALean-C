import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.plus`

CORA's `@zonotope/plus`: centres add, generators concatenate.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.plus (Z₁ Z₂ : Zonotope α) : Zonotope α where
  h := Z₁.h + Z₂.h
  c := Z₁.c + Z₂.c
  G := Fin.append Z₁.G Z₂.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
