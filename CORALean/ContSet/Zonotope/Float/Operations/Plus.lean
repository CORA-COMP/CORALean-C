import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual

/-!
# `Zonotope.plus`

Generators concatenate exactly, so only the centre rounds and its `residual`
goes into the box, leaving the count at `h₁ + h₂` as over ℝ. Paying into new
generators instead would cost `n` more on every addition.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.plus (Z₁ Z₂ : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z₁.h + Z₂.h
  c := fun i => addDown (Z₁.c i) (Z₂.c i)
  G := fun i => Fin.append (Z₁.G i) (Z₂.G i)
  E := (Z₁.E.plus Z₂.E).plus (Zonotope.centerResidual Z₁.c Z₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
