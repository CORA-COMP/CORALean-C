import CORALean.ContSet.Zonotope.Float.Operations.PairDiff
import CORALean.ContSet.Zonotope.Float.Operations.PairSum

/-!
# The whole generator matrix of a linear combination, at one rounding

Split out of `LinComb.lean` (issue #62): `linCombGDiff` calls this at both
roundings, and `Theorems/LinCombOuter.lean` reads it directly, both outside
this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The whole generator matrix at one rounding: the two paired blocks and the
generator spanning the half-difference of the centres. -/
def Zonotope.linCombG (add sub : 𝕋 → 𝕋 → 𝕋) (Z₁ Z₂ : Zonotope 𝕋 n) :
    Mat 𝕋 n (Z₁.h + Z₂.h + 1) :=
  fun i => Fin.append
    (Fin.append (Zonotope.pairSum add (Z₁.G i) (Z₂.G i))
      (Zonotope.pairDiff sub (Z₁.G i) (Z₂.G i)))
    (fun _ : Fin 1 => half (sub (Z₁.c i) (Z₂.c i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
