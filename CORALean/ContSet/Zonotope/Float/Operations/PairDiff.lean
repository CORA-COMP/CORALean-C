import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# The paired-difference generator column, over a floating-point scalar

Split out of `LinComb.lean` (issue #62): `linCombG` uses it, and
`PairDiffBracket.lean` reads it back against `Real.Zonotope.pairDiff`, both
outside this file.

Takes the directed subtraction as an argument rather than fixing one, since
`linCombGDiff` needs the same column rounded both ways.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {h₁ h₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Half the difference, the other half of a pairing; past the shorter block it
is the second set's surplus generator, copied. -/
def Zonotope.pairDiff (sub : 𝕋 → 𝕋 → 𝕋) (G₁ : Fin h₁ → 𝕋) (G₂ : Fin h₂ → 𝕋)
    (j : Fin h₂) : 𝕋 :=
  if hj : (j : ℕ) < h₁ then half (sub (G₁ ⟨j, hj⟩) (G₂ j)) else G₂ j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
