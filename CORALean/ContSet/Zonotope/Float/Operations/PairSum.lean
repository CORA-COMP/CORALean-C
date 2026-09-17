import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# The paired-sum generator column, over a floating-point scalar

Split out of `LinComb.lean` (issue #62): `linCombG` uses it, and
`PairSumBracket.lean` reads it back against `Real.Zonotope.pairSum`, both
outside this file.

Takes the directed addition as an argument rather than fixing one, since
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

/-- Half the sum of a generator and the column it pairs with, formed with the
given directed addition; past the shorter block the generator is copied and
nothing rounds. -/
def Zonotope.pairSum (add : 𝕋 → 𝕋 → 𝕋) (G₁ : Fin h₁ → 𝕋) (G₂ : Fin h₂ → 𝕋)
    (j : Fin h₁) : 𝕋 :=
  if hj : (j : ℕ) < h₂ then half (add (G₁ j) (G₂ ⟨j, hj⟩)) else G₁ j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
