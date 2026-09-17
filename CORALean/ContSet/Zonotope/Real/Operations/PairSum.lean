import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The paired-sum generator column

Split out of `LinComb.lean` (issue #62): shared with `Zonotope.pairDiff` by
`Theorems/SumPair.lean`, and with the float layer's rounded version, which reads
this one back through `toReal` in `PairSumBracket.lean`.

Half the sum of a generator and the column it pairs with; past the shorter
block there is no partner and the generator is kept whole.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h₁ h₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Half the sum of a generator and the column it pairs with, or the generator
whole where the other block has run out. -/
noncomputable def Zonotope.pairSum (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α) (j : Fin h₁) : α :=
  if hj : (j : ℕ) < h₂ then (2:ℝ)⁻¹ • (G₁ j + G₂ ⟨j, hj⟩) else G₁ j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
