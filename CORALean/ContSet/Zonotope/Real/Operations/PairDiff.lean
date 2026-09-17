import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The paired-difference generator column

Split out of `LinComb.lean` (issue #62): shared with `Zonotope.pairSum` by
`Theorems/SumPair.lean`, and with the float layer's rounded version, which reads
this one back through `toReal` in `PairDiffBracket.lean`.

Half the difference, the other half of a pairing; past the shorter block it is
the second set's surplus generator, whole.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h₁ h₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Half the difference, the other half of a pairing; past the shorter block it
is the second set's surplus generator, whole. -/
noncomputable def Zonotope.pairDiff (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α) (j : Fin h₂) : α :=
  if hj : (j : ℕ) < h₁ then (2:ℝ)⁻¹ • (G₁ ⟨j, hj⟩ - G₂ j) else G₂ j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
