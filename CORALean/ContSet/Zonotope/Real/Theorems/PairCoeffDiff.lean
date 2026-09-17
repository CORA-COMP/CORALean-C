import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The coefficient the paired-difference generator carries

The mirror of `pairCoeffSum` on the second block: the two weighted coefficients
subtracted, so that sum and difference together recover both originals. Past the
shorter block the surplus column again carries its own weight alone.

A proof device rather than an operation, hence in `Theorems/`: it only ever
witnesses an existential and is never run.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h₁ h₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficient the paired-difference generator carries. -/
def Zonotope.pairCoeffDiff (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) (j : Fin h₂) : ℝ :=
  if hj : (j : ℕ) < h₁ then lam * β₁ ⟨j, hj⟩ - (1 - lam) * β₂ j else (1 - lam) * β₂ j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
