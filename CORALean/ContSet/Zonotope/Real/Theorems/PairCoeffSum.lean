import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The coefficient the paired-sum generator carries

`linComb` pairs column `j` of one generator block with column `j` of the other,
so the two weighted coefficients travel together on one generator. Past the
shorter block there is no partner and the surplus column carries its own weight
alone.

A proof device rather than an operation, hence in `Theorems/`: it only ever
witnesses an existential and is never run. The float layer and
`PolyZonotope.linComb`'s independent block use the same one.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h₁ h₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficient the paired-sum generator carries: the two weighted
coefficients added, which is what records that they share one `λ`. -/
def Zonotope.pairCoeffSum (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) (j : Fin h₁) : ℝ :=
  if hj : (j : ℕ) < h₂ then lam * β₁ j + (1 - lam) * β₂ ⟨j, hj⟩ else lam * β₁ j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
