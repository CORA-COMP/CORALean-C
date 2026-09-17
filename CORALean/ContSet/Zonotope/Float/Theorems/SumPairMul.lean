import CORALean.ContSet.Zonotope.Real.Theorems.SumPair

/-!
# `sum_pair` with the coefficient following the generator

The order a stored row is read in.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {h₁ h₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Zonotope.sum_pair` where the coefficient follows the generator, which is
the order a stored row is read in. -/
theorem Zonotope.sum_pair_mul (g₁ : Fin h₁ → ℝ) (g₂ : Fin h₂ → ℝ)
    (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) :
    (∑ j, Real.Zonotope.pairSum g₁ g₂ j * Real.Zonotope.pairCoeffSum β₁ β₂ lam j)
        + ∑ j, Real.Zonotope.pairDiff g₁ g₂ j * Real.Zonotope.pairCoeffDiff β₁ β₂ lam j
      = lam * (∑ j, g₁ j * β₁ j) + (1 - lam) * ∑ j, g₂ j * β₂ j := by -- --- PROOF ---
  have key := Real.Zonotope.sum_pair g₁ g₂ β₁ β₂ lam
  simp only [smul_eq_mul] at key
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
        mul_comm (Real.Zonotope.pairSum g₁ g₂ j) (Real.Zonotope.pairCoeffSum β₁ β₂ lam j)),
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
      mul_comm (Real.Zonotope.pairDiff g₁ g₂ j) (Real.Zonotope.pairCoeffDiff β₁ β₂ lam j)),
    key, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => mul_comm (g₁ j) (β₁ j)),
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => mul_comm (g₂ j) (β₂ j))]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
