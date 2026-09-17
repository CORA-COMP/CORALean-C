import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffDiff
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffSum

/-!
# The paired blocks recombine into the two original ones

The pairing is what the proof has to work for: it couples column `j` of one
block with column `j` of the other, so neither block sum closes on its own. Both
are read over the common range `h₁ + h₂` with the summand padded by zero, where
the identity is pointwise — a column both sets have, a column only one has, or
neither.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h₁ h₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- A block sum read over a longer range, the summand padded with zero. What
lets the two paired blocks meet: neither closes on its own, and over a common
range the identity is pointwise. -/
theorem Zonotope.aux_sum_pad {k N : ℕ} (hk : k ≤ N) (f : Fin k → α) :
    ∑ j, f j = ∑ i ∈ Finset.range N, (if h : i < k then f ⟨i, h⟩ else 0) := by -- --- PROOF ---
  have hfin : ∑ j, f j
      = ∑ i ∈ Finset.range k, (if h : i < k then f ⟨i, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < k then f ⟨i, h⟩ else 0) k]
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  rw [hfin]
  refine Finset.sum_subset
    (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
    fun i _ hi => dif_neg (by simpa using hi)

/-- A weight pulled out of a block sum: `module` cannot do this for itself, a
sum being one atom to it. -/
theorem Zonotope.aux_sum_weighted {k : ℕ} (w : ℝ) (b : Fin k → ℝ) (g : Fin k → α) :
    ∑ j, (w * b j) • g j = w • ∑ j, b j • g j := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (smul_smul w (b j) (g j)).symm


-- =======================================  MAIN THEOREM  ======================================= --

/-- The paired blocks recombine into the two original ones. Over a column both
sets have, the sum and the difference generator carry `λβ₁` and `(1-λ)β₂`
between them; past the shorter block each surplus generator carries its own. -/
theorem Zonotope.sum_pair (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α)
    (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) :
    (∑ j, Zonotope.pairCoeffSum β₁ β₂ lam j • Zonotope.pairSum G₁ G₂ j)
        + ∑ j, Zonotope.pairCoeffDiff β₁ β₂ lam j • Zonotope.pairDiff G₁ G₂ j
      = lam • (∑ j, β₁ j • G₁ j) + (1 - lam) • ∑ j, β₂ j • G₂ j := by -- --- PROOF ---
  rw [← Zonotope.aux_sum_weighted lam β₁ G₁, ← Zonotope.aux_sum_weighted (1 - lam) β₂ G₂,
    Zonotope.aux_sum_pad (Nat.le_add_right h₁ h₂)
      (fun j => Zonotope.pairCoeffSum β₁ β₂ lam j • Zonotope.pairSum G₁ G₂ j),
    Zonotope.aux_sum_pad (Nat.le_add_left h₂ h₁)
      (fun j => Zonotope.pairCoeffDiff β₁ β₂ lam j • Zonotope.pairDiff G₁ G₂ j),
    Zonotope.aux_sum_pad (Nat.le_add_right h₁ h₂) (fun j => (lam * β₁ j) • G₁ j),
    Zonotope.aux_sum_pad (Nat.le_add_left h₂ h₁) (fun j => ((1 - lam) * β₂ j) • G₂ j),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Zonotope.pairCoeffSum, Zonotope.pairSum, Zonotope.pairCoeffDiff,
    Zonotope.pairDiff]
  split_ifs <;> module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
