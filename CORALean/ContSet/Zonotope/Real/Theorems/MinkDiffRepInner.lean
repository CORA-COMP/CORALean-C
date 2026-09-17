import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

/-!
# `Zonotope.minkDiffRep` is an inner approximation of the Minkowski difference

Both halves of the sum are spent in the minuend's own coefficients: `βᵢ` on the
scaled generator `i`, and `∑ⱼ γⱼ Mᵢⱼ` on what the subtrahend's point costs
there. The triangle inequality bounds the second by `∑ⱼ |Mᵢⱼ|` whatever `γ`
is, which is exactly why the check subtracts that much and no less — the
scaling is forced by the proof, not chosen ahead of it.

So soundness asks nothing of the shape of either zonotope, only that `M`
represents: the same argument at `Mᵢⱼ = μᵢ` on the diagonal and `0` off it is
`minkDiffAligned_inner`. Each of the check's two facts is used exactly once,
`hrow` for the bound and `hM` for the equation.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffRep_inner (Z₁ Z₂ : Zonotope α) (M : Fin Z₁.h → Fin Z₂.h → ℝ)
    {D : Zonotope α} (hD : Z₁.minkDiffRep Z₂ M = some D) :
    D.construct ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  unfold Zonotope.minkDiffRep at hD
  split_ifs at hD with hchk
  obtain ⟨hM, hrow⟩ := hchk
  obtain rfl := Option.some.inj hD
  rintro x ⟨β, hβ, rfl⟩ y ⟨γ, hγ, rfl⟩
  dsimp only
  refine ⟨fun i => β i * (1 - ∑ j, |M i j|) + ∑ j, γ j * M i j, fun i => ?_, ?_⟩
  · -- row `i`'s budget: what `M` does not take there is what `βᵢ` may spend
    have h0 : (0:ℝ) ≤ 1 - ∑ j, |M i j| := by linarith [hrow i]
    have h1 : |∑ j, γ j * M i j| ≤ ∑ j, |M i j| :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hγ j))
    have h2 : |β i * (1 - ∑ j, |M i j|)| ≤ 1 * (1 - ∑ j, |M i j|) := by
      rw [abs_mul, abs_of_nonneg h0]
      exact mul_le_mul_of_nonneg_right (hβ i) h0
    have h3 := abs_add_le (β i * (1 - ∑ j, |M i j|)) (∑ j, γ j * M i j)
    linarith
  · -- the subtrahend's generators re-expressed, then the two sums merged
    have hG : ∀ j, γ j • Z₂.G j = ∑ i, (γ j * M i j) • Z₁.G i := by
      intro j
      rw [hM j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    have hswap : ∑ j, γ j • Z₂.G j = ∑ i, (∑ j, γ j * M i j) • Z₁.G i := by
      rw [Finset.sum_congr rfl fun j _ => hG j, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]
    calc Z₁.c - Z₂.c + ∑ i, β i • ((1 - ∑ j, |M i j|) • Z₁.G i)
            + (Z₂.c + ∑ j, γ j • Z₂.G j)
        = Z₁.c + (∑ i, (β i * (1 - ∑ j, |M i j|)) • Z₁.G i
            + ∑ i, (∑ j, γ j * M i j) • Z₁.G i) := by
          rw [hswap]; simp only [smul_smul]; abel
      _ = Z₁.c + ∑ i, ((β i * (1 - ∑ j, |M i j|)) • Z₁.G i
            + (∑ j, γ j * M i j) • Z₁.G i) := by rw [← Finset.sum_add_distrib]
      _ = Z₁.c + ∑ i, (β i * (1 - ∑ j, |M i j|) + ∑ j, γ j * M i j) • Z₁.G i :=
          congrArg _ (Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
