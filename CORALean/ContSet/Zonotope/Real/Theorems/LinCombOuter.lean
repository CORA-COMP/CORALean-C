import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffDiffLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffSumLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.SumPair

/-!
# `linComb` contains every segment between the two zonotopes

The paired blocks carry `λ β₁ ± (1-λ) β₂`, both back in `[-1,1]` because the two
weights sum to one, and the generator spanning the half-difference of the
centres carries `2λ - 1`. Past the shorter block a surplus generator carries its
own weighted coefficient alone.

Nothing here asks for convexity: the claim is about the segments themselves, so
it is the statement a non-convex representation could also make.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Zonotope.aux_sum_univ_linComb {Z₁ Z₂ : Zonotope α}
    (f : Fin (Z₁.h + Z₂.h + 1) → α) :
    ∑ j : Fin (Z₁.linComb Z₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (Z₁.h + Z₂.h) j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

-- the closing `module` call normalises a sum over the doubly appended generator index
set_option maxHeartbeats 400000 in
theorem Zonotope.linComb_outer (Z₁ Z₂ : Zonotope α) :
    segments Z₁.construct Z₂.construct ⊆ (Z₁.linComb Z₂).construct := by -- --- PROOF ---
  rintro x ⟨y₁, ⟨β₁, hβ₁, rfl⟩, y₂, ⟨β₂, hβ₂, rfl⟩, lam, ⟨hl0, hl1⟩, rfl⟩
  refine ⟨Fin.append (Fin.append (Zonotope.pairCoeffSum β₁ β₂ lam)
      (Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1), ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa using Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
      · intro j
        simpa using Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · rw [Zonotope.aux_sum_univ_linComb, Fin.sum_univ_add]
    simp only [Zonotope.linComb, Fin.append_left, Fin.append_right, Fin.sum_univ_one]
    rw [Zonotope.sum_pair Z₁.G Z₂.G β₁ β₂ lam]
    -- what is left is the centres, which the fresh generator carries
    module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
