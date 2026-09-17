import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import CORALean.ContSet.Interval.Real.Theorems.MinkDiffInner

/-!
# `Interval.minkDiff` is exactly the Minkowski difference

`I₂` must be `IsNonempty`: it is what puts `I₂.inf` and `I₂.sup` themselves in
`I₂.construct`, and evaluating the difference hypothesis at those two points is
the whole proof of the hard direction. `minkDiff_inner` is the easy half, and it
needs no such hypothesis.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.minkDiff_exact (I₁ I₂ : Interval α) (h₂ : I₂.IsNonempty) :
    minkowskiDiff I₁.construct I₂.construct =
      (I₁.minkDiff I₂).construct := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (Interval.minkDiff_inner I₁ I₂)
  intro i
  have hmemInf : I₂.inf ∈ I₂.construct := fun j => ⟨le_refl _, h₂ j⟩
  have hmemSup : I₂.sup ∈ I₂.construct := fun j => ⟨h₂ j, le_refl _⟩
  have hlo := (hx I₂.inf hmemInf i).1
  have hhi := (hx I₂.sup hmemSup i).2
  rw [Entrywise.entry_add] at hlo hhi
  rw [show (I₁.minkDiff I₂).inf = I₁.inf - I₂.inf from rfl, Entrywise.entry_sub,
      show (I₁.minkDiff I₂).sup = I₁.sup - I₂.sup from rfl, Entrywise.entry_sub]
  exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
