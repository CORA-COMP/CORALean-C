import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter

/-!
# `Interval.plus` is exactly the Minkowski sum

Coordinatewise. Splitting a point of the sum is the only work: `I₁` takes
`min (I₁.sup i) (x i - I₂.inf i)`, and the bounds leave a remainder `I₂` holds.

Both boxes must be `IsNonempty`: `[1, 0] + [0, 10]` is `∅` as a set but `[1, 10]`
by the definition. `plus_outer` is the half that needs no such hypothesis.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

-- every `Entrywise` rewrite unfolds `plus` by `rfl`, and the four `linarith` calls pay for it
set_option maxHeartbeats 400000 in
theorem Interval.plus_exact (I₁ I₂ : Interval α) (h₁ : I₁.IsNonempty) (h₂ : I₂.IsNonempty) :
    I₁.construct + I₂.construct = (I₁.plus I₂).construct := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset (Interval.plus_outer I₁ I₂) fun x hx => ?_
  have hlo : ∀ i, entry I₁.inf i + entry I₂.inf i ≤ entry x i := fun i => by
    have h := (hx i).1
    rwa [show (I₁.plus I₂).inf = I₁.inf + I₂.inf from rfl, Entrywise.entry_add] at h
  have hhi : ∀ i, entry x i ≤ entry I₁.sup i + entry I₂.sup i := fun i => by
    have h := (hx i).2
    rwa [show (I₁.plus I₂).sup = I₁.sup + I₂.sup from rfl, Entrywise.entry_add] at h
  -- the first summand, built from coordinates and then read back off
  set f : ι → ℝ := fun i => min (entry I₁.sup i) (entry x i - entry I₂.inf i) with hf
  refine ⟨ofEntry f, fun i => ?_, x - ofEntry f, fun i => ?_, add_sub_cancel _ _⟩
  · rw [Entrywise.entry_ofEntry]
    exact ⟨le_min (h₁ i) (by linarith [hlo i]), min_le_left _ _⟩
  · rw [Entrywise.entry_sub, Entrywise.entry_ofEntry, hf]
    constructor
    · linarith [min_le_right (entry I₁.sup i) (entry x i - entry I₂.inf i)]
    · have : entry x i - entry I₂.sup i
          ≤ min (entry I₁.sup i) (entry x i - entry I₂.inf i) :=
        le_min (by linarith [hhi i]) (by linarith [h₂ i])
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
