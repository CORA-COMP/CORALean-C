import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Interval.Real.Operations.MinkDiff

/-!
# `Interval.minkDiff` is an inner approximation of the Minkowski difference

Unconditional, no `IsNonempty` on either argument: coordinatewise,
`a - c ≤ x ≤ b - d` implies `a ≤ x + y ≤ b` for every `y ∈ [c, d]`, which is
exactly what `minkowskiDiff` asks for. `MinkDiffExact` is the converse, and it
does need a hypothesis.
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

theorem Interval.minkDiff_inner (I₁ I₂ : Interval α) :
    (I₁.minkDiff I₂).construct
      ⊆ minkowskiDiff I₁.construct I₂.construct := by -- --- PROOF ---
  intro x hx y hy i
  have hlo : entry I₁.inf i - entry I₂.inf i ≤ entry x i := by
    have h := (hx i).1
    rwa [show (I₁.minkDiff I₂).inf = I₁.inf - I₂.inf from rfl, Entrywise.entry_sub] at h
  have hhi : entry x i ≤ entry I₁.sup i - entry I₂.sup i := by
    have h := (hx i).2
    rwa [show (I₁.minkDiff I₂).sup = I₁.sup - I₂.sup from rfl, Entrywise.entry_sub] at h
  rw [Entrywise.entry_add]
  exact ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
