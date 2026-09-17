import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

/-!
# A generator-free zonotope contains its own centre

`ofPoint v` states its own `h`, that counts only up to unfolding, so the sum
needs a `show`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_ofPoint (v : α) : v ∈ (Zonotope.ofPoint v).construct := by
  refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
  show v = v + ∑ j : Fin 0, Fin.elim0 j • Fin.elim0 j
  rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
