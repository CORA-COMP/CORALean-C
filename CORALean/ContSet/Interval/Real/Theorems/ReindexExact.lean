import CORALean.ContSet.Interval.Real.Operations.Reindex

/-!
# `Interval.reindex` is exactly the relabelled box

An equality, not an enclosure, and the hypothesis doing the work is that the
relabelling is a bijection: the preimage `y ∘ e⁻¹` is the point the box has to
contain, and it exists only because every coordinate is hit exactly once.

A non-injective relabelling would break the `⊆` direction — two output
coordinates reading the same input must agree, and an axis-aligned box cannot
express that — which is why `Reindex` takes an `Equiv`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.reindex_exact (e : Fin m ≃ Fin n) (I : Interval (Vec ℝ n)) :
    (I.reindex e).construct = reindexLin e '' I.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · intro y hy
    refine ⟨fun j => y (e.symm j), fun j => ?_, funext fun i => ?_⟩
    · have h : I.inf (e (e.symm j)) ≤ y (e.symm j) ∧ y (e.symm j) ≤ I.sup (e (e.symm j)) :=
        hy (e.symm j)
      rw [Equiv.apply_symm_apply] at h
      exact h
    · show y (e.symm (e i)) = y i
      rw [Equiv.symm_apply_apply]
  · rintro _ ⟨x, hx, rfl⟩
    exact fun i => hx (e i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
