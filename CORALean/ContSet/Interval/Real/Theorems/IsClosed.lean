import CORALean.ContSet.Interval.Real.Interval

/-!
# An interval is closed

An intersection of closed half-spaces, one pair per coordinate, each the
preimage of a closed ray under an evaluation map. Holds for any bounds: the
degenerate `sup i < inf i` denotes `∅`, which is closed too.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isClosed_construct (I : Interval (Vec ℝ n)) :
    IsClosed I.construct := by -- --- PROOF ---
  have hinter : I.construct
      = ⋂ i, ({x : Vec ℝ n | I.inf i ≤ x i} ∩ {x : Vec ℝ n | x i ≤ I.sup i}) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [hinter]
  refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_apply i) continuous_const

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
