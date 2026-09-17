import CORALean.ContSet.Interval.Real.Interval

/-!
# An interval is bounded

Every coordinate is between its two bounds, so the supremum norm is at most the
sum over coordinates of `|inf| + |sup|` — each coordinate's own bound is one
term of it, and the rest are non-negative.

At `Vec ℝ n`: a bound on the norm is not a coordinatewise statement, so it needs
an ambient type whose norm the coordinates determine.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   01-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isBounded_construct (I : Interval (Vec ℝ n)) :
    Bornology.IsBounded I.construct := by -- --- PROOF ---
  refine isBounded_iff_forall_norm_le.mpr
    ⟨∑ i, (|I.inf i| + |I.sup i|), fun x hx => ?_⟩
  refine (pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => by positivity)).mpr fun i => ?_
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun i => |I.inf i| + |I.sup i|) (fun j _ => by positivity) (Finset.mem_univ i))
  -- `entry` at a vector is the coordinate, definitionally
  have h : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (I.inf i), abs_nonneg (I.sup i)]
  · linarith [le_abs_self (I.sup i), abs_nonneg (I.inf i)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
