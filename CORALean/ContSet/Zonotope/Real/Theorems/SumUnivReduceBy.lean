import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy

/-!
# Splitting a sum over what `reduceBy` produces

The kept generators and the one box column per coordinate, counted apart. Stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type, which is also why the float refinement proof reaches
for it rather than for `Fin.sum_univ_add` directly.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Fin.sum_univ_add` at `reduceBy`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Zonotope.sum_univ_reduceBy {Z : Zonotope (Vec ℝ n)}
    {part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)} (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (Z.reduceBy part).h, f j = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
