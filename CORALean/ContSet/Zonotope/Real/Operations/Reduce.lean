import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

/-!
# `Zonotope.reduce`

CORA's `@zonotope/reduce`: bring the generator count down to a maximum order.
Girard's rule is the one used here; which rule that is goes no further — a
caller names an order and gets an over-approximation.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, and which it is goes no further — a caller
names an order and gets an over-approximation. -/
noncomputable def Zonotope.reduce (Z : Zonotope (Vec ℝ n)) (o : ℕ) : Zonotope (Vec ℝ n) :=
  Z.reduceGirard o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
