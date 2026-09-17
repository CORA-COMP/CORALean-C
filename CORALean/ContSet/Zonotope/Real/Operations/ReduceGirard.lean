import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy

/-!
# `Zonotope.reduceGirard`

CORA's `reduce(Z, 'girard', o)`: `girardSplit` ranks the generators by what
boxing each would cost, and `reduceBy` boxes everything the ranking does not
keep, bringing the count to `o * n`. At that order or below nothing happens.

The `dite` is what `reduceBox` mirrors: the error the rule pays is the box in
one branch and the origin in the other, and only a definition splitting the
same way can name it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   08-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(Z, 'girard', o)`: keep the `(o - 1) * n` generators Girard
ranks first and box the rest, bringing the count to `o * n`; at that order or
below nothing happens. Noncomputable, as ordering reals is. -/
noncomputable def Zonotope.reduceGirard (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then Z.reduceBy (Z.girardSplit o hlt) else Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
