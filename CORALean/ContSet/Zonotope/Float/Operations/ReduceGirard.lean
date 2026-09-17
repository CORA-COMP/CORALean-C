import CORALean.ContSet.Zonotope.Float.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy

/-!
# `Zonotope.reduceGirard`

CORA's `reduce(Z, 'girard', o)`: `girardSplit` ranks the generators by what
boxing each would cost, and `reduceBy` boxes everything the ranking does not
keep, bringing the count to `o * n`. At that order or below nothing happens.

The `dite` is what `reduceGirardBox` mirrors: the error the rule pays is the
box in one branch and the origin in the other, and only a definition splitting
the same way can name it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   08-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, as over ℝ, and which it is goes no further —
a caller names an order and gets an over-approximation. -/
def Zonotope.reduceGirard (Z : Zonotope 𝕋 n) (o : ℕ) : Zonotope 𝕋 n :=
  if hlt : o * n < Z.h then Z.reduceBy (Z.girardSplit o hlt) else Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
