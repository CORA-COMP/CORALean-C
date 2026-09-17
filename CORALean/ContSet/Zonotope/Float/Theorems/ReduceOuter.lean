import CORALean.ContSet.Zonotope.Float.Operations.Reduce
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter

/-!
# `Zonotope.reduce` over-approximates the zonotope

Girard's is the rule `reduce` runs, and this is the whole of that choice: any
other rule would discharge it too.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem Zonotope.reduce_outer (Z : Zonotope 𝕋 n) (o : ℕ) :
    Z.construct ⊆ (Z.reduce o).construct :=
  Zonotope.reduceGirard_outer Z o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
