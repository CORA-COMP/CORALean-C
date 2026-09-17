import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.Convex

/-!
# A float zonotope is convex

Not the exact layer's theorem at float data: what this denotes is a nominal
zonotope *plus* an error box, so what carries convexity across is
`Convex.add`, over two sets each convex for its own reason — the nominal one
as an affine image of a cube, the box because its coordinates are bounded
independently.

So the error box costs the property nothing, which is why no operation has to
restate it after paying a rounding into that box.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.convex_construct (Z : Zonotope 𝕋 n) : Convex ℝ Z.construct :=
  Convex.add (nominal Z).convex_construct Z.E.nominal.convex_construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
