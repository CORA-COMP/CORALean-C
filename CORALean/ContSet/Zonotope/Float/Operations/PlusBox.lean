import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

/-!
# `Zonotope.plusBox`

What `plus` can add beyond the Minkowski sum of its two operands' `construct`:
a single point, the gap between the exact centre sum and the one directed
rounding stores, and the result's own error box read back as a zonotope. The
generators never round — `plus` concatenates them exactly — so this is the
whole of it.

Not an operation `Reduce`-style: no class asks a representation for how far a
binary operation may overshoot its inputs, and only `plus`'s own definition can
say. Real-valued, like `reachError`, since it feeds a `Real` accumulator.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The point `plus`'s stored centre misses the exact sum by, together with the
result's own error box read back as a zonotope. -/
noncomputable def Zonotope.plusBox (Z₁ Z₂ : Zonotope 𝕋 n) : Real.Zonotope (Vec ℝ n) :=
  (Real.Zonotope.ofPoint fun i =>
      toReal (addDown (Z₁.c i) (Z₂.c i)) - toReal (Z₁.c i) - toReal (Z₂.c i)).plus
    ((Z₁.plus Z₂).E.nominal.zonotope)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
