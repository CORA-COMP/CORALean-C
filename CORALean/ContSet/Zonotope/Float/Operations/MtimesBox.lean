import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

/-!
# `Zonotope.mtimesBox`

What `mtimes` can add beyond the image of its operand's `construct`: one
generator per `Z`'s own — the centre and each generator round, so this is
`Z.h` generators, the same count `mtimesResidual` charges — together with the
result's own error box read back as a zonotope.

Not an operation `Reduce`-style, for the same reason `plusBox` is not: only
`mtimes`'s own definition can say how far it may overshoot its operand.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One generator per `Z`'s own, holding what `mtimes`'s centre and that
generator missed of the exact image, together with the result's own error box
read back as a zonotope. -/
noncomputable def Zonotope.mtimesBox (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Real.Zonotope (Vec ℝ m) :=
  (⟨Z.h,
      fun i => toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k),
      fun j i => toReal (matMulDown M Z.G i j) - ∑ k, toReal (M i k) * toReal (Z.G k j)⟩ :
    Real.Zonotope (Vec ℝ m)).plus ((Zonotope.mtimes M Z).E.nominal.zonotope)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
