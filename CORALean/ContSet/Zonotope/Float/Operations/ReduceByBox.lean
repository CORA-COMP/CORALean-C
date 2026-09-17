import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
import CORALean.Global.Partition

/-!
# `Zonotope.reduceByBox`

The error `reduceBy` pays, as `Real`'s own `reduceByBox` with one difference:
the row sums it boxes are rounded up, `reduceBy`'s own diagonal block being
built from `radius` rather than an exact sum. Centred at `0`, for the same
reason `Real`'s is — the dropped generators contribute `0` to `Z` when their
coefficients are set to `0`, so the reduced set never reaches further than `Z`
plus this box.

Not a `Reduce` operation and no class instantiates it, as at `Real`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `reduceBy` absorbs the dropped generators into, on its own: one
entry per coordinate, the rounded-up absorbed rows' `1`-norm, centred at the
origin. -/
noncomputable def Zonotope.reduceByBox (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Real.Zonotope (Vec ℝ n) where
  h := n
  c := 0
  G := Matrix.diagonal fun i => toReal (radius (fun i l => Z.G i (part.right l)) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
