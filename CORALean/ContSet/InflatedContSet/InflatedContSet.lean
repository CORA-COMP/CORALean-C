import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Interval.Float.Interval

/-!
# Representations that carry a rounding error

A nominal representation inflated by an axis-aligned box holding what rounding
has cost so far. An operation never rounds its nominal part into shape: it
computes that part however it likes and pays the difference into the box.

For a zonotope that is the point — rounding paid into new generators would grow
the generator count on every operation, which is what reachability costs.

`Interval` deliberately has no instance: it *is* the box. Boxes are built by
whoever knows what was rounded (`Interval.residual`, `Interval.symmetric`,
`Zonotope.generatorError`), and none of those mentions this class.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic


-- ========================================  MAIN TYPE  ========================================= --

class InflatedContSet (S : Type) (N : outParam Type) (𝕋 : outParam Type) (n : outParam ℕ)
    [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ContSet N (Vec ℝ n)] where
  /-- The exact-layer representation the stored floats describe, not the set it
  denotes — keeping the representation is what lets a refinement proof reach the
  theorem about it. -/
  nominal : S → N
  /-- Everything rounding has cost, as a box. Held in `𝕋` because operations
  compute it. -/
  error : S → Interval 𝕋 n

namespace InflatedContSet

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [InflatedContSet S N 𝕋 n]

/-- What the nominal part denotes. Generic code cannot write
`s.nominal.construct`, since dot notation resolves through a head constant and
`N` is a variable. -/
abbrev nominalSet (s : S) : Set (Vec ℝ n) := ContSet.construct (nominal s)

def construct (s : S) : Set (Vec ℝ n) := nominalSet s + (error s).construct

instance : ContSet S (Vec ℝ n) := ⟨construct⟩

end InflatedContSet

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
