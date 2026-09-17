import CORALean.Global.Float.SoundFloatArithmetic

/-!
# Dyadic numbers at a fixed precision: the representation

`Dyadic p` is `mantissa * 2 ^ exponent` with the mantissa held to `p` bits. The
bound is what makes it a float model: unbounded dyadics are closed under `+`
and `*`, so rounding them would do nothing.

`p` is a phantom parameter rather than a field bound — the class constrains only
`toReal` of a result, so values off the grid are representable but never produced.
The exponent is unbounded, so nothing overflows, which is what
`SoundFloatArithmetic` assumes and why this instance needs no axioms.

`toReal` takes its power of two through ℚ, and that detour is what makes the
scalar *runnable*: a negative exponent is an inversion, ℝ's is noncomputable and
ℚ's is not, and a class field of type `𝕋 → ℝ` is data the compiler cannot erase,
so a noncomputable `toReal` would make every generic algorithm called at this
type noncomputable too. `toReal_def` is the number it denotes.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

structure Dyadic (p : ℕ) where
  mantissa : ℤ
  exponent : ℤ

def Dyadic.toReal {p : ℕ} (d : Dyadic p) : ℝ :=
  (d.mantissa : ℝ) * ((2 ^ d.exponent : ℚ) : ℝ)

/-- The number `toReal` denotes, past the rational detour it computes it by.
Every proof about `Dyadic` rewrites with this where it would have unfolded the
definition. -/
theorem Dyadic.toReal_def {p : ℕ} (d : Dyadic p) :
    Dyadic.toReal d = (d.mantissa : ℝ) * 2 ^ d.exponent := by
  rw [Dyadic.toReal, Rat.cast_zpow]
  norm_num

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
