import CORALean.Global.Float.Instances.Dyadic.Theorems.DivDownLeDiv
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeDivUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.RoundDownLe
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactMul
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealHalf
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealLeOfLe
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMaximum
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMinimum
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMkZero
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealNeg

/-!
# `Dyadic` as a sound float model

Each obligation is exactness composed with a rounding direction, the two halves
proved separately in `Theorems`. Division has no exact half to compose with and
arrives already directed. `le` is exact and needs no rounding at all. No bound
on the mantissa is needed: leaving the grid costs precision, never soundness.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

instance {p : ℕ} : FloatOps (Dyadic p) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  neg := Dyadic.neg
  addUp := Dyadic.addUp
  addDown := Dyadic.addDown
  mulUp := Dyadic.mulUp
  mulDown := Dyadic.mulDown
  divUp := Dyadic.divUp
  divDown := Dyadic.divDown
  minimum := Dyadic.minimum
  maximum := Dyadic.maximum
  le := Dyadic.le
  half := Dyadic.half

/-- Computable, which is what lets an algorithm written against the operation
classes be *run* at `Dyadic`: a `toReal` the compiler cannot erase would make
every instance derived from this one noncomputable. -/
instance {p : ℕ} : SoundFloatArithmetic (Dyadic p) where
  toReal := Dyadic.toReal
  toReal_neg := Dyadic.toReal_neg
  toReal_zero := Dyadic.toReal_mk_zero 0
  toReal_one := by
    show Dyadic.toReal (⟨1, 0⟩ : Dyadic p) = 1
    rw [Dyadic.toReal_def]
    norm_num
  add_le_addUp a b := Dyadic.toReal_exactAdd a b ▸ Dyadic.le_roundUp _
  addDown_le_add a b := Dyadic.toReal_exactAdd a b ▸ Dyadic.roundDown_le _
  mul_le_mulUp a b := Dyadic.toReal_exactMul a b ▸ Dyadic.le_roundUp _
  mulDown_le_mul a b := Dyadic.toReal_exactMul a b ▸ Dyadic.roundDown_le _
  div_le_divUp := Dyadic.le_divUp
  divDown_le_div := Dyadic.divDown_le_div
  toReal_minimum := Dyadic.toReal_minimum
  toReal_maximum := Dyadic.toReal_maximum
  toReal_le_of_le := Dyadic.toReal_le_of_le
  toReal_half := Dyadic.toReal_half

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
