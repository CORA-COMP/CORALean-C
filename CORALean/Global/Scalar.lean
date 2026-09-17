import CORALean.Global.Tensor

/-!
# The scalar a layer computes in

`Scalar 𝕋` is a type whose matrices and vectors denote real ones: ℝ itself, or a
machine scalar read entrywise. It is all the exact layer needs to know about the
arithmetic an implementation runs, which is what lets one guarantee cover both.

`toRealVec` is not `toRealMat` at a single column: a vector `Vec 𝕋 n` is a
function `Fin n → 𝕋`, not a `Matrix`, so reading it needs its own field.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

class Scalar (𝕋 : Type) where
  toRealMat {m n : ℕ} : Mat 𝕋 m n → Mat ℝ m n
  toRealVec {n : ℕ} : Vec 𝕋 n → Vec ℝ n

/-- ℝ stores itself. -/
instance : Scalar ℝ where
  toRealMat M := M
  toRealVec v := v

/-- True by `rfl`, but a proof about the real layer has to rewrite with it. -/
@[simp] theorem Scalar.toRealMat_real {m n : ℕ} (M : Mat ℝ m n) : toRealMat M = M := rfl

/-- True by `rfl`, but a proof about the real layer has to rewrite with it. -/
@[simp] theorem Scalar.toRealVec_real {n : ℕ} (v : Vec ℝ n) : toRealVec v = v := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
