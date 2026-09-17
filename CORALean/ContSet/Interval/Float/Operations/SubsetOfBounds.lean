import CORALean.ContSet.Interval.Float.Operations.OfBounds

/-!
# `Interval.ofBounds` encloses, over a floating-point scalar

Nothing rounds: each bound was already rounded outward where it was computed,
and negating a float is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {S : Set (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.subset_ofBounds (up : ∀ j, FloatBound 𝕋 S (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 S (-LinearMap.proj j)) :
    S ⊆ (Interval.ofBounds up lo).construct := by -- --- PROOF ---
  intro x hx j
  constructor
  · have h : -(x j) ≤ toReal (lo j).val := (lo j).le x hx
    show toReal (neg (lo j).val) ≤ x j
    rw [toReal_neg]
    linarith
  · exact (up j).le x hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
