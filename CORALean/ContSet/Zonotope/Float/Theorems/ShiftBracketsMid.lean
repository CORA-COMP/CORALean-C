import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError

/-!
# The stored shifted centres of `absorbError` bracket the exact one
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stored centres bracket the exact shifted one, which is what is left. -/
theorem Zonotope.shift_brackets_mid (Z : Zonotope 𝕋 n) (i : Fin n) :
    toReal (Z.shiftDown i) ≤ toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2 ∧
      toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
        ≤ toReal (Z.shiftUp i) := by -- --- PROOF ---
  constructor
  · have h1 := addDown_le_add (Z.c i) (half (addDown (Z.E.inf i) (Z.E.sup i)))
    have h2 := addDown_le_add (Z.E.inf i) (Z.E.sup i)
    rw [toReal_half] at h1
    simpa only [Zonotope.shiftDown] using by linarith
  · have h1 := add_le_addUp (Z.c i) (half (addUp (Z.E.inf i) (Z.E.sup i)))
    have h2 := add_le_addUp (Z.E.inf i) (Z.E.sup i)
    rw [toReal_half] at h1
    simpa only [Zonotope.shiftUp] using by linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
