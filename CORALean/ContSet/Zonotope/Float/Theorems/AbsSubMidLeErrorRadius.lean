import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError

/-!
# The new generators of `absorbError` reach every point the box did
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

/-- The new generators reach every point the box did. -/
theorem Zonotope.abs_sub_mid_le_errorRadius (Z : Zonotope 𝕋 n) {e : Vec ℝ n}
    (he : e ∈ Z.E.construct) (i : Fin n) :
    |e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2|
      ≤ toReal (Z.errorRadius i) := by -- --- PROOF ---
  have hwidth := sub_le_subUp (Z.E.sup i) (Z.E.inf i)
  -- ascribed, so `toRealVec _ i` is unfolded to the atom linarith shares with hwidth
  have hlo : toReal (Z.E.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (Z.E.sup i) := (he i).2
  simp only [Zonotope.errorRadius, toReal_half]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
