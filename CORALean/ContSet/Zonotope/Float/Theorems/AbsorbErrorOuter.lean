import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError
import CORALean.ContSet.Zonotope.Float.Theorems.AbsSubMidLeErrorRadius
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.ShiftBracketsMid
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

/-!
# `absorbError` keeps the set it had

Over ℝ an identity — a box is a zonotope about its own midpoint. It is only an
inclusion here because the shifted centre must be stored as a float and the
midpoint need not be one, which is why the box does not become `[0, 0]`.

The witness is `Fin.append β γ`: the old coefficients, then one per coordinate
placing that coordinate's error in its new generator. `coefficient` supplies it,
and the radius rounds up so it always fits.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `absorbError`'s generator count. -/
theorem Zonotope.aux_sum_univ_absorbError {Z : Zonotope 𝕋 n} (f : Fin (Z.h + n) → ℝ) :
    ∑ j : Fin Z.absorbError.h, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd Z.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.absorbError_outer (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ Z.absorbError.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hz'
  refine ⟨fun i => toReal (Z.absorbError.c i)
            + ∑ j, toReal (Z.absorbError.G i j)
                * Fin.append β (fun l => Real.Zonotope.coefficient (toReal (Z.errorRadius l))
                    (e l - (toReal (Z.E.inf l) + toReal (Z.E.sup l)) / 2)) j,
          Zonotope.mem_nominalSet_iff.mpr ⟨_, ?_, fun _ => rfl⟩,
          fun i => toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
            - toReal (Z.shiftDown i), ?_, ?_⟩
  -- the fresh coefficients read the box from its own midpoint outward
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ l
    · simpa using Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (Zonotope.abs_sub_mid_le_errorRadius Z he l))
        (Zonotope.abs_sub_mid_le_errorRadius Z he l)
  · exact Interval.sub_mem_residual (Zonotope.shift_brackets_mid Z)
  · funext i
    simp only [Pi.add_apply]
    rw [Zonotope.aux_sum_univ_absorbError]
    simp only [Zonotope.absorbError, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock, hz i]
    rw [Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (Zonotope.abs_sub_mid_le_errorRadius Z he i)]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
