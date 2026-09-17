import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Zonotope.Float.Operations.ReduceAndAbsorb
import CORALean.ContSet.Zonotope.Float.Theorems.AbsAbsorbedLeRadius
import CORALean.ContSet.Zonotope.Float.Theorems.AbsSubMidLeErrorRadius
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.ShiftBracketsMid
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

/-!
# `reduceAndAbsorbBy` keeps the set it had

The two arguments meet in one coefficient. The absorbed generators contribute at
most `radius`, the box at most `errorRadius`, and the merged block has radius at
least their sum, so one coefficient places both at once.

Neither `mono_subset` nor `map_subset` applies: they send nominal to nominal and
box to box, whereas this moves content *out* of the box into the nominal part.
What is left in the box is the rounded centre shift, as in `absorbError`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The merged block covers the absorbed generators and the box together. -/
theorem Zonotope.aux_abs_merged_le_radius (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) {β : Vec ℝ Z.h} {e : Vec ℝ n}
    (hβ : ∀ j, |β j| ≤ 1) (he : e ∈ Z.E.construct) (i : Fin n) :
    |(∑ l, toReal (Z.G i (part.right l)) * β (part.right l))
        + (e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2)|
      ≤ toReal (addUp (radius (fun i l => Z.G i (part.right l)) i) (Z.errorRadius i)) := by
  have hgen := Zonotope.abs_absorbed_le_radius Z part hβ i
  have hbox := Zonotope.abs_sub_mid_le_errorRadius Z he i
  have hsum := add_le_addUp (radius (fun i l => Z.G i (part.right l)) i) (Z.errorRadius i)
  exact le_trans (abs_add_le _ _) (by linarith)

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduceAndAbsorbBy`'s generator count. -/
theorem Zonotope.aux_sum_univ_reduceAndAbsorbBy {Z : Zonotope 𝕋 n}
    {part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)} (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (Z.reduceAndAbsorbBy part).h, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceAndAbsorbBy_outer (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    Z.construct ⊆ (Z.reduceAndAbsorbBy part).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hz'
  have hmerged := Zonotope.aux_abs_merged_le_radius Z part hβ he
  have hnonneg : ∀ i, (0:ℝ) ≤
      toReal (addUp (radius (fun i l => Z.G i (part.right l)) i) (Z.errorRadius i)) :=
    fun i => (abs_nonneg _).trans (hmerged i)
  -- the witness: kept coefficients, plus one per coordinate for the merged box
  refine ⟨fun i => toReal ((Z.reduceAndAbsorbBy part).c i)
            + ∑ j, toReal ((Z.reduceAndAbsorbBy part).G i j)
                * Fin.append (fun l => β (part.left l)) (fun i =>
                    Real.Zonotope.coefficient
                      (toReal (addUp (radius (fun i l => Z.G i (part.right l)) i)
                        (Z.errorRadius i)))
                      ((∑ l, toReal (Z.G i (part.right l)) * β (part.right l))
                        + (e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2))) j,
          Zonotope.mem_nominalSet_iff.mpr ⟨_, ?_, fun _ => rfl⟩,
          fun i => toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
            - toReal (Z.shiftDown i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one (hnonneg i) (hmerged i)
  · exact Interval.sub_mem_residual (Zonotope.shift_brackets_mid Z)
  -- the value spelled out, both blocks and the recentring shift together
  · funext i
    show toReal ((Z.reduceAndAbsorbBy part).c i)
        + ∑ j, toReal ((Z.reduceAndAbsorbBy part).G i j)
            * Fin.append (fun l => β (part.left l)) (fun i =>
                Real.Zonotope.coefficient
                  (toReal (addUp (radius (fun i l => Z.G i (part.right l)) i)
                    (Z.errorRadius i)))
                  ((∑ l, toReal (Z.G i (part.right l)) * β (part.right l))
                    + (e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2))) j
        + (toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
            - toReal (Z.shiftDown i))
      = z i + e i
    -- the dropped generators and the recentred box come back out of the diagonal block
    rw [hz i, part.sum_split₂ fun j => toReal (Z.G i j) * β j,
      Zonotope.aux_sum_univ_reduceAndAbsorbBy]
    simp only [Zonotope.reduceAndAbsorbBy, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock]
    rw [Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hmerged i)]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
