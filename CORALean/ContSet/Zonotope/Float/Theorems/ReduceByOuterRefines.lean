import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# `Zonotope.reduceBy` encloses the exact reduction

At one and the same partition the two layers differ in the diagonal block alone:
the kept generators are copied either way, and `radius` rounds the block *up*,
so it covers the exact row sum. `coefficient` rescales by the ratio of the two,
which the unit ball allows because the exact radius is the smaller.

As far as the refinement goes. At the *order* level there is none: `reduce`
picks its partition by a metric computed in `𝕋`, so the layers can keep
different generators, and two reductions of one zonotope are in general
incomparable — boxing a generator loses a correlation between coordinates that
keeping it preserves.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduceBy`'s generator count, stated through the
projection because that is the form the goal has. -/
theorem Zonotope.aux_sum_univ_reduceBy {Z : Zonotope 𝕋 n}
    {part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)} (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (Z.reduceBy part).h, f j = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceBy_outer_refines (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    ((nominal Z).reduceBy part).construct ⊆ nominalSet (Z.reduceBy part) := by -- --- PROOF ---
  intro x hxmem
  obtain ⟨β, hβ, hx⟩ := Real.Zonotope.mem_construct_iff.mp hxmem
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |toReal (Z.G i (part.right l))| :=
    fun i => Finset.sum_nonneg fun l _ => abs_nonneg _
  have hle : ∀ i, (∑ l, |toReal (Z.G i (part.right l))|)
      ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) :=
    fun i => sum_abs_le_radius (d := fun i l => Z.G i (part.right l)) i
  have hbound : ∀ i, |(∑ l, |toReal (Z.G i (part.right l))|) * β (Fin.natAdd q i)|
      ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) := by
    intro i
    rw [abs_mul, abs_of_nonneg (hnonneg i)]
    exact le_trans (mul_le_of_le_one_right (hnonneg i) (hβ _)) (hle i)
  -- the witness: kept coefficients, plus one per coordinate scaled to the rounded radius
  refine Zonotope.mem_nominalSet_iff.mpr ⟨Fin.append (fun l => β (Fin.castAdd n l)) (fun i =>
      Real.Zonotope.coefficient (toReal (radius (fun i l => Z.G i (part.right l)) i))
        ((∑ l, |toReal (Z.G i (part.right l))|) * β (Fin.natAdd q i))), ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ _
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one ((hnonneg i).trans (hle i)) (hbound i)
  · rw [hx i, Real.Zonotope.sum_univ_reduceBy, Zonotope.aux_sum_univ_reduceBy]
    simp only [Real.Zonotope.reduceBy, Zonotope.reduceBy, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock]
    -- the exact block is indexed generator-first, the float one coordinate-first
    rw [Real.Zonotope.sum_diagonal_mul', Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hbound i)]
    -- what is left is the `nominal` projections, which are definitional
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
