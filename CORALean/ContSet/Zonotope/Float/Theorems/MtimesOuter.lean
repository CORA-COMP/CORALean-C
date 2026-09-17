import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.MtimesResidual
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# `Zonotope.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box. The
box is easy: the old one travels through the map as a box, by
`Interval.mtimes_outer`, and the spill is added on.

The nominal obligation is where the float layer pays for arithmetic rather than
bookkeeping. Centre and generators are wrong in different ways: the centre by a
fixed vector, which `residual` holds, the generators by an entrywise amount the
coefficients then scale, which `generatorError` sums.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image, regrouped so the centre and each generator appear once. -/
theorem Zonotope.aux_mulVec_nominal (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) (β : Vec ℝ Z.h)
    {x : Vec ℝ n} (hx : ∀ k, x k = toReal (Z.c k) + ∑ j, toReal (Z.G k j) * β j) (i : Fin m) :
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (Z.c k)
              + ∑ j, toReal (M i k) * toReal (Z.G k j) * β j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
    _ = (∑ k, toReal (M i k) * toReal (Z.c k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (Z.G k j) * β j := Finset.sum_add_distrib
    _ = (∑ k, toReal (M i k) * toReal (Z.c k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm)

-- the image's nominal part, with the generator rounding charged to a box
theorem Zonotope.aux_mtimes_nominal (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' nominalSet Z ⊆
      nominalSet (Zonotope.mtimes M Z)
        + (Zonotope.mtimesResidual M Z).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx', rfl⟩
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx'
  -- the generators are wrong by this much, entrywise
  have hgen : ∀ i j, |(∑ k, toReal (M i k) * toReal (Z.G k j))
      - toReal (matMulDown M Z.G i j)| ≤ toReal (matMulDiff M Z.G i j) := by
    intro i j
    -- ascribed, so these are about `matMul*` rather than the `dot*` they unfold to
    have hlo : toReal (matMulDown M Z.G i j) ≤ ∑ k, toReal (M i k) * toReal (Z.G k j) :=
      dotDown_le (M i) (fun k => Z.G k j)
    have hhi : ∑ k, toReal (M i k) * toReal (Z.G k j) ≤ toReal (matMulUp M Z.G i j) :=
      le_dotUp (M i) (fun k => Z.G k j)
    have hgap := sub_le_subUp (matMulUp M Z.G i j) (matMulDown M Z.G i j)
    rw [abs_le]
    exact ⟨by simp only [matMulDiff]; linarith, by simp only [matMulDiff]; linarith⟩
  refine ⟨fun i => toReal ((Zonotope.mtimes M Z).c i)
            + ∑ j : Fin Z.h, toReal ((Zonotope.mtimes M Z).G i j) * β j,
          Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩,
          _, Interval.plus_outer _ _
            ⟨_, Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) Z.c, le_dotUp (M i) Z.c⟩),
             _, Zonotope.mem_generatorError hgen hβ, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hsum : (∑ j, toReal (matMulDown M Z.G i j) * β j)
      + (∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)
          - toReal (matMulDown M Z.G i j)) * β j)
      = ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  show toReal ((Zonotope.mtimes M Z).c i)
        + ∑ j : Fin Z.h, toReal ((Zonotope.mtimes M Z).G i j) * β j
      + ((∑ k, toReal (M i k) * toReal (Z.c k) - toReal (mulVecDown M Z.c i))
        + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)
            - toReal (matMulDown M Z.G i j)) * β j)
    = (toRealMat M *ᵥ x) i
  rw [Zonotope.aux_mulVec_nominal M Z β hx i]
  simp only [Zonotope.mtimes]
  linarith [hsum]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem Zonotope.aux_mtimes_error (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (error Z).construct + (Zonotope.mtimesResidual M Z).construct ⊆
      (error (Zonotope.mtimes M Z)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M Z.E))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimes_outer (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' Z.construct ⊆ (Zonotope.mtimes M Z).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (Zonotope.aux_mtimes_nominal M Z) (Zonotope.aux_mtimes_error M Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
