import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# `mtimes` reaches no further than the image of its operand plus `mtimesBox`

The reverse of `mtimes_outer`. `mtimes` keeps `Z`'s own generator count, one
rounded value per generator plus one for the centre, so the same coefficients
`Z`'s point used reproduce the exact image up to exactly `mtimesBox`'s
generators — the same regrouping `mtimes_outer`'s own proof does, run in the
other direction. `Z`'s own error box is absorbed at `0`, spent the same way
`plus_subset_add_box` spends it.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image, regrouped so the centre and each generator appear once —
`Zonotope.aux_mulVec_nominal` in `MtimesOuter`, restated here for this file's
own use. -/
theorem Zonotope.aux_mulVec_nominal_box (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) (β : Vec ℝ Z.h)
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mtimes` reaches no further than the image of `Z.construct`, widened by
`mtimesBox`, provided `Z` already brackets `0` in its own box. -/
theorem Zonotope.mtimes_subset_add_box (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n)
    (h : (0 : Vec ℝ n) ∈ Z.E.construct) :
    (Zonotope.mtimes M Z).construct ⊆
      (toRealMat M *ᵥ ·) '' Z.construct
        + (Zonotope.mtimesBox M Z).construct := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  obtain ⟨β, hβ, hy₁eq⟩ := Zonotope.mem_nominalSet_iff.mp hy₁
  -- `Z`'s own point, at the coefficients `mtimes`'s stored generators used
  set x : Vec ℝ n := fun k => toReal (Z.c k) + ∑ l, toReal (Z.G k l) * β l with hxdefeq
  have hxmem : (toRealMat M *ᵥ x) ∈ (toRealMat M *ᵥ ·) '' Z.construct := by
    refine ⟨x, ?_, rfl⟩
    have hh : x + (0 : Vec ℝ n) ∈ nominalSet Z + Z.E.construct :=
      Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩) h
    rwa [add_zero] at hh
  -- the centre and each generator's rounding gap, at the same coefficients
  set g : Vec ℝ m := fun i => (toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (toReal (matMulDown M Z.G i j) - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j
    with hgdefeq
  -- `g` and `mtimes`'s own error box, read back into `mtimesBox`
  have hgmem : g + y₂ ∈ (Zonotope.mtimesBox M Z).construct := by
    show g + y₂ ∈
      ((⟨Z.h, fun i => toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k),
          fun j i => toReal (matMulDown M Z.G i j)
            - ∑ k, toReal (M i k) * toReal (Z.G k j)⟩ : Real.Zonotope (Vec ℝ m)).plus
        ((Zonotope.mtimes M Z).E.nominal.zonotope)).construct
    rw [← Real.Zonotope.plus_exact]
    refine Set.add_mem_add ?_ (Real.Interval.zonotope_contains _ hy₂)
    exact Real.Zonotope.mem_construct_iff.mpr ⟨β, hβ, fun i => rfl⟩
  refine ⟨_, hxmem, _, hgmem, ?_⟩
  funext i
  -- the exact image at `x`, regrouped so the centre and each generator appear once
  have himg : (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j :=
    Zonotope.aux_mulVec_nominal_box M Z β (fun k => by rw [hxdefeq]) i
  have hy₁i : y₁ i = toReal (mulVecDown M Z.c i) + ∑ j, toReal (matMulDown M Z.G i j) * β j :=
    hy₁eq i
  show (toRealMat M *ᵥ x) i + (g i + y₂ i) = y₁ i + y₂ i
  have hgi : g i = (toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (toReal (matMulDown M Z.G i j) - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
    rw [hgdefeq]
  rw [himg, hgi, hy₁i]
  have hsplit : ∑ j, (toReal (matMulDown M Z.G i j)
      - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j
      = ∑ j, toReal (matMulDown M Z.G i j) * β j
        - ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
