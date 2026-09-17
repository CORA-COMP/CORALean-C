import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

/-!
# `mtimes` keeps the origin in the error box

The `mtimes` counterpart of `ZeroMemPlusError`, needed by `MtimesSubsetAddBox`
and by `reachErrorFloat`'s own recursion. `Interval.mtimes` keeps `0` because
`0` sits between every row's `inf` and `sup`, so each term's rounded `min`/`max`
is charged against a product that is itself at most/at least `0`, whichever
sign the matrix entry has; `mtimesResidual` keeps it for the same structural
reason `centerResidual` does, `generatorError` being symmetric outright.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_zero_mem_interval_plus' {I J : Interval 𝕋 n}
    (hI : (0 : Vec ℝ n) ∈ I.construct) (hJ : (0 : Vec ℝ n) ∈ J.construct) :
    (0 : Vec ℝ n) ∈ (I.plus J).construct := by -- --- PROOF ---
  intro i
  have hI1 : toReal (I.inf i) ≤ (0:ℝ) := (hI i).1
  have hI2 : (0:ℝ) ≤ toReal (I.sup i) := (hI i).2
  have hJ1 : toReal (J.inf i) ≤ (0:ℝ) := (hJ i).1
  have hJ2 : (0:ℝ) ≤ toReal (J.sup i) := (hJ i).2
  refine ⟨?_, ?_⟩
  · show toReal (addDown (I.inf i) (J.inf i)) ≤ (0:ℝ)
    exact le_trans (addDown_le_add _ _) (by linarith)
  · show (0:ℝ) ≤ toReal (addUp (I.sup i) (J.sup i))
    exact le_trans (by linarith) (add_le_addUp _ _)

/-- `Interval.mtimes` keeps `0`: each row's rounded bound is charged against a
term whose real value already sits on the sound side of `0`. -/
theorem Zonotope.aux_zero_mem_interval_mtimes {M : Mat 𝕋 m n} {I : Interval 𝕋 n}
    (hI : (0 : Vec ℝ n) ∈ I.construct) :
    (0 : Vec ℝ m) ∈ (Interval.mtimes M I).construct := by -- --- PROOF ---
  intro i
  have hIk1 : ∀ k, toReal (I.inf k) ≤ (0:ℝ) := fun k => (hI k).1
  have hIk2 : ∀ k, (0:ℝ) ≤ toReal (I.sup k) := fun k => (hI k).2
  -- each term's rounded `min` sits under a real product on the sound side of `0`
  have hterm_lo : ∀ k, toReal (minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k)))
      ≤ 0 := by
    intro k
    rw [toReal_minimum]
    rcases le_total 0 (toReal (M i k)) with hs | hs
    · exact le_trans (min_le_left _ _) (le_trans (mulDown_le_mul _ _)
        (mul_nonpos_of_nonneg_of_nonpos hs (hIk1 k)))
    · exact le_trans (min_le_right _ _) (le_trans (mulDown_le_mul _ _)
        (mul_nonpos_of_nonpos_of_nonneg hs (hIk2 k)))
  -- the reflection: the rounded `max` sits over a product on the other sound side
  have hterm_hi : ∀ k, (0:ℝ) ≤
      toReal (maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))) := by
    intro k
    rw [toReal_maximum]
    rcases le_total 0 (toReal (M i k)) with hs | hs
    · exact (le_trans (mul_nonneg hs (hIk2 k)) (mul_le_mulUp _ _)).trans (le_max_right _ _)
    · exact (le_trans (mul_nonneg_of_nonpos_of_nonpos hs (hIk1 k)) (mul_le_mulUp _ _)).trans
        (le_max_left _ _)
  -- summing nonpositive (resp. nonnegative) terms keeps the sign
  refine ⟨?_, ?_⟩
  · show toReal (sumDown fun k => minimum (mulDown (M i k) (I.inf k))
      (mulDown (M i k) (I.sup k))) ≤ (0:ℝ)
    exact le_trans (sumDown_le_sum _) (Finset.sum_nonpos fun k _ => hterm_lo k)
  · show (0:ℝ) ≤ toReal (sumUp fun k => maximum (mulUp (M i k) (I.inf k))
      (mulUp (M i k) (I.sup k)))
    exact le_trans (Finset.sum_nonneg fun k _ => hterm_hi k) (sum_le_sumUp _)

/-- The shape `centerResidual` and `mtimesResidual`'s centre piece share: a
value stored as its own lower bound always brackets `0`. -/
theorem Zonotope.aux_zero_mem_residual_self {lo hi : Vec 𝕋 n}
    (hle : ∀ i, toReal (lo i) ≤ toReal (hi i)) :
    (0 : Vec ℝ n) ∈ (Interval.residual lo hi lo).construct := by -- --- PROOF ---
  intro i
  refine ⟨?_, ?_⟩
  · show toReal (subDown (lo i) (lo i)) ≤ (0:ℝ)
    exact le_trans (subDown_le_sub _ _) (by linarith)
  · show (0:ℝ) ≤ toReal (subUp (hi i) (lo i))
    exact le_trans (by linarith [hle i]) (sub_le_subUp _ _)

/-- Symmetric outright: a magnitude bound brackets `0` in either direction. -/
theorem Zonotope.aux_zero_mem_generatorError (G : Mat 𝕋 n h) :
    (0 : Vec ℝ n) ∈ (Zonotope.generatorError G).construct := by -- --- PROOF ---
  intro i
  have hnonneg : (0:ℝ) ≤ toReal (radius G i) :=
    le_trans (Finset.sum_nonneg fun j _ => (toReal_absolute (G i j)) ▸ abs_nonneg _)
      (sum_le_sumUp _)
  refine ⟨?_, ?_⟩
  · show toReal (neg (radius G i)) ≤ (0:ℝ)
    rw [toReal_neg]; linarith
  · exact hnonneg

theorem Zonotope.aux_zero_mem_mtimesResidual (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) :
    (0 : Vec ℝ m) ∈ (Zonotope.mtimesResidual M Z).construct :=
  Zonotope.aux_zero_mem_interval_plus'
    (Zonotope.aux_zero_mem_residual_self
      (fun i => le_trans (dotDown_le (M i) Z.c) (le_dotUp (M i) Z.c)))
    (Zonotope.aux_zero_mem_generatorError (matMulDiff M Z.G))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mtimes` keeps `0` in the error box, given the operand already has it. -/
theorem Zonotope.zero_mem_mtimes_error {M : Mat 𝕋 m n} {Z : Zonotope 𝕋 n}
    (h : (0 : Vec ℝ n) ∈ Z.E.construct) : (0 : Vec ℝ m) ∈ (Zonotope.mtimes M Z).E.construct :=
  Zonotope.aux_zero_mem_interval_plus' (Zonotope.aux_zero_mem_interval_mtimes h)
    (Zonotope.aux_zero_mem_mtimesResidual M Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
