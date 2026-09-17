import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# `plus` keeps the origin in the error box

An invariant the growth bounds in `PlusSubsetAddBox` and the whole
`reachErrorFloat` recursion lean on: if both operands already bracket `0` in
their own box, so does the sum's. `centerResidual` brackets `0` on its own —
`subDown` of two equal arguments is at most `0`, and `subUp` of the two
directed roundings of one addition is at least their gap — and `Interval.plus`
carries the property through, each bound rounding the way that keeps it.

Not a fact about `plus` specifically: any two boxes that bracket `0`, added,
bracket `0`. Stated at `plus` because that is the one call site.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Interval.plus` of two boxes that bracket `0` brackets `0`: each rounded
bound sits on the sound side of the sum of the two exact ones. -/
theorem Zonotope.aux_zero_mem_interval_plus {I J : Interval 𝕋 n}
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

/-- `centerResidual` always brackets `0`: its lower bound is a directed
subtraction of one value from itself, and its upper bound is at least the gap
between the two directed roundings of the same addition. -/
theorem Zonotope.aux_zero_mem_centerResidual (a b : Vec 𝕋 n) :
    (0 : Vec ℝ n) ∈ (Zonotope.centerResidual a b).construct := by -- --- PROOF ---
  intro i
  have hle : toReal (addDown (a i) (b i)) ≤ toReal (addUp (a i) (b i)) :=
    le_trans (addDown_le_add _ _) (add_le_addUp _ _)
  refine ⟨?_, ?_⟩
  · show toReal (subDown (addDown (a i) (b i)) (addDown (a i) (b i))) ≤ (0:ℝ)
    exact le_trans (subDown_le_sub _ _) (by linarith)
  · show (0:ℝ) ≤ toReal (subUp (addUp (a i) (b i)) (addDown (a i) (b i)))
    exact le_trans (by linarith) (sub_le_subUp _ _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plus` keeps `0` in the error box, given both operands already have it. -/
theorem Zonotope.zero_mem_plus_error {Z₁ Z₂ : Zonotope 𝕋 n}
    (h₁ : (0 : Vec ℝ n) ∈ Z₁.E.construct) (h₂ : (0 : Vec ℝ n) ∈ Z₂.E.construct) :
    (0 : Vec ℝ n) ∈ (Z₁.plus Z₂).E.construct :=
  Zonotope.aux_zero_mem_interval_plus (Zonotope.aux_zero_mem_interval_plus h₁ h₂)
    (Zonotope.aux_zero_mem_centerResidual Z₁.c Z₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
