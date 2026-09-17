import CORALean.ContSet.Zonotope.Float.Operations.PlusBox
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# `plus` reaches no further than its operands plus `plusBox`

The reverse of `plus_outer`, and what a float step's own accumulated error
needs: `plus`'s generators concatenate exactly, so its nominal part misses
`nominalSet Z₁ + nominalSet Z₂` by exactly the centre's rounding, a single
point; its error box is read back into `plusBox` unchanged. Both operands' own
error boxes are absorbed at `0`, which is where `h₁`, `h₂` are spent — not
because the sum needs them small, but because `plusBox` was built to add
`plus`'s own error box as-is rather than to reprove what rounded it.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the
projection because that is the form the goal has. -/
theorem Zonotope.aux_sum_univ_plus_box {Z₁ Z₂ : Zonotope 𝕋 n} (f : Fin (Z₁.h + Z₂.h) → ℝ) :
    ∑ j : Fin (Z₁.plus Z₂).h, f j
      = ∑ j, f (Fin.castAdd Z₂.h j) + ∑ j, f (Fin.natAdd Z₁.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plus` reaches no further than `Z₁.construct + Z₂.construct`, widened by
`plusBox`, provided both operands already bracket `0` in their own box. -/
theorem Zonotope.plus_subset_add_box (Z₁ Z₂ : Zonotope 𝕋 n)
    (h₁ : (0 : Vec ℝ n) ∈ Z₁.E.construct) (h₂ : (0 : Vec ℝ n) ∈ Z₂.E.construct) :
    (Z₁.plus Z₂).construct ⊆
      Z₁.construct + Z₂.construct + (Zonotope.plusBox Z₁ Z₂).construct := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  obtain ⟨β, hβ, hy₁eq⟩ := Zonotope.mem_nominalSet_iff.mp hy₁
  -- the two halves of `β`, read back onto `Z₁` and `Z₂`'s own generators
  set p₁ : Vec ℝ n := fun i => toReal (Z₁.c i) + ∑ l, toReal (Z₁.G i l) * β (Fin.castAdd Z₂.h l)
    with hp₁def
  set p₂ : Vec ℝ n := fun i => toReal (Z₂.c i) + ∑ l, toReal (Z₂.G i l) * β (Fin.natAdd Z₁.h l)
    with hp₂def
  -- the point `plus`'s stored centre misses the exact sum by
  set d : Vec ℝ n := fun i =>
    toReal (addDown (Z₁.c i) (Z₂.c i)) - toReal (Z₁.c i) - toReal (Z₂.c i) with hddef
  -- each half sits in its own zonotope's construct, its error box absorbed at `0`
  have hp₁ : p₁ ∈ Z₁.construct := by
    have h := Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr
      ⟨fun l => β (Fin.castAdd Z₂.h l), fun l => hβ _, fun _ => rfl⟩) h₁
    rwa [add_zero] at h
  have hp₂ : p₂ ∈ Z₂.construct := by
    have h := Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr
      ⟨fun l => β (Fin.natAdd Z₁.h l), fun l => hβ _, fun _ => rfl⟩) h₂
    rwa [add_zero] at h
  -- `d` and `plus`'s own error box, read back into `plusBox` via the exact `Real` `plus`
  have hbox : d + y₂ ∈ (Zonotope.plusBox Z₁ Z₂).construct := by
    show d + y₂ ∈
      ((Real.Zonotope.ofPoint d).plus ((Z₁.plus Z₂).E.nominal.zonotope)).construct
    rw [← Real.Zonotope.plus_exact]
    exact Set.add_mem_add (Real.Zonotope.mem_ofPoint d) (Real.Interval.zonotope_contains _ hy₂)
  refine ⟨_, Set.add_mem_add hp₁ hp₂, _, hbox, ?_⟩
  funext i
  have hsum := Zonotope.aux_sum_univ_plus_box (Z₁ := Z₁) (Z₂ := Z₂)
    (fun x => toReal (Fin.append (Z₁.G i) (Z₂.G i) x) * β x)
  simp only [Fin.append_left, Fin.append_right] at hsum
  have hy₁i : y₁ i = toReal (addDown (Z₁.c i) (Z₂.c i))
      + (∑ l, toReal (Z₁.G i l) * β (Fin.castAdd Z₂.h l)
         + ∑ l, toReal (Z₂.G i l) * β (Fin.natAdd Z₁.h l)) :=
    (hy₁eq i).trans (congrArg (toReal (addDown (Z₁.c i) (Z₂.c i)) + ·) hsum)
  show p₁ i + p₂ i + (d i + y₂ i) = y₁ i + y₂ i
  rw [hy₁i, hp₁def, hp₂def, hddef]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
