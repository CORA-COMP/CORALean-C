import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# `Zonotope.plus` is exactly the Minkowski sum

The witness is `Fin.append β₁ β₂`: concatenated generators take concatenated
coefficients. `Fin.addCases` and `Fin.sum_univ_add` split the bound and the sum
the same way, and splitting a coefficient vector the other way gives the
converse, so concatenation loses nothing.

No `plus_outer` here: the float `plus` displaces the centre, so it reproves this
against the displaced centre rather than composing with it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the
projection because that is the form the goal has. Matched by `rw`, never
applied: supplying `f` forces its domain to the reduced count. -/
theorem Zonotope.aux_sum_univ_plus {Z₁ Z₂ : Zonotope α} (f : Fin (Z₁.h + Z₂.h) → α) :
    ∑ j : Fin (Z₁.plus Z₂).h, f j
      = ∑ j, f (Fin.castAdd Z₂.h j) + ∑ j, f (Fin.natAdd Z₁.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.plus_exact (Z₁ Z₂ : Zonotope α) :
    Z₁.construct + Z₂.construct = (Z₁.plus Z₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x₁, ⟨β₁, hβ₁, rfl⟩, x₂, ⟨β₂, hβ₂, rfl⟩, rfl⟩
    refine ⟨Fin.append β₁ β₂, Fin.addCases (fun l => by simpa using hβ₁ l)
      (fun l => by simpa using hβ₂ l), ?_⟩
    rw [Zonotope.aux_sum_univ_plus]
    simp only [Zonotope.plus, Fin.append_left, Fin.append_right]
    abel
  -- back: the two halves of `β` are the two zonotopes' own coefficients
  · rintro x ⟨β, hβ, rfl⟩
    refine ⟨Z₁.c + ∑ j, β (Fin.castAdd Z₂.h j) • Z₁.G j,
            ⟨_, fun j => hβ _, rfl⟩,
            Z₂.c + ∑ j, β (Fin.natAdd Z₁.h j) • Z₂.G j,
            ⟨_, fun j => hβ _, rfl⟩, ?_⟩
    rw [Zonotope.aux_sum_univ_plus]
    simp only [Zonotope.plus, Fin.append_left, Fin.append_right]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
