import CORALean.ContSet.HPolytope.Real.Operations.Intersection

/-!
# Membership in a concatenated constraint list

Both constraint lists have to hold, which is what concatenating them says.
`Fin.addCases` splits the quantifier the same way `Fin.append` splits the list.

Stated as an `iff` on points rather than as the set equality it implies, because
that is the form its users need: a constrained zonotope reads its coefficient
polytope this way, and so does the float halfspace description.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_intersection_iff {P₁ P₂ : HPolytope α} {x : α} :
    x ∈ (P₁.intersection P₂).construct ↔ x ∈ P₁.construct ∧ x ∈ P₂.construct := by -- --- PROOF ---
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨fun i => ?_, fun i => ?_⟩⟩
    · have h := hle (Fin.castAdd P₂.m i)
      simp only [HPolytope.intersection, Fin.append_left] at h
      exact h
    · have h := heq (Fin.castAdd P₂.me i)
      simp only [HPolytope.intersection, Fin.append_left] at h
      exact h
    · have h := hle (Fin.natAdd P₁.m i)
      simp only [HPolytope.intersection, Fin.append_right] at h
      exact h
    · have h := heq (Fin.natAdd P₁.me i)
      simp only [HPolytope.intersection, Fin.append_right] at h
      exact h
  -- back: the two memberships are the two halves of one row list
  · rintro ⟨⟨h₁, he₁⟩, h₂, he₂⟩
    constructor
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.intersection, Fin.append_left]; exact h₁ i
      · simp only [HPolytope.intersection, Fin.append_right]; exact h₂ i
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.intersection, Fin.append_left]; exact he₁ i
      · simp only [HPolytope.intersection, Fin.append_right]; exact he₂ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
