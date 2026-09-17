import CORALean.ContSet.Zonotope.Real.Operations.Recentre

/-!
# A member shifted by the centre is a member of the recentred zonotope

Each states its own `h`, that counts only up to unfolding, so the sum needs a
`show`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sub_centre_mem_recentre {Z : Zonotope α} {y : α} (hy : y ∈ Z.construct) :
    y - Z.c ∈ Z.recentre.construct := by -- --- PROOF ---
  obtain ⟨β, hβ, hy⟩ := hy
  refine ⟨β, hβ, ?_⟩
  rw [hy]
  show Z.c + ∑ j, β j • Z.G j - Z.c = 0 + ∑ j, β j • Z.G j
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
