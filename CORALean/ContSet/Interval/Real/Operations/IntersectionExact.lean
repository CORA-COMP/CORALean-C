import CORALean.ContSet.Interval.Real.Operations.Intersection

/-!
# `Interval.intersection` is exact

Intersecting two boxes, coordinatewise and exactly: a point is in both when
each of its coordinates clears both lower bounds and stays under both upper
ones.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.intersection_exact (I₁ I₂ : Interval (Vec ℝ n)) :
    (I₁.intersection I₂).construct = I₁.construct ∩ I₂.construct := by -- --- PROOF ---
  ext x
  constructor
  · intro h
    refine ⟨fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
    · exact (max_le_iff.mp (h j).1).1
    · exact (le_min_iff.mp (h j).2).1
    · exact (max_le_iff.mp (h j).1).2
    · exact (le_min_iff.mp (h j).2).2
  · rintro ⟨h₁, h₂⟩ j
    exact ⟨max_le (h₁ j).1 (h₂ j).1, le_min (h₁ j).2 (h₂ j).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
