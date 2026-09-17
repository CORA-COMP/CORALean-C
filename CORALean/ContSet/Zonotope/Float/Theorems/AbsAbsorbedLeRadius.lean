import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy

/-!
# What the generators `reduceBy` absorbs contribute, so what the block must cover
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the absorbed generators contribute, so what the block must cover. -/
theorem Zonotope.abs_absorbed_le_radius (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) {β : Vec ℝ Z.h}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ l, toReal (Z.G i (part.right l)) * β (part.right l)|
      ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) := by
  exact abs_sum_le_radius (d := fun i l => Z.G i (part.right l))
    (fun _ _ => le_refl _) (fun l => hβ (part.right l)) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
