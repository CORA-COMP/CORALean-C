import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# A paired-difference column brackets its exact value between the two directed roundings
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {h₁ h₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same at the paired-difference column. -/
theorem Zonotope.pairDiff_bracket (g₁ : Fin h₁ → 𝕋) (g₂ : Fin h₂ → 𝕋) (k : Fin h₂) :
    toReal (Zonotope.pairDiff subDown g₁ g₂ k)
        ≤ Real.Zonotope.pairDiff (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
      ∧ Real.Zonotope.pairDiff (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
        ≤ toReal (Zonotope.pairDiff subUp g₁ g₂ k) := by -- --- PROOF ---
  simp only [Zonotope.pairDiff, Real.Zonotope.pairDiff]
  by_cases hk : (k : ℕ) < h₁
  · rw [dif_pos hk, dif_pos hk, dif_pos hk, toReal_half, toReal_half, smul_eq_mul]
    exact ⟨by have := subDown_le_sub (g₁ ⟨k, hk⟩) (g₂ k); linarith,
           by have := sub_le_subUp (g₁ ⟨k, hk⟩) (g₂ k); linarith⟩
  · rw [dif_neg hk, dif_neg hk, dif_neg hk]
    exact ⟨le_refl _, le_refl _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
