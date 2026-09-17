import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# A paired-sum column brackets its exact value between the two directed roundings

Halving is exact, so the directed addition is the only rounding, and a surplus
column is copied and does not round at all.
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

/-- A paired-sum column brackets its exact value between the two directed
roundings: halving is exact, so the directed addition is the only rounding, and
a surplus column is copied and does not round at all. -/
theorem Zonotope.pairSum_bracket (g₁ : Fin h₁ → 𝕋) (g₂ : Fin h₂ → 𝕋) (k : Fin h₁) :
    toReal (Zonotope.pairSum addDown g₁ g₂ k)
        ≤ Real.Zonotope.pairSum (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
      ∧ Real.Zonotope.pairSum (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
        ≤ toReal (Zonotope.pairSum addUp g₁ g₂ k) := by -- --- PROOF ---
  simp only [Zonotope.pairSum, Real.Zonotope.pairSum]
  by_cases hk : (k : ℕ) < h₂
  · rw [dif_pos hk, dif_pos hk, dif_pos hk, toReal_half, toReal_half, smul_eq_mul]
    exact ⟨by have := addDown_le_add (g₁ k) (g₂ ⟨k, hk⟩); linarith,
           by have := add_le_addUp (g₁ k) (g₂ ⟨k, hk⟩); linarith⟩
  · rw [dif_neg hk, dif_neg hk, dif_neg hk]
    exact ⟨le_refl _, le_refl _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
