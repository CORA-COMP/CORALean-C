import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.LinProg.API

/-!
# A zonotope answers a direction without a linear program

Each generator contributes independently: coefficient `βⱼ ∈ [-1,1]` reaches at
most `|c (Gⱼ)|` in direction `c`, so the sum peaks at `c (Z.c) + Σⱼ |c (Gⱼ)|`.
No solver and no dual certificate — and the value is attained, which
`Theorems.SupportBoundAttained` states.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No linear program: each generator's coefficient reaches at most
`|c (Z.G j)|`, independently of the others, so the sum bounds the whole. -/
def Zonotope.supportBound (Z : Zonotope α) (c : α →ₗ[ℝ] ℝ) :
    SupportBound Z.construct c where
  val := c Z.c + ∑ j, |c (Z.G j)|
  le := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [map_add]
    refine add_le_add le_rfl ?_
    calc c (∑ j, β j • Z.G j) = ∑ j, β j * c (Z.G j) := by
          rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
      _ ≤ ∑ j, |β j * c (Z.G j)| := Finset.sum_le_sum fun j _ => le_abs_self _
      _ = ∑ j, |β j| * |c (Z.G j)| := by simp_rw [abs_mul]
      _ ≤ ∑ j, |c (Z.G j)| := Finset.sum_le_sum fun j _ => by
          simpa using mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg (c (Z.G j)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
