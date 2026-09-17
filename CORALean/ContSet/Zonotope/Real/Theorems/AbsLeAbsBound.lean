import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# A coordinate of a zonotope never leaves `absBound`

Centre plus the generator column sums, coordinatewise, the coefficients being at
most one. What both the real and the constrained interval-matrix products bound
their leftover against.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A coordinate of a zonotope never leaves `absBound`. -/
theorem Zonotope.abs_le_absBound {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n} {β : Vec ℝ Z.h}
    (hβ : ∀ j, |β j| ≤ 1) (hx : ∀ i, x i = Z.c i + ∑ j, Z.G j i * β j) (j : Fin n) :
    |x j| ≤ Z.absBound j := by -- --- PROOF ---
  rw [hx j, Zonotope.absBound]
  refine (abs_add_le _ _).trans ?_
  gcongr
  calc |∑ l, Z.G l j * β l|
      ≤ ∑ l, |Z.G l j * β l|   := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, |Z.G l j| * |β l| := by simp_rw [abs_mul]
    _ ≤ ∑ l, |Z.G l j|         := Finset.sum_le_sum fun l _ => by
        simpa using mul_le_mul_of_nonneg_left (hβ l) (abs_nonneg (Z.G l j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
