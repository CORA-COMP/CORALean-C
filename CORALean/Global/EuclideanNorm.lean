import CORALean.Global.Tensor

/-!
# The Euclidean norm of a vector

`Vec ℝ n` is `Fin n → ℝ`, and Mathlib's `Pi` instance gives that type the
*supremum* norm, so `‖·‖` on a vector is not the norm an ellipsoid is described
by. `‖·‖₂` is spelt out here rather than borrowed from
`EuclideanSpace ℝ (Fin n)`, which is a `PiLp` type synonym every statement and
every set would have to be transported across.

Only what an ellipsoid needs: Cauchy–Schwarz, homogeneity, the triangle
inequality, and that the closed unit ball is convex and compact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}

noncomputable def norm₂ (x : Vec ℝ n) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Deliberately not `‖·‖`, which at `Vec ℝ n` is the supremum norm. -/
scoped notation "‖" x "‖₂" => norm₂ x


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_sum_sq_nonneg (x : Vec ℝ n) : 0 ≤ ∑ i, x i ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm₂_nonneg (x : Vec ℝ n) : 0 ≤ ‖x‖₂ := Real.sqrt_nonneg _

theorem norm₂_sq (x : Vec ℝ n) : ‖x‖₂ ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (aux_sum_sq_nonneg x)

theorem dotProduct_self (x : Vec ℝ n) : x ⬝ᵥ x = ‖x‖₂ ^ 2 := by
  rw [norm₂_sq]
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

theorem norm₂_zero : ‖(0 : Vec ℝ n)‖₂ = 0 := by
  have h : ∑ i, (0 : Vec ℝ n) i ^ 2 = 0 := by
    exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply]; ring
  rw [norm₂, h, Real.sqrt_zero]

theorem norm₂_smul (r : ℝ) (x : Vec ℝ n) : ‖r • x‖₂ = |r| * ‖x‖₂ := by
  have h : ∑ i, (r • x) i ^ 2 = r ^ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [norm₂, norm₂, h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

/-- Cauchy–Schwarz in magnitude. The two-sided form is what a box conversion
needs, a coordinate reaching as far in one direction as in the other. -/
theorem abs_dotProduct_le_norm₂_mul_norm₂ (x y : Vec ℝ n) :
    |x ⬝ᵥ y| ≤ ‖x‖₂ * ‖y‖₂ := by -- --- PROOF ---
  have hcs : (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * ∑ i, y i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  calc |x ⬝ᵥ y| = Real.sqrt ((∑ i, x i * y i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, x i ^ 2) * ∑ i, y i ^ 2) := Real.sqrt_le_sqrt hcs
    _ = ‖x‖₂ * ‖y‖₂ := Real.sqrt_mul (aux_sum_sq_nonneg x) _

/-- Cauchy–Schwarz, which is the whole of the ellipsoid's support function. -/
theorem dotProduct_le_norm₂_mul_norm₂ (x y : Vec ℝ n) : x ⬝ᵥ y ≤ ‖x‖₂ * ‖y‖₂ :=
  le_trans (le_abs_self _) (abs_dotProduct_le_norm₂_mul_norm₂ x y)

theorem norm₂_add_le (x y : Vec ℝ n) : ‖x + y‖₂ ≤ ‖x‖₂ + ‖y‖₂ := by -- --- PROOF ---
  have hexp : ∑ i, (x + y) i ^ 2 = (∑ i, x i ^ 2) + 2 * (x ⬝ᵥ y) + ∑ i, y i ^ 2 := by
    rw [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply]; ring
  have hle : ∑ i, (x + y) i ^ 2 ≤ (‖x‖₂ + ‖y‖₂) ^ 2 := by
    rw [hexp, add_sq, norm₂_sq, norm₂_sq]
    linarith [dotProduct_le_norm₂_mul_norm₂ x y]
  calc ‖x + y‖₂ = Real.sqrt (∑ i, (x + y) i ^ 2) := rfl
    _ ≤ Real.sqrt ((‖x‖₂ + ‖y‖₂) ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖x‖₂ + ‖y‖₂ := Real.sqrt_sq (add_nonneg (norm₂_nonneg x) (norm₂_nonneg y))

/-- One coordinate never exceeds the whole, which is what bounds the unit ball
in the supremum norm the ambient type actually carries. -/
theorem abs_le_norm₂ (x : Vec ℝ n) (i : Fin n) : |x i| ≤ ‖x‖₂ := by -- --- PROOF ---
  have h : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, x j ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖x‖₂ := rfl

/-- The closed unit ball, which is what an ellipsoid is the affine image of. -/
def unitBall₂ (n : ℕ) : Set (Vec ℝ n) := {x | ‖x‖₂ ≤ 1}

theorem mem_unitBall₂ {x : Vec ℝ n} : x ∈ unitBall₂ n ↔ ‖x‖₂ ≤ 1 := Iff.rfl

theorem zero_mem_unitBall₂ : (0 : Vec ℝ n) ∈ unitBall₂ n := by
  rw [mem_unitBall₂, norm₂_zero]
  exact zero_le_one

theorem continuous_norm₂ : Continuous (norm₂ : Vec ℝ n → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)

theorem convex_unitBall₂ : Convex ℝ (unitBall₂ n) := by -- --- PROOF ---
  intro x hx y hy a b ha hb hab
  have htri := norm₂_add_le (a • x) (b • y)
  rw [norm₂_smul, norm₂_smul, abs_of_nonneg ha, abs_of_nonneg hb] at htri
  show ‖a • x + b • y‖₂ ≤ 1
  calc ‖a • x + b • y‖₂ ≤ a * ‖x‖₂ + b * ‖y‖₂ := htri
    _ ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by rw [mul_one, mul_one, hab]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Closed because the norm is continuous, and inside the supremum-norm unit
ball because no coordinate exceeds the whole. -/
theorem isCompact_unitBall₂ : IsCompact (unitBall₂ n) := by -- --- PROOF ---
  show IsCompact {x : Vec ℝ n | ‖x‖₂ ≤ 1}
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec ℝ n) 1)
    (isClosed_le continuous_norm₂ continuous_const) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  exact fun i => by rw [Real.norm_eq_abs]; exact le_trans (abs_le_norm₂ x i) hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
