import CORALean.Global.Float.FloatOps
import CORALean.Global.Scalar

/-!
# Sound floating-point arithmetic

What the layer assumes of its scalar: a real interpretation `toReal`,
`FloatOps` rounding in the direction its name claims, and `le` agreeing with
`toReal` in one direction only. No format is fixed, so the proofs hold for
binary64, for any other precision, and for ℝ itself.

Not IEEE 754 — rounding *to nearest* bounds nothing in a stated direction. How
the direction is achieved is left open: a hardware rounding mode and nearest
plus one ulp outward both discharge these obligations.

`toReal` is total into ℝ, so no instance has NaN or an infinity. Overflow is
assumed away rather than modelled, and an implementation owes a range argument;
that is the one gap between these axioms and a machine.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps


-- ========================================  MAIN TYPE  ========================================= --

class SoundFloatArithmetic (𝕋 : Type) [FloatOps 𝕋] where
  toReal : 𝕋 → ℝ
  toReal_neg (a : 𝕋) : toReal (neg a) = -toReal a
  toReal_zero : toReal (zero : 𝕋) = 0
  toReal_one : toReal (one : 𝕋) = 1
  add_le_addUp (a b : 𝕋) : toReal a + toReal b ≤ toReal (addUp a b)
  addDown_le_add (a b : 𝕋) : toReal (addDown a b) ≤ toReal a + toReal b
  mul_le_mulUp (a b : 𝕋) : toReal a * toReal b ≤ toReal (mulUp a b)
  mulDown_le_mul (a b : 𝕋) : toReal (mulDown a b) ≤ toReal a * toReal b
  /-- The one partial guarantee: a divisor of zero bounds nothing, and a
  negative one is the caller's own negation away, `neg` being exact. -/
  div_le_divUp (a b : 𝕋) (hb : 0 < toReal b) : toReal a / toReal b ≤ toReal (divUp a b)
  divDown_le_div (a b : 𝕋) (hb : 0 < toReal b) : toReal (divDown a b) ≤ toReal a / toReal b
  toReal_minimum (a b : 𝕋) : toReal (minimum a b) = min (toReal a) (toReal b)
  toReal_maximum (a b : 𝕋) : toReal (maximum a b) = max (toReal a) (toReal b)
  /-- One direction only, see the module docstring for why. -/
  toReal_le_of_le {a b : 𝕋} (h : le a b = true) : toReal a ≤ toReal b
  toReal_half (a : 𝕋) : toReal (half a) = toReal a / 2

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m h : ℕ}

/-! ## Reading arrays -/

def toRealVec (v : Vec 𝕋 n) : Vec ℝ n := fun i => toReal (v i)
def toRealMat (M : Mat 𝕋 m n) : Mat ℝ m n := fun i j => toReal (M i j)

/-- What the exact layer needs of the scalar, and all it needs. -/
instance : Scalar 𝕋 where
  toRealMat M := CORALean.Float.toRealMat M
  toRealVec v := CORALean.Float.toRealVec v

/-! ## What the derived operations inherit -/

theorem toReal_absolute (a : 𝕋) : toReal (absolute a) = |toReal a| := by
  rw [absolute, toReal_maximum, toReal_neg]
  exact (abs_eq_max_neg).symm

/-- Read as reals it is `Matrix.diagonal`, so the exact layer's lemmas apply. -/
theorem toReal_diagonalBlock (v : Vec 𝕋 n) (i l : Fin n) :
    toReal (diagonalBlock v i l) = Matrix.diagonal (toRealVec v) i l := by
  by_cases hil : i = l
  · rw [diagonalBlock, if_pos hil, hil, Matrix.diagonal_apply_eq]
    rfl
  · rw [diagonalBlock, if_neg hil, Matrix.diagonal_apply_ne _ hil, toReal_zero]

theorem sub_le_subUp (a b : 𝕋) : toReal a - toReal b ≤ toReal (subUp a b) := by
  rw [sub_eq_add_neg, ← toReal_neg b, subUp]
  exact add_le_addUp a (neg b)

theorem subDown_le_sub (a b : 𝕋) : toReal (subDown a b) ≤ toReal a - toReal b := by
  rw [sub_eq_add_neg, ← toReal_neg b, subDown]
  exact addDown_le_add a (neg b)

/-- An underestimated positive denominator gives an overestimated reciprocal,
and the rounding only grows it further. -/
theorem one_div_le_divUp {d : 𝕋} {y : ℝ} (h1 : 1 ≤ toReal d) (h2 : toReal d ≤ y) :
    1 / y ≤ toReal (divUp one d) := by
  have hd : (0:ℝ) < toReal d := lt_of_lt_of_le zero_lt_one h1
  have hdiv := div_le_divUp one d hd
  rw [toReal_one] at hdiv
  exact le_trans (one_div_le_one_div_of_le hd h2) hdiv

/-- `maximumOver` bounds every entry, which is what lets one box cover a whole
list of roundings. -/
theorem le_maximumOver : ∀ {k : ℕ} (f : Fin k → 𝕋) (l : Fin k),
    toReal (f l) ≤ toReal (maximumOver f) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ l => absurd l.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    intro f l
    rw [maximumOver, toReal_maximum]
    refine Fin.cases ?_ (fun l' => ?_) l
    · exact le_max_left _ _
    · exact le_trans (ih (fun i => f i.succ) l') (le_max_right _ _)

/-- And `minimumOver` is under every entry, the reflection of the same fold. -/
theorem minimumOver_le {k : ℕ} (f : Fin k → 𝕋) (l : Fin k) :
    toReal (minimumOver f) ≤ toReal (f l) := by
  rw [minimumOver, toReal_neg, neg_le]
  rw [← toReal_neg]
  exact le_maximumOver (fun i => neg (f i)) l

/-- A fold of `addUp`, so each partial sum pays one rounding in the same direction. -/
theorem sum_le_sumUp (f : Fin n → 𝕋) : ∑ i, toReal (f i) ≤ toReal (sumUp f) := by -- --- PROOF ---
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumUp, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumUp]
    exact le_trans (add_le_add (le_refl _) (ih _)) (add_le_addUp _ _)

theorem sumDown_le_sum (f : Fin n → 𝕋) :
    toReal (sumDown f) ≤ ∑ i, toReal (f i) := by -- --- PROOF ---
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumDown, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumDown]
    exact le_trans (addDown_le_add _ _) (add_le_add (le_refl _) (ih _))

/-- A count of copies, each addition rounding the way the fold does. -/
theorem le_nsmulUp (k : ℕ) (a : 𝕋) :
    (k : ℝ) * toReal a ≤ toReal (nsmulUp k a) := by -- --- PROOF ---
  induction k with
  | zero => rw [nsmulUp, toReal_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [nsmulUp, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact le_trans (by linarith) (add_le_addUp a (nsmulUp k a))

theorem nsmulDown_le (k : ℕ) (a : 𝕋) :
    toReal (nsmulDown k a) ≤ (k : ℝ) * toReal a := by -- --- PROOF ---
  induction k with
  | zero => rw [nsmulDown, toReal_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [nsmulDown, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact le_trans (addDown_le_add a (nsmulDown k a)) (by linarith)

/-- Products then sum, the direction preserved through both steps. -/
theorem dotDown_le (a b : Vec 𝕋 n) :
    toReal (dotDown a b) ≤ ∑ k, toReal (a k) * toReal (b k) :=
  le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun _ _ => mulDown_le_mul _ _)

theorem le_dotUp (a b : Vec 𝕋 n) :
    ∑ k, toReal (a k) * toReal (b k) ≤ toReal (dotUp a b) :=
  le_trans (Finset.sum_le_sum fun _ _ => mul_le_mulUp _ _) (sum_le_sumUp _)

theorem sum_abs_le_radius {d : Mat 𝕋 n h} (i : Fin n) :
    ∑ j, |toReal (d i j)| ≤ toReal (radius d i) :=
  calc ∑ j, |toReal (d i j)|
      = ∑ j, toReal (absolute (d i j)) :=
        Finset.sum_congr rfl fun _ _ => (toReal_absolute _).symm
    _ ≤ toReal (radius d i) := sum_le_sumUp _

/-- What a matrix known only to within `d` entrywise can reach on the unit ball;
`d` exact is the special case. -/
theorem abs_sum_le_radius {d : Mat 𝕋 n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hd : ∀ i j, |Δ i j| ≤ |toReal (d i j)|) (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, Δ i j * β j| ≤ toReal (radius d i) :=
  calc |∑ j, Δ i j * β j|
      ≤ ∑ j, |Δ i j * β j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |toReal (d i j)| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact le_trans (mul_le_of_le_one_right (abs_nonneg _) (hβ j)) (hd i j)
    _ ≤ toReal (radius d i) := sum_abs_le_radius i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
