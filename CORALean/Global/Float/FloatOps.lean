import CORALean.Global.Tensor

/-!
# Floating-point operations

The arithmetic a machine float offers, with no claim about what it computes:
two rounding directions per operation, and the exact operations that need none.
`SoundFloatArithmetic` is what says the directions are honest.

Kept separate from that class so the layer stays executable — a real
interpretation is noncomputable, and so is everything reached through a class
carrying one. Definitions assume this class alone; theorems assume both.

The folds recurse so that proofs about them are one induction, and run as loops
because `@[csimp]` swaps in a `Fin.foldr` version — which the compiler accepts
only with the proof of equality beside it, so the trusted base is untouched and
the theorems still see the recursion. Each swap sits directly under the
definition it replaces: `@[csimp]` reaches only the call sites compiled after
it, so a use above the attribute would keep the recursion and its cost.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

class FloatOps (𝕋 : Type) where
  zero : 𝕋
  /-- Every format has it exactly, and a constraint matrix cannot name a
  coordinate without it. -/
  one : 𝕋
  /-- Sign is a bit, so negation needs no direction. -/
  neg : 𝕋 → 𝕋
  addUp : 𝕋 → 𝕋 → 𝕋
  addDown : 𝕋 → 𝕋 → 𝕋
  mulUp : 𝕋 → 𝕋 → 𝕋
  mulDown : 𝕋 → 𝕋 → 𝕋
  /-- Constrained only for a positive divisor, which costs nothing: `neg` is
  exact, so a caller dividing by a negative `b` negates both arguments. -/
  divUp : 𝕋 → 𝕋 → 𝕋
  divDown : 𝕋 → 𝕋 → 𝕋
  /-- Exact, like `neg`: choosing between two floats invents no digits. -/
  minimum : 𝕋 → 𝕋 → 𝕋
  maximum : 𝕋 → 𝕋 → 𝕋
  /-- `SoundFloatArithmetic` constrains a `true` answer only: that is what a
  generator ranking spends, and what lets a caller elsewhere discharge a bound
  hypothesis it already suspects holds. -/
  le : 𝕋 → 𝕋 → Bool
  /-- Exact in a binary format, where halving only moves the exponent. -/
  half : 𝕋 → 𝕋

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

/-! ## Subtraction

Derived, not assumed: negation is exact, so a directed difference is a directed
sum. -/

def subUp (a b : 𝕋) : 𝕋 := addUp a (neg b)
def subDown (a b : 𝕋) : 𝕋 := addDown a (neg b)

/-! ## Summation

`addUp` is not associative, so a sum has to name its own bracketing rather than
go through `Finset.sum`. Right-nested, matching `Fin.sum_univ_succ`, so the
bounds are one induction. -/

def sumUp : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | _ + 1, f => addUp (f 0) (sumUp fun i => f i.succ)

def sumDown : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | _ + 1, f => addDown (f 0) (sumDown fun i => f i.succ)

/-- `Fin.foldr` nests to the right, which is what makes this the same sum and
not merely an equal one: the bracketing is the definition's. -/
def sumUpImpl {n : ℕ} (f : Fin n → 𝕋) : 𝕋 := Fin.foldr n (fun i acc => addUp (f i) acc) zero

def sumDownImpl {n : ℕ} (f : Fin n → 𝕋) : 𝕋 := Fin.foldr n (fun i acc => addDown (f i) acc) zero

@[csimp] theorem sumUp_eq_impl : @sumUp = @sumUpImpl := by -- --- PROOF ---
  funext 𝕋 _ n
  induction n with
  | zero => funext f; rw [sumUpImpl, Fin.foldr_zero]; rfl
  | succ n ih =>
    funext f
    -- The recursion peels `f 0`; `Fin.foldr_succ` peels the same entry.
    rw [sumUpImpl, Fin.foldr_succ, ← sumUpImpl, ← congrFun ih fun i => f i.succ]
    rfl

@[csimp] theorem sumDown_eq_impl : @sumDown = @sumDownImpl := by -- --- PROOF ---
  funext 𝕋 _ n
  induction n with
  | zero => funext f; rw [sumDownImpl, Fin.foldr_zero]; rfl
  | succ n ih =>
    funext f
    rw [sumDownImpl, Fin.foldr_succ, ← sumDownImpl, ← congrFun ih fun i => f i.succ]
    rfl

/-! ## Repeated addition

A count of copies, one fold per direction. The count comes from an exponent
matrix, which is over ℕ in both layers, so only the additions round. -/

def nsmulDown : ℕ → 𝕋 → 𝕋
  | 0, _ => zero
  | k + 1, a => addDown a (nsmulDown k a)

def nsmulUp : ℕ → 𝕋 → 𝕋
  | 0, _ => zero
  | k + 1, a => addUp a (nsmulUp k a)

/-- The largest of `n` values, `zero` below none. Exact, as `maximum` is, so it
needs no direction. -/
def maximumOver : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | _ + 1, f => maximum (f 0) (maximumOver fun i => f i.succ)

/-- Right-nested like `maximumOver`. `maximum` is associative where `addUp` is
not, so here the bracketing is a matter of cost alone. -/
def maximumOverImpl {n : ℕ} (f : Fin n → 𝕋) : 𝕋 :=
  Fin.foldr n (fun i acc => maximum (f i) acc) zero

@[csimp] theorem maximumOver_eq_impl : @maximumOver = @maximumOverImpl := by -- --- PROOF ---
  funext 𝕋 _ n
  induction n with
  | zero => funext f; rw [maximumOverImpl, Fin.foldr_zero]; rfl
  | succ n ih =>
    funext f
    rw [maximumOverImpl, Fin.foldr_succ, ← maximumOverImpl, ← congrFun ih fun i => f i.succ]
    rfl

/-- The smallest of `n` values, `zero` above none. `neg` and `maximum` are both
exact, so the reflection costs nothing and no second fold is needed. -/
def minimumOver {n : ℕ} (f : Fin n → 𝕋) : 𝕋 := neg (maximumOver fun i => neg (f i))

/-- Exact. Not named `abs`, which would make `|·|` ambiguous wherever this
namespace is open. -/
def absolute (a : 𝕋) : 𝕋 := maximum a (neg a)

/-! ## Dot products

Products and sum rounded the same way. Every matrix operation in the layer is
built from these two. -/

def dotDown {n : ℕ} (a b : Vec 𝕋 n) : 𝕋 := sumDown fun k => mulDown (a k) (b k)
def dotUp {n : ℕ} (a b : Vec 𝕋 n) : 𝕋 := sumUp fun k => mulUp (a k) (b k)

/-- Row sums of absolute values, rounded up: the half-width of the hull of a
zonotope centred at zero with these generators. -/
def radius {n h : ℕ} (G : Mat 𝕋 n h) : Vec 𝕋 n := fun i => sumUp fun j => absolute (G i j)

/-- One generator per coordinate. Not `Matrix.diagonal`, which needs `Zero 𝕋`,
and giving `𝕋` one would collide with ℝ's on the `SoundFloatArithmetic ℝ`
instance. -/
def diagonalBlock {n : ℕ} (v : Vec 𝕋 n) : Mat 𝕋 n n := fun i l => if i = l then v i else zero

/-! ## Rounded linear algebra

Each entry is a dot product. Both directions are kept: the stored value is the
lower one, the gap to the upper what a caller is charged. -/

def mulVecDown {m n : ℕ} (M : Mat 𝕋 m n) (v : Vec 𝕋 n) : Vec 𝕋 m := fun i => dotDown (M i) v
def mulVecUp {m n : ℕ} (M : Mat 𝕋 m n) (v : Vec 𝕋 n) : Vec 𝕋 m := fun i => dotUp (M i) v

def matMulDown {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => dotDown (M₁ i) (fun l => M₂ l j)
def matMulUp {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => dotUp (M₁ i) (fun l => M₂ l j)

/-- How far a stored entry can be from the exact product. -/
def matMulDiff {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => subUp (matMulUp M₁ M₂ i j) (matMulDown M₁ M₂ i j)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
