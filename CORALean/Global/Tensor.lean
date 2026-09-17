import CORALean.Global.Mathlib

/-!
# Arrays: vectors, matrices, tensors

`Tensor α s` is an array of `α` of shape `s`, curried, so an entry is read by
applying one index per axis, and `Vec` is its order-one case. The scalar is
explicit because it separates the two arithmetic layers: `Vec ℝ n` is a point,
`Vec 𝕋 n` its machine representation.
`Mat` is the order-two case up to `rfl`, but spelt as Mathlib's `Matrix`, whose
wrapper keeps `*` matrix multiplication rather than the pointwise product; and
instance search sees through it in neither direction.

Being curried also makes a tensor a closure, so the one an operation returns
carries its whole history and every read walks it again. A representation stores
its fields with `Vector.ofFn`, in the `materialise` it keeps for that, and never
through a `Vec → Vec` helper: a definition whose result type is a function is
eta-expanded to that arity, so it recomputes its storage on every read and is
slower than storing nothing. Only a definition returning a structure lets the
closure hold the vector; a stored entry is indexed with `i.isLt` for the same
reason.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

universe u

abbrev Tensor (α : Type u) : List ℕ → Type u
  | [] => α
  | n :: s => Fin n → Tensor α s

abbrev Vec (α : Type u) (n : ℕ) := Tensor α [n]
abbrev Mat (α : Type u) (n m : ℕ) := Matrix (Fin n) (Fin m) α


-- =======================================  MAIN THEOREM  ======================================= --

theorem mat_eq_tensor (α : Type u) (n m : ℕ) : Mat α n m = Tensor α [n, m] := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
