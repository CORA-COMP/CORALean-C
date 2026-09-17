import CORALean.ContSet.ContSet.ContSet

/-!
# `WithEmpty`: what a representation denotes, or nothing at all

An operation whose result can be empty has no answer inside a representation
that denotes only nonempty sets: a zonotope always holds its centre, so no
`Zonotope → Zonotope → Zonotope` returns the Minkowski difference of `{0}` and
`[-1, 1]`, which is `∅`. Wrapping the result is what gives it one.

`Option S` in shape and deliberately not in meaning. An `Option` here says a
*candidate the caller supplied* failed its check, as `Zonotope.minkDiffRep`'s
does — a statement about the input. `WithEmpty.empty` is a statement about the
set: it denotes `∅`, and a wrapper keeps the two from being read as one.

A wrapper rather than a sum with `EmptySet`: `S` already fixes the ambient
type, where `EmptySet n` fixes it to `Vec ℝ n`, so this extends the matrix and
module ambient types too — every type `ContSet` is indexed by.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A representation extended by an explicit empty set, for an operation whose
result can be empty where `S` has no way to say so. -/
inductive WithEmpty (S : Type) where
  | empty
  | of (s : S)

/-- `∅` at `empty`, and what `S` denotes at everything else. -/
def WithEmpty.construct [ContSet S α] : WithEmpty S → Set α
  | .empty => ∅
  | .of s => ContSet.construct s

instance [ContSet S α] : ContSet (WithEmpty S) α := ⟨WithEmpty.construct⟩

@[simp] theorem WithEmpty.construct_empty [ContSet S α] :
    ContSet.construct (WithEmpty.empty : WithEmpty S) = (∅ : Set α) := rfl

@[simp] theorem WithEmpty.construct_of [ContSet S α] (s : S) :
    ContSet.construct (WithEmpty.of s) = ContSet.construct s := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
