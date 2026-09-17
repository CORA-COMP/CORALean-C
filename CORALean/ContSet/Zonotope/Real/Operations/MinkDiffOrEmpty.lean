import CORALean.ContSet.WithEmpty.WithEmpty
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

/-!
# `Zonotope.minkDiffOrEmpty`

`minkDiffRep` at whichever generator representation certifies one, wrapped so
that the result may be empty. No zonotope denotes `∅` — `β = 0` gives the
centre — while `{0} ⊖ [-1, 1]` is `∅`, so a total `Zonotope → Zonotope →
Zonotope` cannot meet `MinkDiff`'s obligation and this one can.

Two readings of "nothing", kept apart by two types. `minkDiffRep`'s `none`
says the caller's `M` failed its check, about the input; `WithEmpty.empty`
says the returned *set* is `∅`. As `MinkDiff` is inner, `∅` is sound whatever
the true difference is, and this returns it exactly when no `M` certifies —
which claims the difference is empty no more than the class ever does.

Classical, and noncomputable with it: the class field takes no candidate, so
which `M` is used is a choice made here rather than by the caller. A caller
holding one calls `minkDiffRep` and keeps the precision that goes with it.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The difference at some certified generator representation, and the explicit
empty set where none certifies. -/
noncomputable def Zonotope.minkDiffOrEmpty (Z₁ Z₂ : Zonotope α) : WithEmpty (Zonotope α) :=
  if h : ∃ M, (Z₁.minkDiffRep Z₂ M).isSome then
    .of ((Z₁.minkDiffRep Z₂ h.choose).get h.choose_spec)
  else .empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
