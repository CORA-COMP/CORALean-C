import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.Zonotope.Float.Theorems.Convex
import CORALean.ContSet.Zonotope.Float.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact

/-!
# What `Zonotope` instantiates

`ContSet` is not among them — `InflatedContSet` supplies it, which is what makes
this the same class the exact layer instantiates. So an algorithm written against
the three operation classes run here with no float counterpart to write.

A zonotope's four fields are function types, so the one an operation returns is a
closure over the one it was given and nothing stores the numbers in between: a
loop that iterates operations rebuilds its whole history on every entry read, and
costs geometrically in the number of iterations rather than linearly.
`Zonotope.materialise` stores them, and `materialise_eq` says it is the identity,
so each proof below is the operation's own guarantee after one rewrite.

It goes here rather than in `Operations/`: an algorithm reaches a representation
through the operation fields below and through nothing else, so this is the place
that knows a set is about to be handed back to a loop. In the operations it
would have to guess which of them a loop calls — `NeuralNetwork.enclose` calls
neither `reduce` nor `linComb`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

/-- Not the nominal zonotope's own convexity read across: the set is that one
plus the error box, and `Convex.add` is what carries the property over the sum. -/
instance {n : ℕ} : ConvexSet (Zonotope 𝕋 n) (Vec ℝ n) := ⟨Zonotope.convex_construct⟩

/-- Compactness, not the closed-and-bounded pair, for the exact layer's reason;
it survives the box because a sum of two compact sets is compact. -/
instance {n : ℕ} : CompactSet (Zonotope 𝕋 n) (Vec ℝ n) := ⟨Zonotope.isCompact_construct⟩

instance {n : ℕ} : Plus (Zonotope 𝕋 n) (Vec ℝ n) where
  plus Z₁ Z₂ := (Z₁.plus Z₂).materialise
  plus_outer Z₁ Z₂ := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.plus_outer Z₁ Z₂

instance {n : ℕ} : LinComb (Zonotope 𝕋 n) (Vec ℝ n) where
  linComb Z₁ Z₂ := (Z₁.linComb Z₂).materialise
  linComb_outer Z₁ Z₂ := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.linComb_outer Z₁ Z₂

instance {n : ℕ} : Reduce (Zonotope 𝕋 n) (Vec ℝ n) where
  reduce Z o := (Z.reduce o).materialise
  reduce_outer Z o := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.reduce_outer Z o

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex (Zonotope 𝕋) where
  reindex e Z := (Zonotope.reindex e Z).materialise
  reindex_exact e Z := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.reindex_exact e Z

instance : Mtimes (Mat 𝕋) (Zonotope 𝕋) where
  mtimes M Z := (Zonotope.mtimes M Z).materialise
  mtimes_outer M Z := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, Zonotope.materialise_eq]
    exact Zonotope.mtimes_outer M Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
