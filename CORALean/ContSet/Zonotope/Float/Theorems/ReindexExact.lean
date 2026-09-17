import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
import CORALean.ContSet.Zonotope.Float.Operations.Reindex
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# `Zonotope.reindex` is exactly the relabelled zonotope, in float too

An equality, in the layer where every other guarantee is an enclosure, and the
reason is that a relabelling does no arithmetic.

What the float layer adds is the error box, and it costs nothing here either. A
reindexing is linear, so it distributes over the Minkowski sum that
`InflatedContSet.construct` is — the relabelled set is the relabelled nominal
part plus the relabelled box, with no widening between them.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A linear map passes a Minkowski sum, which is what carries a guarantee
stated on the nominal part and the error box separately to the set itself. -/
theorem aux_image_add (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (A B : Set (Vec ℝ n)) :
    f '' (A + B) = f '' A + f '' B := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, (map_add f a b).symm⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, map_add f a b⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reindex_exact (e : Fin m ≃ Fin n) (Z : Zonotope 𝕋 n) :
    (Z.reindex e).construct = reindexLin e '' Z.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (Z.reindex e) + (Z.E.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet Z + Z.E.construct)
  have h : InflatedContSet.nominalSet (Z.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet Z :=
    (Real.Zonotope.map_exact (reindexLin e) (InflatedContSet.nominal Z)).symm
  rw [aux_image_add, Interval.reindex_exact e Z.E, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
