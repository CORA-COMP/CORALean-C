import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# Composing a nominal part with its box

Set addition is commutative and associative, so the two nominal parts and the
two boxes regroup and each side is weakened once. Every binary operation that
computes its nominal part approximately reduces to this.

The three representations are separately typed, since an operation may take and
return different ones.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S₁ S₂ T N₁ N₂ N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N₁ (Vec ℝ n)] [ContSet N₂ (Vec ℝ n)] [ContSet N (Vec ℝ n)]
variable [InflatedContSet S₁ N₁ 𝕋 n] [InflatedContSet S₂ N₂ 𝕋 n] [InflatedContSet T N 𝕋 n]


-- =======================================  MAIN THEOREM  ======================================= --

theorem plus_subset {s₁ : S₁} {s₂ : S₂} {t : T} {D : Set (Vec ℝ n)}
    (hnominal : nominalSet s₁ + nominalSet s₂ ⊆
      nominalSet t + D)
    (herror : (error s₁).construct + (error s₂).construct + D ⊆ (error t).construct) :
    construct s₁ + construct s₂ ⊆ construct t := by -- --- PROOF ---
  show nominalSet s₁ + (error s₁).construct
      + (nominalSet s₂ + (error s₂).construct) ⊆
    nominalSet t + (error t).construct
  -- the four summands regrouped so each hypothesis applies to one pair
  calc nominalSet s₁ + (error s₁).construct
        + (nominalSet s₂ + (error s₂).construct)
      = nominalSet s₁ + nominalSet s₂
        + ((error s₁).construct + (error s₂).construct) := add_add_add_comm _ _ _ _
    _ ⊆ nominalSet t + D
        + ((error s₁).construct + (error s₂).construct) :=
        Set.add_subset_add_right hnominal
    _ = nominalSet t
        + ((error s₁).construct + (error s₂).construct + D) := by
        rw [add_assoc, add_comm D _]
    _ ⊆ nominalSet t + (error t).construct :=
        Set.add_subset_add_left herror

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
