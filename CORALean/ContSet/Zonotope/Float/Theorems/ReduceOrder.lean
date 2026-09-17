import CORALean.ContSet.Zonotope.Float.Operations.ReduceCombastel

/-!
# `Zonotope.reduceCombastel` bounds the generator count

The exact layer's bound, and the same proof: `h` is the `ℕ` field `reduceBy`'s
shape gives regardless of the scalar, so nothing about rounding enters, and
nothing about the ranking does either, which leaves `le`'s comparator free.

Girard's rule admits the identical bound; it is not stated here, since this
addition is scoped to Combastel's rule alone.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceCombastel_order_le (Z : Zonotope 𝕋 n) {o : ℕ} (ho : 0 < o) :
    (Z.reduceCombastel o).h ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold Zonotope.reduceCombastel
  split_ifs with hlt
  · exact le_of_eq hK
  · exact Nat.le_of_not_lt hlt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
