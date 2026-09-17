import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.HPolytope.Float.Operations.SubsetOfBounds
import CORALean.ContSet.InflatedContSet.Operations.Bound
import CORALean.ContSet.Interval.Float.Operations.BoundDot

/-!
# A zonotope as halfspaces, over a floating-point scalar

A zonotope answers a direction without a linear program, and this layer computes
that answer with directed rounding: the centre's dot product rounded up, and
each generator's contribution bounded in absolute value.

The absolute value is where a rounding mode has to be chosen twice. A generator's
exact contribution lies between its rounded-down and rounded-up dot products, so
what bounds its magnitude is the larger of the up one and the negated down one —
neither alone would do, the exact value being free to have either sign.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}

def Zonotope.nominalBoundDot (Z : Zonotope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 (nominalSet Z) c :=
  FloatBound.ofSupportBound ((InflatedContSet.nominal Z).supportBound c)
    (addUp (dotUp a Z.c)
      (sumUp fun j => maximum (dotUp a fun i => Z.G i j) (neg (dotDown a fun i => Z.G i j))))
    (by
      have h₁ : c (InflatedContSet.nominal Z).c ≤ toReal (dotUp a Z.c) := by
        rw [hc]
        exact le_dotUp a Z.c
      have h₂ : ∀ j, |c ((InflatedContSet.nominal Z).G j)|
          ≤ toReal (maximum (dotUp a fun i => Z.G i j)
              (neg (dotDown a fun i => Z.G i j))) := by
        intro j
        -- the nominal generator spelt out, so both sides name the same sum
        have hval : c ((InflatedContSet.nominal Z).G j)
            = ∑ k, toReal (a k) * toReal (Z.G k j) := hc _
        rw [hval, toReal_maximum, toReal_neg]
        refine abs_le.mpr ⟨?_, ?_⟩
        · have hdown := dotDown_le a fun i => Z.G i j
          have hm := le_max_right (toReal (dotUp a fun i => Z.G i j))
            (-toReal (dotDown a fun i => Z.G i j))
          linarith
        · have hup := le_dotUp a fun i => Z.G i j
          have hm := le_max_left (toReal (dotUp a fun i => Z.G i j))
            (-toReal (dotDown a fun i => Z.G i j))
          linarith
      -- and the generators' total, summed upward once
      have h₃ : (∑ j, |c ((InflatedContSet.nominal Z).G j)|)
          ≤ toReal (sumUp fun j => maximum (dotUp a fun i => Z.G i j)
              (neg (dotDown a fun i => Z.G i j))) :=
        le_trans (Finset.sum_le_sum fun j _ => h₂ j) (sum_le_sumUp _)
      have h₄ := add_le_addUp (dotUp a Z.c)
        (sumUp fun j => maximum (dotUp a fun i => Z.G i j) (neg (dotDown a fun i => Z.G i j)))
      show c (InflatedContSet.nominal Z).c + ∑ j, |c ((InflatedContSet.nominal Z).G j)| ≤ _
      linarith)

def Zonotope.boundDot (Z : Zonotope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 Z.construct c :=
  InflatedContSet.boundOfParts (Z.nominalBoundDot a hc) (Z.E.boundDot a hc)

def Zonotope.hPolytope (Z : Zonotope 𝕋 n) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 n :=
  HPolytope.ofBounds Aq fun i => Z.boundDot (Aq i) fun _ => rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.hPolytope_contains (Z : Zonotope 𝕋 n) (Aq : Mat 𝕋 q n) :
    Z.construct ⊆ (Z.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
