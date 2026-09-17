import CORALean.Global.LinProg.API
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# Bounds whose value is machine-representable

A `SupportBound` holds a real number, which an algorithm cannot store. A
`FloatBound` holds a float and says the set stays under what that float denotes,
so an operation may keep it in a representation's field.

Everything composes the same way, one rounding mode throughout: upward wherever
two bounds are combined, since a bound only stays sound by growing. The
composition rules are `Composition`'s with `+` replaced by `addUp` and `max` by
`maximum`, and each one is that rule followed by the rounding axiom.

Read as a `SupportBound` this is the same object, so a float bound may be handed
to anything stated over ℝ; the converse needs a float large enough, which is
`raise`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
variable {S T : Set α} {c : α →ₗ[ℝ] ℝ}


-- ========================================  MAIN TYPE  ========================================= --

structure FloatBound (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    {α : Type} [AddCommGroup α] [Module ℝ α] (S : Set α) (c : α →ₗ[ℝ] ℝ) where
  val : 𝕋
  le : ∀ x ∈ S, c x ≤ toReal val

def FloatBound.toSupportBound (u : FloatBound 𝕋 S c) : SupportBound S c :=
  ⟨toReal u.val, u.le⟩

/-- A real bound becomes a float one at any float that covers it, which is where
a rounded computation discharges its obligation. -/
def FloatBound.ofSupportBound (u : SupportBound S c) (v : 𝕋) (h : u.val ≤ toReal v) :
    FloatBound 𝕋 S c :=
  ⟨v, fun x hx => le_trans (u.le x hx) h⟩

/-- As `ofSupportBound`, but the exact bound only has to exist: wrapped in a
`Prop`, it is erased, so a noncomputable exact bound (a square root, say) never
infects this one. -/
def FloatBound.ofExistsBound (v : 𝕋) (h : ∃ u : SupportBound S c, u.val ≤ toReal v) :
    FloatBound 𝕋 S c :=
  ⟨v, fun x hx => h.elim fun u hu => le_trans (u.le x hx) hu⟩

/-- A bound on a larger set bounds a smaller one, at the same value. -/
def FloatBound.mono (h : S ⊆ T) (u : FloatBound 𝕋 T c) : FloatBound 𝕋 S c :=
  ⟨u.val, fun x hx => u.le x (h hx)⟩

def FloatBound.raise (u : FloatBound 𝕋 S c) {v : 𝕋} (h : toReal u.val ≤ toReal v) :
    FloatBound 𝕋 S c :=
  ⟨v, fun x hx => le_trans (u.le x hx) h⟩

/-- A sum sees a sum of extents, with `addUp` for the one rounding it costs. -/
def FloatBound.add (u : FloatBound 𝕋 S c) (v : FloatBound 𝕋 T c) :
    FloatBound 𝕋 (S + T) c where
  val := addUp u.val v.val
  le := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    show c (x + y) ≤ toReal (addUp u.val v.val)
    rw [map_add]
    exact le_trans (add_le_add (u.le x hx) (v.le y hy)) (add_le_addUp _ _)

def FloatBound.union (u : FloatBound 𝕋 S c) (v : FloatBound 𝕋 T c) :
    FloatBound 𝕋 (S ∪ T) c where
  val := maximum u.val v.val
  le x hx := by
    rw [toReal_maximum]
    exact hx.elim (fun h => le_trans (u.le x h) (le_max_left _ _))
      fun h => le_trans (v.le x h) (le_max_right _ _)

/-- An image sees the direction pulled back, so nothing rounds. -/
def FloatBound.image {d : β →ₗ[ℝ] ℝ} (M : α →ₗ[ℝ] β) (u : FloatBound 𝕋 S (d.comp M)) :
    FloatBound 𝕋 (⇑M '' S) d where
  val := u.val
  le := by
    rintro _ ⟨x, hx, rfl⟩
    exact u.le x hx

/-- Directions add, and the two bounds are added upward — the split that lets an
inexactly computed dual solution still certify something. -/
def FloatBound.addDir {d : α →ₗ[ℝ] ℝ} (u : FloatBound 𝕋 S c) (v : FloatBound 𝕋 S d) :
    FloatBound 𝕋 S (c + d) where
  val := addUp u.val v.val
  le x hx := by
    show c x + d x ≤ toReal (addUp u.val v.val)
    exact le_trans (add_le_add (u.le x hx) (v.le x hx)) (add_le_addUp _ _)

def FloatBound.convexHull (u : FloatBound 𝕋 S c) : FloatBound 𝕋 (convexHull ℝ S) c where
  val := u.val
  le := u.toSupportBound.convexHull.le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
