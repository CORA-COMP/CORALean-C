import CORALean.Global.Float.SoundFloatArithmetic

/-!
# The hardware double as a sound float model

Each operation is IEEE-754 binary64 round-to-nearest, then one representable
value outward: the exact result lies strictly between the neighbours of its
nearest rounding, so the step bounds it in the direction asked for.

Lean's `Float` has no model, so what the proofs need of it is assumed below
(`axiom`); this is the trusted base the `Dyadic` scalar does without. The axioms
state IEEE facts about *finite* doubles. Infinities and NaN have no real value,
so every operation here carries them into its result instead: rounding keeps
them, `minimum`/`maximum` propagate NaN, and a `half` that would round is NaN.
A run whose outputs are all finite therefore only ever computed with finite
values, which `Main` checks before it reports a result.
-/

namespace CoraleanC.IEEE

open CORALean.Float

def isFinite (x : Float) : Bool := !x.isNaN && !x.isInf

/-- IEEE `nextUp` on finite values; the identity on infinities and NaN, so
rounding never turns an overflow into a finite bound. -/
def nextUp (x : Float) : Float :=
  if !isFinite x then x
  else if x == 0 then Float.ofBits 1
  else if x > 0 then Float.ofBits (x.toBits + 1)
  else Float.ofBits (x.toBits - 1)

def nextDown (x : Float) : Float := -nextUp (-x)

def nan : Float := 0 / 0

def minimum (a b : Float) : Float :=
  if a.isNaN || b.isNaN then nan else if a ≤ b then a else b

def maximum (a b : Float) : Float :=
  if a.isNaN || b.isNaN then nan else if a ≤ b then b else a

/-- Halving is exact unless the value is subnormal and odd; that case is NaN
rather than a rounded half. -/
def half (a : Float) : Float :=
  let h := a / 2
  if h * 2 == a then h else nan

instance : FloatOps Float where
  zero := 0
  one := 1
  neg a := -a
  addUp a b := nextUp (a + b)
  addDown a b := nextDown (a + b)
  mulUp a b := nextUp (a * b)
  mulDown a b := nextDown (a * b)
  divUp a b := nextUp (a / b)
  divDown a b := nextDown (a / b)
  minimum := minimum
  maximum := maximum
  le a b := decide (a ≤ b)
  half := half


-- ==========================================  AXIOMS  ========================================== --

/-- The real a finite double denotes. -/
opaque toReal : Float → ℝ

/-- Sign is a bit. -/
axiom toReal_neg (a : Float) : toReal (-a) = -toReal a
axiom toReal_zero : toReal 0 = 0
axiom toReal_one : toReal 1 = 1

/-- Round to nearest, then one step outward, brackets the exact result. -/
axiom add_bracket (a b : Float) :
    toReal (nextDown (a + b)) ≤ toReal a + toReal b ∧ toReal a + toReal b ≤ toReal (nextUp (a + b))
axiom mul_bracket (a b : Float) :
    toReal (nextDown (a * b)) ≤ toReal a * toReal b ∧ toReal a * toReal b ≤ toReal (nextUp (a * b))
axiom div_bracket (a b : Float) (hb : 0 < toReal b) :
    toReal (nextDown (a / b)) ≤ toReal a / toReal b ∧ toReal a / toReal b ≤ toReal (nextUp (a / b))

/-- The comparison is the order of the reals denoted. -/
axiom toReal_minimum (a b : Float) : toReal (minimum a b) = min (toReal a) (toReal b)
axiom toReal_maximum (a b : Float) : toReal (maximum a b) = max (toReal a) (toReal b)
axiom toReal_le_of_le {a b : Float} (h : a ≤ b) : toReal a ≤ toReal b

/-- Exact whenever it is not NaN, which is what `half` checks. -/
axiom toReal_half (a : Float) : toReal (half a) = toReal a / 2

instance : SoundFloatArithmetic Float where
  toReal := toReal
  toReal_neg := toReal_neg
  toReal_zero := toReal_zero
  toReal_one := toReal_one
  add_le_addUp a b := (add_bracket a b).2
  addDown_le_add a b := (add_bracket a b).1
  mul_le_mulUp a b := (mul_bracket a b).2
  mulDown_le_mul a b := (mul_bracket a b).1
  div_le_divUp a b hb := (div_bracket a b hb).2
  divDown_le_div a b hb := (div_bracket a b hb).1
  toReal_minimum := toReal_minimum
  toReal_maximum := toReal_maximum
  toReal_le_of_le h := toReal_le_of_le (of_decide_eq_true h)
  toReal_half := toReal_half

end CoraleanC.IEEE
