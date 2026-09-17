import CORALean.Global.Float.Instances.Dyadic.Theorems.DivDownLeDiv
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeDivUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.MantissaPos
import CORALean.Global.Float.Instances.Dyadic.Theorems.RoundDownLe
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealAlign
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDivEq
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactMul
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealHalf
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealLeOfLe
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMaximum
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMinimum
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMk
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMkZero
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealNeg
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealShift
import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowAlign

/-!
# What `Dyadic` guarantees

The obligations `SoundFloatArithmetic` states, split by which step incurs
them: the `ToRealExact*`/`ToRealNeg`/`ToRealHalf`/`ToRealMkZero` family for
the operations that lose nothing, `RoundDownLe`/`LeRoundUp` for the two that
round, `LeIff` and what reads off it for the comparison, `DivDownLeDiv`/
`LeDivUp` for the one operation with no exact step to compose with.
`Instance` assembles them.
-/
