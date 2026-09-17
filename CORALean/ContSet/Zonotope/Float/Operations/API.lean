import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.PlusBox
import CORALean.ContSet.Zonotope.Float.Operations.Midpoint
import CORALean.ContSet.Zonotope.Float.Operations.MidpointResidual
import CORALean.ContSet.Zonotope.Float.Operations.PairSum
import CORALean.ContSet.Zonotope.Float.Operations.PairDiff
import CORALean.ContSet.Zonotope.Float.Operations.LinCombG
import CORALean.ContSet.Zonotope.Float.Operations.LinCombGDiff
import CORALean.ContSet.Zonotope.Float.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Operations.MtimesResidual
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
import CORALean.ContSet.Zonotope.Float.Operations.ShiftDown
import CORALean.ContSet.Zonotope.Float.Operations.ShiftUp
import CORALean.ContSet.Zonotope.Float.Operations.ErrorRadius
import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError
import CORALean.ContSet.Zonotope.Float.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
import CORALean.ContSet.Zonotope.Float.Operations.ReduceByBox
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox
import CORALean.ContSet.Zonotope.Float.Operations.ReduceCombastel
import CORALean.ContSet.Zonotope.Float.Operations.Reduce
import CORALean.ContSet.Zonotope.Float.Operations.ReduceAndAbsorb
import CORALean.ContSet.Zonotope.Float.Operations.Reindex

/-!
# What `Zonotope` computes

Each pays its rounding into the error box rather than into new generators,
except where a diagonal block is being appended anyway.

`PlusBox`, `MtimesBox`, `ReduceByBox` and `ReduceGirardBox` are the reverse of
that: real-valued zonotopes bounding how far an operation's result reaches
*beyond* the exact operation on its operand, for `reachErrorFloat`'s own use.
-/
