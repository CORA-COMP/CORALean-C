import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Interval.Float.Operations.Symmetric
import CORALean.ContSet.Interval.Float.Operations.OfBounds
import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds
import CORALean.ContSet.Interval.Float.Operations.BoundProj
import CORALean.ContSet.Interval.Float.Operations.BoundNegProj
import CORALean.ContSet.Interval.Float.Operations.BoundDot
import CORALean.ContSet.Interval.Float.Operations.Intersection
import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.MinkDiff
import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Reindex

/-!
# What `Interval` computes

CORA's three operations, the two box constructors every float representation
pays its rounding into, and the degenerate box a bias is added as.
-/
