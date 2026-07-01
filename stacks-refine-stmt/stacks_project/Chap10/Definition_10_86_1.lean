import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.86.1: for an inverse system of sets over a directed preorder, the canonical owner
predicate is mathlib's `CategoryTheory.Functor.IsMittagLeffler` on functors `OrderDual I ⥤ Type`.
-/
recall CategoryTheory.Functor.IsMittagLeffler

/- Companion recall: mathlib packages the stabilization condition by saying that the eventual
range at each stage is attained. -/
recall CategoryTheory.Functor.isMittagLeffler_iff_eventualRange

/- Companion recall: over a cofiltered index category, the owner theorem
`Functor.isMittagLeffler_iff_subset_range_comp` is the canonical bridge from
`Functor.IsMittagLeffler` to stagewise range stabilization. -/
recall CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp
