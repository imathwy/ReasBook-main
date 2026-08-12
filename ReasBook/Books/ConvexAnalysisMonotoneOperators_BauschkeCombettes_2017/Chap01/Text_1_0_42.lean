import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.42: a Hausdorff topological space is formalized by the canonical predicate
`T2Space X`, expressing that distinct points admit disjoint neighborhoods. -/
recall T2Space {X : Type u} [TopologicalSpace X] : Prop
