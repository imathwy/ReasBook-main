import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.36: a base of a topology on `X` is formalized by the canonical predicate
`TopologicalSpace.IsTopologicalBasis B`, expressing that `B` is a family of open sets whose
members locally refine every neighborhood. -/
recall TopologicalSpace.IsTopologicalBasis {X : Type u} [TopologicalSpace X] (B : Set (Set X)) :
    Prop
