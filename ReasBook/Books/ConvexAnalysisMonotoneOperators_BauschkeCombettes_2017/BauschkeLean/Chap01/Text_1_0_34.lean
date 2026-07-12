import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.34: a topology on a type `X` is the canonical structure `TopologicalSpace X`,
encoding the empty set, the whole space, arbitrary unions, and finite intersections of open
sets; a topological space is therefore a type equipped with an instance of `TopologicalSpace X`,
and the associated notions of open and closed sets are `IsOpen` and `IsClosed`. -/
recall TopologicalSpace (X : Type u) : Type u

/- Open sets of a topological space are formalized by the predicate `IsOpen`. -/
recall IsOpen {X : Type u} [TopologicalSpace X] (s : Set X) : Prop

/- Closed sets of a topological space are formalized by the predicate `IsClosed`. -/
recall IsClosed {X : Type u} [TopologicalSpace X] (s : Set X) : Prop
