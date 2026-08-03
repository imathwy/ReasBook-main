import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.17: continuity of a map `f : X → Y` at a point `x : X` is formalized by the
canonical predicate `ContinuousAt f x`; global continuity is formalized by `Continuous f`. -/
recall ContinuousAt

/- Companion recall: global continuity of a map between topological spaces is formalized by the
canonical predicate `Continuous f`. -/
recall Continuous
