import Mathlib.Topology.Homotopy.Path

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x : X}

/- Definition 1.2.2: a loop at `x` is a path from `x` to itself, namely an element of `Path x x`. -/
#check (Path x x)

/- The set `π₁(X, x)` is the quotient `Path.Homotopic.Quotient x x` of loops at `x` by
endpoint-fixed homotopy. -/
#check (Path.Homotopic.Quotient x x)
