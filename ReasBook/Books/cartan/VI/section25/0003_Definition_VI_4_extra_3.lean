import Mathlib.Geometry.Manifold.Complex
import Mathlib.Tactic.Recall

open scoped Manifold

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition VI.4-extra-3: for spaces endowed with complex manifold structures, the textbook
notion of a holomorphic mapping `φ : X → Y` is the canonical mathlib owner
`MDifferentiable I I' φ`; `MDiff φ` is only the corresponding notation when the source and target
models with corners are inferred. This is a direct recall of the ambient complex-manifold owner
rather than a separate local wrapper. The continuity requirement, local-coordinate holomorphicity,
and independence of the chosen coordinates are built into this manifold-differentiability predicate
over `ℂ`. -/
recall MDifferentiable
