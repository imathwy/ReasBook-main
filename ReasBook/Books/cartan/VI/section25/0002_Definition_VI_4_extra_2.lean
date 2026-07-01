import Mathlib.Geometry.Manifold.Complex
import Mathlib.Tactic.Recall

open scoped Manifold

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition VI.4-extra-2: for a complex manifold `X` and a complex-valued function `f : X → ℂ`,
the textbook notion that `f` is holomorphic is the canonical mathlib notion
`MDifferentiable I 𝓘(ℂ) f`, written `MDiff f` when the source model with corners and the target
complex model are inferred. This is the function-valued specialization of the ambient
complex-manifold holomorphic-map owner, so no parallel local wrapper is introduced here; the
built-in predicate already packages continuity and chartwise holomorphicity. -/
recall MDifferentiable
