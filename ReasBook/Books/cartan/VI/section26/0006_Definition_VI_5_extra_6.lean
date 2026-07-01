import Mathlib.Geometry.Manifold.Complex
import Mathlib.Tactic.Recall

open scoped Manifold

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition VI.5-extra-6: once a Riemann surface is viewed through its underlying complex
analytic manifold `X`, the textbook notion of a holomorphic function `f : X → ℂ` is exactly the
canonical mathlib owner `MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f`, written `MDiff f` when the source and
target complex models are inferred. This item is therefore a direct recall of the ambient
complex-manifold notion rather than a separate Riemann-surface wrapper. -/
recall MDifferentiable
