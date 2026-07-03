import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file lives in several-complex-variable holomorphy on open subsets of
-- `ℂ^n`. The owner abstraction is mathlib's `DifferentiableOn`; the primitive datum is complex
-- Fréchet differentiability within the domain, while coordinate descriptions and open-set analytic
-- reformulations are derived API.

/- Definition IV.5-extra-1: for a function on an open set `D` of `ℂ^n`, represented here as
`D : Set (Fin n → ℂ)`, the textbook notion of being holomorphic in `D` is modeled canonically by
`DifferentiableOn ℂ f D`. For maps between complex normed spaces, complex Fréchet differentiability
is the coordinate-free form of the condition that the differential has no `d\bar z_k` part, i.e.
`df = ∑ k, (∂f/∂z_k) dz_k`. -/
recall DifferentiableOn
