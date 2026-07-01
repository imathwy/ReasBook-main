import Mathlib
import Mathlib.Dynamics.Ergodic.Ergodic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Definition 20.6 (1): for a probability space `(Ω, 𝓐, P)` and measurable transformation `τ`,
the textbook condition `P[τ⁻¹(A)] = P[A]` for all `A ∈ 𝓐` is the canonical notion
`MeasurePreserving τ P P`; thus a measure-preserving dynamical system
`(Ω, 𝓐, P, τ)` is encoded by this predicate. -/
recall MeasurePreserving

/- Definition 20.6 (2): on a probability space, an ergodic measure-preserving dynamical system is
the canonical notion `Ergodic τ P`; equivalently, every measurable invariant set is `P`-trivial,
i.e. has probability `0` or `1`. -/
recall Ergodic
