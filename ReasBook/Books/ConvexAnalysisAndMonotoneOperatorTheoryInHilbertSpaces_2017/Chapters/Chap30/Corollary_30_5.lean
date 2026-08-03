import Mathlib.Analysis.InnerProductSpace.MeanErgodic

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: Corollary 30.5 states the von Neumann mean ergodic convergence of the Cesàro
  averages `(n + 1)⁻¹ • ∑_{k=0}^n T^[k] x` for a nonexpansive `T`, with limit the orthogonal
  projection onto `ker (ContinuousLinearMap.id ℝ H - T)`.
- `core/canonical`: mathlib owns the average by `birkhoffAverage` and the convergence theorem by
  `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`; its fixed-point subspace is
  `LinearMap.eqLocus T 1`.
- `bridge/view`: `LinearMap.eqLocus_eq_ker_sub` identifies that fixed-point subspace with
  `ker (T - 1)`, and the source's `ker (id - T)` is the same kernel up to the harmless sign
  convention.

Primitive data: a contraction `T : H →L[ℝ] H` and a point `x : H`.
Derived API: the explicit Cesàro-sum expansion and the kernel formulation. -/

/- Corollary 30.5: this item is a direct recall of the canonical mean ergodic theorem for
contracting continuous linear maps on a real Hilbert space. -/
#check ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection

/- Companion recall: the textbook Cesàro average is the canonical owner `birkhoffAverage`. -/
#check birkhoffAverage

/- Companion recall: the fixed-point subspace in the owner theorem is the kernel of `T - 1`,
hence equivalently the kernel of `id - T`. -/
#check LinearMap.eqLocus_eq_ker_sub
