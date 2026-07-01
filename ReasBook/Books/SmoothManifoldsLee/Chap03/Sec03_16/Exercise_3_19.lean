import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

noncomputable section

universe u

variable {n : ℕ} [NeZero n]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ⊤ M]

/- Exercise 3.19: if `M` is a smooth manifold with boundary, then its tangent bundle carries the
canonical topology and smooth structure coming from the tangent-bundle model with corners
`(𝓡∂ n).tangent`. -/
#synth TopologicalSpace (TangentBundle (𝓡∂ n) M)
#synth IsManifold (𝓡∂ n).tangent ⊤ (TangentBundle (𝓡∂ n) M)

-- Proof sketch: compose the canonical tangent-bundle chart with the product-swap homeomorphism;
-- its coordinate expression is then the tuple `(v, x)` obtained from the natural `(x, v)` chart
-- by permuting the two factors.
/-- Exercise 3.19: the canonical tangent-bundle topology and smooth structure on `TM` for a smooth
manifold with boundary have the property that swapping the factors in the natural chart
`(x, v)` gives the boundary-chart coordinate expression `(v, x)` described in the exercise. -/
theorem tangentBundleBoundaryChart_apply
    (p q : TangentBundle (𝓡∂ n) M) :
    ((chartAt (ModelProd (EuclideanHalfSpace n) (EuclideanSpace ℝ (Fin n))) p).transHomeomorph
      (Homeomorph.prodComm (EuclideanHalfSpace n) (EuclideanSpace ℝ (Fin n))) q) =
      Prod.swap ((chartAt (ModelProd (EuclideanHalfSpace n) (EuclideanSpace ℝ (Fin n))) p) q) := rfl
