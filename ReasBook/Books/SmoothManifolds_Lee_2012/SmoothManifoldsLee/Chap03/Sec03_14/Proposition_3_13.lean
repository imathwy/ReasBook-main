import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold

-- Domain sampling pass: this item lies in the smooth-manifold tangent-space / manifold derivative
-- API for vector spaces. Relevant owner declarations checked before refinement:
-- `NormedSpace.fromTangentSpace` from mathlib (core/canonical owner),
-- `ContinuousLinearMap.mfderiv_eq` from mathlib's manifold derivative API for vector spaces,
-- and `LinearMap.toContinuousLinearMap` for the finite-dimensional source-facing linear-map view.
-- Primitive data is only a tangent vector in `TangentSpace (𝓘(ℝ, V)) a`; the inverse
-- identification from `V` is derived bridge/view API from the canonical owner
-- `NormedSpace.fromTangentSpace`.

section

universe u v

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]

/- Proposition 3.13 (1): the canonical identification between the tangent space of a real vector
space and the vector space itself is `NormedSpace.fromTangentSpace`; the source-facing map
`v ↦ Dᵥ|ₐ` is its inverse. -/
recall NormedSpace.fromTangentSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (v : E) : TangentSpace (𝓘(𝕜, E)) v ≃L[𝕜] E

/-- Applying the source-facing inverse of `NormedSpace.fromTangentSpace` simply regards a vector of
`V` as a tangent vector at `a`. -/
theorem vector_space_to_tangent_space_apply (a : V) (v : V) :
    ((NormedSpace.fromTangentSpace a : TangentSpace (𝓘(ℝ, V)) a ≃L[ℝ] V).symm v) = v := by
  rfl

/-- Proposition 3.13 (2): if `L : V → W` is linear, then the differential of `L` carries the
tangent vector at `a` corresponding to `v` to the tangent vector at `L a` corresponding to
`L v`. -/
theorem mfderiv_vector_space_to_tangent_space [FiniteDimensional ℝ V]
    (a : V) (L : V →ₗ[ℝ] W) (v : V) :
    mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, W)) L a
        ((NormedSpace.fromTangentSpace a : TangentSpace (𝓘(ℝ, V)) a ≃L[ℝ] V).symm v) =
      ((NormedSpace.fromTangentSpace (L a) :
        TangentSpace (𝓘(ℝ, W)) (L a) ≃L[ℝ] W).symm (L v)) := by
  change
    mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, W)) L.toContinuousLinearMap a
        ((NormedSpace.fromTangentSpace a : TangentSpace (𝓘(ℝ, V)) a ≃L[ℝ] V).symm v) =
      ((NormedSpace.fromTangentSpace (L a) :
        TangentSpace (𝓘(ℝ, W)) (L a) ≃L[ℝ] W).symm (L v))
  rw [L.toContinuousLinearMap.mfderiv_eq]
  rfl

end
