import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold

-- Semantic search note: the `lean_leansearch` MCP tool was unavailable in this session, so the
-- statement uses local mathlib inspection of `NormedSpace.fromTangentSpace`.

section

universe u v

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Proposition 3.13 (1): for a finite-dimensional real vector space `V` with its standard smooth
manifold structure and a point `a : V`, the map `v ↦ Dᵥ|ₐ` is the canonical linear isomorphism
from `V` to the tangent space `TangentSpace (𝓘(ℝ, V)) a`. -/
def vector_space_to_tangent_space (a : V) : V ≃L[ℝ] TangentSpace (𝓘(ℝ, V)) a :=
  (NormedSpace.fromTangentSpace a).symm

/-- Applying `vector_space_to_tangent_space` simply regards a vector of `V` as a tangent vector at
`a`. -/
theorem vector_space_to_tangent_space_apply (a : V) (v : V) :
    vector_space_to_tangent_space a v = v := sorry

/-- Proposition 3.13 (2): if `L : V → W` is linear, then the differential of `L` carries the
tangent vector at `a` corresponding to `v` to the tangent vector at `L a` corresponding to
`L v`. -/
theorem mfderiv_vector_space_to_tangent_space (a : V) (L : V →ₗ[ℝ] W) (v : V) :
    mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, W)) L a (vector_space_to_tangent_space a v) =
      vector_space_to_tangent_space (L a) (L v) := sorry

end
