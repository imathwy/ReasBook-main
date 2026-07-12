import Mathlib
import Mathlib.Geometry.Manifold.Instances.Real

-- Domain sampling pass: this item lies in the smooth-manifold derivative API for the boundary
-- model `EuclideanHalfSpace`. The relevant owner-layer declarations are mathlib's
-- `ModelWithCorners.hasMFDerivAt`, the derived equation `HasMFDerivAt.mfderiv`, and
-- `ContinuousLinearMap.isInvertible_equiv` for the identity continuous linear equivalence.
-- Source/core/bridge triage: the theorem below is source-facing, while the proof reuses those
-- core/canonical and bridge declarations directly instead of introducing a duplicate local owner.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

/-- Lemma 3.11: for any boundary point `a` of `ℍ^n`, the differential of the inclusion
`Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)` at `a` is an isomorphism.
This is in fact true at every point, since the inclusion is exactly the model map `𝓡∂ n`. -/
theorem mfderiv_half_space_inclusion_isInvertible
    (n : ℕ) [NeZero n] (a : EuclideanHalfSpace n) :
    (mfderiv (𝓡∂ n) (𝓡 n) (𝓡∂ n) a).IsInvertible := by
  have hmf :
      mfderiv (𝓡∂ n) (𝓡 n) (𝓡∂ n) a =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) a) := by
    simpa using
      (show HasMFDerivAt (𝓡∂ n) (𝓡 n) (𝓡∂ n) a
        (ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) a)) from
        (𝓡∂ n).hasMFDerivAt).mfderiv
  rw [hmf]
  let e : TangentSpace (𝓡∂ n) a ≃L[ℝ] TangentSpace (𝓡∂ n) a :=
    ContinuousLinearEquiv.refl ℝ (TangentSpace (𝓡∂ n) a)
  have he : (e : TangentSpace (𝓡∂ n) a →L[ℝ] TangentSpace (𝓡∂ n) a).IsInvertible :=
    ContinuousLinearMap.isInvertible_equiv
  simpa [e] using he
