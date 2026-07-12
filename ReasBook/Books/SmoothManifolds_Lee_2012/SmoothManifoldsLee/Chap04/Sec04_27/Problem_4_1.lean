import Mathlib.Geometry.Manifold.Instances.Real
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Theorem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

namespace EuclideanHalfSpace

/-- The canonical inclusion `ℍ^n ↪ ℝ^n`. This is just the ambient coercion, exposed as a short
owner name for the half-space inclusion map used below. -/
abbrev inclusion (n : ℕ) [NeZero n] :
    EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n) := Subtype.val

end EuclideanHalfSpace

section

variable (n : ℕ) [NeZero n]

/-- Helper for Problem 4-1: the half-space inclusion is exactly the boundary model map, so it is
smooth as a map from `ℍ^n` to `ℝ^n`. -/
lemma euclideanHalfSpace_inclusion_contMDiff :
    ContMDiff (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) := by
  -- The inclusion is the defining model-with-corners map `𝓡∂ n`.
  simpa [EuclideanHalfSpace.inclusion] using
    (contMDiff_model (I := 𝓡∂ n) (n := (∞ : ℕ∞ω)))

/-- Helper for Problem 4-1: in the preferred charts at the boundary point `0`, the half-space
inclusion has manifold derivative equal to the identity. -/
lemma euclideanHalfSpace_inclusion_hasMFDerivAt_id_at_zero :
    HasMFDerivAt (𝓡∂ n) (𝓡 n) (EuclideanHalfSpace.inclusion n) 0
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) (0 : EuclideanHalfSpace n))) := by
  -- The defining map of a model with corners has derivative `id` in its own preferred chart.
  simpa [EuclideanHalfSpace.inclusion] using
    ((𝓡∂ n).hasMFDerivAt (x := (0 : EuclideanHalfSpace n)))

/-- Helper for Problem 4-1: the origin is a boundary point of the Euclidean half-space model. -/
lemma euclideanHalfSpace_zero_isBoundaryPoint :
    (𝓡∂ n).IsBoundaryPoint (0 : EuclideanHalfSpace n) := by
  -- On the model itself, the boundary is exactly the hyperplane `x 0 = 0`, and the origin lies
  -- on that hyperplane by definition.
  rw [(𝓡∂ n).isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace n]
  change (0 : ℝ) = (EuclideanHalfSpace.inclusion n 0).ofLp 0
  rfl

/-- Problem 4-1 (1): the canonical inclusion `ℍ^n ↪ ℝ^n`, namely
`EuclideanHalfSpace.inclusion n`, is smooth as a map from the Euclidean half-space model to
Euclidean space, and its manifold derivative at the boundary point `0` is invertible. -/
theorem euclideanHalfSpace_inclusion_contMDiff_and_mfderiv_isInvertible_at_zero :
    ContMDiff (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) ∧
      (mfderiv (𝓡∂ n) (𝓡 n) (EuclideanHalfSpace.inclusion n) 0).IsInvertible := by
  constructor
  · -- The smoothness half is the model-map smoothness established above.
    exact euclideanHalfSpace_inclusion_contMDiff n
  · -- Rewriting `mfderiv` through the explicit `HasMFDerivAt` calculation reduces to `id`.
    let f' :
        TangentSpace (𝓡∂ n) (0 : EuclideanHalfSpace n) →L[ℝ]
          TangentSpace (𝓡 n) (EuclideanHalfSpace.inclusion n 0) :=
      ContinuousLinearMap.id ℝ _
    have hmf : mfderiv (𝓡∂ n) (𝓡 n) (EuclideanHalfSpace.inclusion n) 0 = f' := by
      simpa [EuclideanHalfSpace.inclusion, f'] using
        (euclideanHalfSpace_inclusion_hasMFDerivAt_id_at_zero n).mfderiv
    rw [hmf]
    simpa [f'] using
      (ContinuousLinearMap.isInvertible_equiv :
        ((ContinuousLinearEquiv.refl ℝ
          (TangentSpace (𝓡∂ n) (0 : EuclideanHalfSpace n)) :
            TangentSpace (𝓡∂ n) (0 : EuclideanHalfSpace n) ≃L[ℝ]
              TangentSpace (𝓡∂ n) (0 : EuclideanHalfSpace n)) :
          TangentSpace (𝓡∂ n) (0 : EuclideanHalfSpace n) →L[ℝ]
            TangentSpace (𝓡∂ n) (0 : EuclideanHalfSpace n)).IsInvertible)

/-- Problem 4-1 (2): the boundary inclusion `ℍ^n ↪ ℝ^n` is not a local diffeomorphism at the
boundary point `0`, so the inverse-function conclusion of Theorem 4.5 fails at boundary points. -/
theorem euclideanHalfSpace_inclusion_not_isLocalDiffeomorphAt_zero :
    ¬ IsLocalDiffeomorphAt (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) 0 := by
  intro hlocal
  have hsource_boundary : (𝓡∂ n).IsBoundaryPoint (0 : EuclideanHalfSpace n) :=
    euclideanHalfSpace_zero_isBoundaryPoint n
  have htarget_boundary : (𝓡 n).IsBoundaryPoint (EuclideanHalfSpace.inclusion n 0) := by
    -- Local diffeomorphisms preserve the interior/boundary dichotomy.
    exact (hlocal.isBoundaryPoint_iff (by simp)).mp hsource_boundary
  have htarget_interior : (𝓡 n).IsInteriorPoint (EuclideanHalfSpace.inclusion n 0) := by
    -- Euclidean space is boundaryless, so every point is interior.
    simpa [EuclideanHalfSpace.inclusion] using
      (BoundarylessManifold.isInteriorPoint :
        (𝓡 n).IsInteriorPoint (0 : EuclideanSpace ℝ (Fin n)))
  exact ((𝓡 n).isBoundaryPoint_iff_not_isInteriorPoint (EuclideanHalfSpace.inclusion n 0)).1
    htarget_boundary htarget_interior

/-- Consequently the inclusion `ℍ^n ↪ ℝ^n` is not a local diffeomorphism. -/
theorem euclideanHalfSpace_inclusion_not_isLocalDiffeomorph :
    ¬ IsLocalDiffeomorph (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) := by
  intro hlocal
  -- A global local diffeomorphism is, in particular, a local diffeomorphism at `0`.
  exact euclideanHalfSpace_inclusion_not_isLocalDiffeomorphAt_zero n (hlocal 0)

/-- Companion to Problem 4-1 (2): the boundary inclusion `ℍ^n ↪ ℝ^n` cannot restrict to a
diffeomorphism between connected open neighborhoods of `0` in `ℍ^n` and `0` in `ℝ^n`. This is
the Theorem 4.5-shaped neighborhood formulation of
`euclideanHalfSpace_inclusion_not_isLocalDiffeomorphAt_zero`. -/
theorem euclideanHalfSpace_inclusion_not_diffeomorph_on_connected_open_neighborhoods_at_zero :
    ¬ ∃ U : TopologicalSpace.Opens (EuclideanHalfSpace n),
        0 ∈ (U : Set (EuclideanHalfSpace n)) ∧ IsConnected (U : Set (EuclideanHalfSpace n)) ∧
          ∃ V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)),
            0 ∈ (V : Set (EuclideanSpace ℝ (Fin n))) ∧
              IsConnected (V : Set (EuclideanSpace ℝ (Fin n))) ∧
                ∃ Φ : U ≃ₘ⟮𝓡∂ n, 𝓡 n⟯ V,
                  ∀ x : U,
                    (Φ x : EuclideanSpace ℝ (Fin n)) =
                      EuclideanHalfSpace.inclusion n x.1 := by
  rintro ⟨U, h0U, -, V, _, -, Φ, _⟩
  let x0 : U := ⟨0, h0U⟩
  have hx0_boundary : (𝓡∂ n).IsBoundaryPoint x0 := by
    -- Open-subset boundary points are exactly the ambient boundary points of their underlying
    -- values.
    exact ((𝓡∂ n).isBoundaryPoint_iff_isBoundaryPoint_val).2
      (euclideanHalfSpace_zero_isBoundaryPoint n)
  have hΦ_boundary : (𝓡 n).IsBoundaryPoint (Φ x0) := by
    -- The restricted diffeomorphism is a local diffeomorphism at every source point.
    exact ((Φ.isLocalDiffeomorph x0).isBoundaryPoint_iff (by simp)).mp hx0_boundary
  have hΦ_interior : (𝓡 n).IsInteriorPoint (Φ x0) := by
    -- Any open subset of boundaryless Euclidean space is still boundaryless.
    exact BoundarylessManifold.isInteriorPoint
  exact ((𝓡 n).isBoundaryPoint_iff_not_isInteriorPoint (Φ x0)).1 hΦ_boundary hΦ_interior

end
