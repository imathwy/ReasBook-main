import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_41 (from Chap05/Sec05_35) -/
open Set
open scoped ContDiff Manifold Topology

noncomputable section

section

universe uM

variable {n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

/-- The distinguished boundary-coordinate component of `v` in the smooth boundary chart `e`.
In Lee's notation this is the `xⁿ`-component; in mathlib's half-space model it is indexed by `0`.
-/
def boundary_coordinate_component (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (p : M)
    (v : TangentSpace (𝓡∂ n) p) : ℝ :=
  let w : EuclideanSpace ℝ (Fin n) := (mfderiv (𝓡∂ n) (𝓡 n) (e.extend (𝓡∂ n)) p) v
  w 0

-- Proof sketch: write the tangent vector in the chosen boundary chart, reduce to the standard
-- half-space model, and characterize which curve germs remain in the interior for positive time by
-- the sign of the distinguished boundary coordinate.
/-- Proposition 5.41: in any smooth boundary chart around a boundary point, a tangent vector is
inward-pointing exactly when the distinguished boundary-coordinate component of its chart
representation is positive. -/
theorem inward_pointing_iff_boundary_coordinate_component_pos
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsInwardPointing p v ↔
      0 < boundary_coordinate_component e p v := sorry

-- Proof sketch: the same chart computation identifies outward-pointing vectors with curve germs
-- entering the interior for negative time, which corresponds to a negative distinguished
-- boundary-coordinate component.
/-- The outward-pointing vectors are exactly those whose distinguished boundary-coordinate component
is negative in any smooth boundary chart. -/
theorem outward_pointing_iff_boundary_coordinate_component_neg
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsOutwardPointing p v ↔
      boundary_coordinate_component e p v < 0 := sorry

-- Proof sketch: in boundary coordinates, a smooth curve stays in the boundary precisely when its
-- distinguished boundary coordinate vanishes to first order, so the normal component of the
-- tangent vector is zero.
/-- A tangent vector is tangent to the boundary exactly when its distinguished
boundary-coordinate component vanishes. -/
theorem tangent_to_boundary_iff_boundary_coordinate_component_eq_zero
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsBoundaryTangentVector p v ↔
      boundary_coordinate_component e p v = 0 := sorry

-- Proof sketch: combine the three sign characterizations above with the trichotomy
-- `x < 0 ∨ x = 0 ∨ 0 < x` for the distinguished boundary-coordinate component.
/-- Every tangent vector at a boundary point is tangent to the boundary, inward-pointing, or
outward-pointing. -/
theorem boundary_vector_trichotomy
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    IsBoundaryTangentVector p v ∨
      IsInwardPointing p v ∨
      IsOutwardPointing p v := sorry

-- Proof sketch: use the sign descriptions of tangent and inward-pointing vectors from boundary
-- coordinates; the distinguished boundary-coordinate component cannot be both zero and positive.
/-- A tangent vector tangent to the boundary is not inward-pointing. -/
theorem tangent_to_boundary_not_inward_pointing
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    ¬ (IsBoundaryTangentVector p v ∧ IsInwardPointing p v) := sorry

-- Proof sketch: use the sign descriptions of tangent and outward-pointing vectors from boundary
-- coordinates; the distinguished boundary-coordinate component cannot be both zero and negative.
/-- A tangent vector tangent to the boundary is not outward-pointing. -/
theorem tangent_to_boundary_not_outward_pointing
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    ¬ (IsBoundaryTangentVector p v ∧ IsOutwardPointing p v) := sorry

-- Proof sketch: use the sign descriptions of inward- and outward-pointing vectors from boundary
-- coordinates; the distinguished boundary-coordinate component cannot be both positive and
-- negative.
/-- An inward-pointing tangent vector is not outward-pointing. -/
theorem inward_pointing_not_outward_pointing
    {p : M} (hp : p ∈ (𝓡∂ n).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (hpe : p ∈ e.source)
    {v : TangentSpace (𝓡∂ n) p} :
    ¬ (IsInwardPointing p v ∧ IsOutwardPointing p v) := sorry

-- Proof sketch: reparameterize a witnessing curve by `t ↦ -t`; this flips the sign of the
-- tangent vector and exchanges positive-time interior germs with negative-time interior germs.
/-- A tangent vector is inward-pointing if and only if its negative is outward-pointing. -/
theorem inward_pointing_iff_neg_outward_pointing {p : M} {v : TangentSpace (𝓡∂ n) p} :
    IsInwardPointing p v ↔
      IsOutwardPointing p (-v) := sorry

end
