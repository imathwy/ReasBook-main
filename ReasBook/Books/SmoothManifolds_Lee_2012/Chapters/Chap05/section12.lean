import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_5_12 (from Chap05/Sec05_37) -/
-- Semantic search note: no `lean_leansearch` tool was available in this session, so this repair
-- follows the component-wise API already present in the file.

open scoped Manifold ContDiff

universe uK uVE uVM uHE uHM uE uM

open Set

variable {K : Type uK} [NontriviallyNormedField K]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace K VE]
variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace K VM]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IE : ModelWithCorners K VE HE} [IsManifold IE (∞ : ℕ∞ω) E]
variable {IM : ModelWithCorners K VM HM} [IsManifold IM (∞ : ℕ∞ω) M]
variable {π : E → M}

/-- A smooth covering map sends boundary points of the total space to boundary points of the base
manifold. -/
-- Proof sketch: use `IsLocalDiffeomorph.preimage_boundary` for the local-diffeomorphism part of the
-- smooth covering map, specialized to smooth manifolds and regularity `∞`.
theorem smooth_covering_mapsTo_boundary (hlocal : IsLocalDiffeomorph IE IM ∞ π) :
    MapsTo π (IE.boundary E) (IM.boundary M) := sorry

/-- A surjective smooth covering map maps the boundary of the total space onto the boundary of the
base manifold. -/
-- Proof sketch: combine surjectivity of `π` with `mapsTo_boundary`; any preimage of a boundary
-- point is again a boundary point by the local-diffeomorphism boundary formula.
theorem smooth_covering_image_boundary_eq (hsurj : Function.Surjective π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) :
    π '' IE.boundary E = IM.boundary M := sorry

/-- A smooth covering map sends each connected component of the boundary into the connected
component of the image point in the boundary of the base. -/
-- Proof sketch: `π` is continuous because a covering map is continuous; apply
-- `Continuous.mapsTo_connectedComponentIn` to the boundary, then rewrite the image of the boundary
-- using `image_boundary_eq`.
theorem smooth_covering_mapsTo_boundary_component (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    MapsTo π (connectedComponentIn (IE.boundary E) x)
      (connectedComponentIn (IM.boundary M) (π x)) := sorry

/-- The restriction of a smooth covering map to a connected component of the boundary, viewed as a
map to the connected component of the image point in the boundary of the base. -/
abbrev boundaryComponentRestriction (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : IE.boundary E) :
    connectedComponentIn (IE.boundary E) x →
      connectedComponentIn (IM.boundary M) (π x) :=
  fun y ↦ ⟨π y, smooth_covering_mapsTo_boundary_component hcov hlocal x y.2⟩

/-- The boundary-component restriction agrees with the original covering map on underlying
points. -/
-- Proof sketch: unfold `boundaryComponentRestriction`; its codomain subtype stores `π y` as the
-- underlying point.
theorem boundaryComponentRestriction_val (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : IE.boundary E)
    (y : connectedComponentIn (IE.boundary E) x) :
    ((boundaryComponentRestriction hcov hlocal x y :
      connectedComponentIn (IM.boundary M) (π x)) : M) = π y :=
    sorry

/-- Problem 5-12 (1): the restriction of a smooth covering map to a boundary connected component is
onto the corresponding boundary connected component of the image point. -/
-- Proof sketch: first restrict the ambient covering map to the whole boundary using
-- `image_boundary_eq`; then use connectedness of the target component to show the source component
-- containing `x` covers that target component surjectively.
theorem boundaryComponentRestriction_surjective (hsurj : Function.Surjective π)
    (hcov : IsCoveringMap π) (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    Function.Surjective (boundaryComponentRestriction hcov hlocal x) := sorry

/-- Problem 5-12 (2): the restriction of a smooth covering map to a boundary connected component
is still a covering map. -/
-- Proof sketch: restrict the ambient covering map first to the boundary and then to the connected
-- component of `π x`; identify the resulting source with the connected component of `x` in the
-- boundary.
theorem boundaryComponentRestriction_isCoveringMap (hcov : IsCoveringMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    IsCoveringMap (boundaryComponentRestriction hcov hlocal x) := sorry

/-- Problem 5-12 (3): the ambient smooth local-diffeomorphism property restricts to each connected
component of the boundary. -/
-- Proof sketch: the ambient map is a local diffeomorphism everywhere, so its restriction to the
-- subset `connectedComponentIn (IE.boundary E) x` is automatically an `IsLocalDiffeomorphOn`.
theorem boundaryComponentRestriction_isLocalDiffeomorphOn
    (hlocal : IsLocalDiffeomorph IE IM ∞ π)
    (x : IE.boundary E) :
    IsLocalDiffeomorphOn IE IM ∞ π (connectedComponentIn (IE.boundary E) x) := sorry

/-! ### Theorem_5_12 (from Chap05/Sec05_30) -/
open scoped ContDiff Manifold

section ConstantRankLevelSets

universe uE uE' uH uH' uM uN

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was matched against the local constant-rank API from `Exercise_4_4`, the embedded
-- submanifold API from `Definition_5_28_extra_1`, and the nearby level-set precedent in
-- `Corollary_5_13`.
-- Proof sketch: apply the constant-rank theorem pointwise on the level set to obtain local slice
-- coordinates of codimension `r`, then package the resulting manifold structure on the fiber.
/-- Theorem 5.12 (1) (Constant-Rank Level Set Theorem): each level set of a smooth constant-rank
map carries a smooth embedded submanifold structure whose codimension is the constant rank. -/
theorem constant_rank_level_set_has_embedded_submanifold_structure {r : ℕ} {Φ : M → N}
    (hΦsmooth : ContMDiff I J ∞ Φ) (hΦrank : HasConstantRank I J Φ r) (c : N) :
    let k : ℕ := Module.finrank ℝ E - r
    let S : Set M := Φ ⁻¹' {c}
    let K :=
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
        ∃ hs : IsManifold K ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold K ∞ S := hs
        ∃ hS : IsEmbeddedSubmanifold I K S, hS.codimension = r := sorry

-- Proof sketch: the level set is the preimage of the closed singleton `{c}` under the continuous
-- map `Φ`, so it is closed in `M`; combine this with the embedded-submanifold structure from (1).
/-- Theorem 5.12 (2) (Constant-Rank Level Set Theorem): each level set of a smooth constant-rank
map is properly embedded in the ambient manifold. -/
theorem constant_rank_level_set_isProperlyEmbedded [T1Space N] {r : ℕ} {Φ : M → N}
    (hΦsmooth : ContMDiff I J ∞ Φ) (hΦrank : HasConstantRank I J Φ r) (c : N) :
    (Φ ⁻¹' {c}).IsProperlyEmbedded := sorry

end ConstantRankLevelSets
