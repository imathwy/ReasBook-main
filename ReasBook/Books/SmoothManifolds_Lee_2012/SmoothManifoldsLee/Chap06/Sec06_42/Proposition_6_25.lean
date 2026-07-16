import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_8
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Theorem_4_26
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_42.Definition_6_42_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped ContDiff Manifold NormalBundle

noncomputable section

section TubularNeighborhoodRetraction

variable {n m : ℕ}
variable {M : Set (EuclideanSpace ℝ (Fin n))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
variable [IsManifold (𝓡 n) ∞ (NM[n, m; M])]

-- Domain sampling pass: Proposition 6.25 lives in the embedded-submanifold / normal-bundle
-- domain. The relevant upstream owner declarations checked before refinement are
-- `NM[n, m; M]` and `π_NM[n, m; M]` from `Definition_6_42_extra_1`,
-- `NormalBundle.endpointMap`,
-- `NormalBundle.TubularNeighborhood`,
-- and `Manifold.IsSmoothSubmersion`.
-- The owner abstraction is `NormalBundle.TubularNeighborhood`; the retraction and inclusion are
-- derived maps on that owner, not primitive data of a second public wrapper.

namespace NormalBundle

/-- The chosen ambient smooth structure on `NM[n, m; M]` is compatible with the canonical
product-coordinate description used in Section 6.42. -/
class CompatibleSmoothStructure
    (n m : ℕ)
    (M : Set (EuclideanSpace ℝ (Fin n)))
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ∞ M]
    [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])] : Prop where
  toProd_isSmoothEmbedding :
    IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M)

/-- The compatibility package exposes the smooth-embedding property of the canonical product
coordinates on the normal bundle. -/
theorem isSmoothEmbedding_normal_bundle_toProd
    [h : CompatibleSmoothStructure n m M] :
    IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M) :=
  h.toProd_isSmoothEmbedding

/-- Helper: the canonical projection `π_NM[n, m; M]` from the normal bundle to its base manifold
is smooth. -/
lemma piNM_contMDiff
    (h_toProd :
      IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M)) :
    ContMDiff (𝓡 n) (𝓡 m) ∞ (π_NM[n, m; M] : NM[n, m; M] → M) := sorry

/-- Helper: a point of the normal bundle lies on a smooth local section of `π_NM[n, m; M]`. -/
lemma piNM_hasSmoothLocalSectionThrough
    (h_toProd :
      IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M))
    (p : NM[n, m; M]) :
    ∃ U : TopologicalSpace.Opens M, ∃ hpU : π_NM[n, m; M] p ∈ U, ∃ σ : U → NM[n, m; M],
      Manifold.IsSmoothLocalSection (𝓡 n) (𝓡 m) (π_NM[n, m; M] : NM[n, m; M] → M) U σ ∧
        σ ⟨π_NM[n, m; M] p, hpU⟩ = p := sorry

/-- Helper: the canonical projection `π_NM[n, m; M]` is a smooth submersion. -/
theorem piNM_isSmoothSubmersion
    (h_toProd :
      IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M)) :
    IsSmoothSubmersion (𝓡 n) (𝓡 m) (π_NM[n, m; M] : NM[n, m; M] → M) := by
  -- The local-section criterion converts the bundle-section package into the submersion property.
  refine ⟨piNM_contMDiff h_toProd, ?_⟩
  exact
    (Manifold.smooth_submersion_iff_exists_smooth_local_section_through_every_point
      (piNM_contMDiff h_toProd)).2
      (piNM_hasSmoothLocalSectionThrough h_toProd)

end NormalBundle

namespace NormalBundle.TubularNeighborhood

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- The canonical map associated to a tubular neighborhood is the normal-bundle projection
transported across the inverse of the endpoint diffeomorphism. -/
def retraction (T : TubularNeighborhood n m M) : T.neighborhood → M := fun y ↦
  π_NM[n, m; M] (T.endpointDiffeomorph.symm y)

/-
The helper layer works with the local normal-bundle manifold structure already present in the
section context.
-/
omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- The canonical tubular retraction is given pointwise by the normal-bundle projection composed
with the inverse endpoint diffeomorphism. -/
@[simp] theorem retraction_apply (T : TubularNeighborhood n m M) (y : T.neighborhood) :
    T.retraction y = π_NM[n, m; M] (T.endpointDiffeomorph.symm y) :=
  rfl

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper: the zero normal vector over `x` lies in the chosen tube. -/
lemma zeroVector_mem_tube (T : TubularNeighborhood n m M) (x : M) :
    Bundle.TotalSpace.mk x (0 : N[n, m; M; x]) ∈ (T.tube : Set (NM[n, m; M])) := by
  -- Rewrite the tube by its radius-slice description and use positivity of the radius function.
  rw [T.tube_eq]
  simpa [normal_bundle_vector] using T.δ_pos x

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper: the inverse endpoint diffeomorphism sends a base point of `M` to the zero vector over
that point. -/
lemma endpointDiffeomorph_symm_inclusion_eq_zeroVector (T : TubularNeighborhood n m M) (x : M) :
    T.endpointDiffeomorph.symm (Set.inclusion T.contains_base x) =
      ⟨Bundle.TotalSpace.mk x (0 : N[n, m; M; x]), zeroVector_mem_tube T x⟩ := by
  -- Compare the two candidate preimages after applying the endpoint diffeomorphism.
  apply T.endpointDiffeomorph.injective
  change
    T.endpointDiffeomorph (T.endpointDiffeomorph.symm (Set.inclusion T.contains_base x)) =
      T.endpointDiffeomorph ⟨Bundle.TotalSpace.mk x (0 : N[n, m; M; x]), zeroVector_mem_tube T x⟩
  rw [T.endpointDiffeomorph.apply_symm_apply]
  -- The endpoint map fixes the zero section, so both points are the same base point in `T`.
  ext
  rw [T.endpointDiffeomorph_eq]
  simp [NormalBundle.endpointMap, normal_bundle_vector]

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper: the canonical map associated to a tubular neighborhood is a retraction of the canonical
subset inclusion `M ↪ T.neighborhood`. -/
theorem retraction_leftInverse (T : TubularNeighborhood n m M) :
    Function.LeftInverse T.retraction (Set.inclusion T.contains_base) := by
  intro x
  -- Project the identified zero-vector preimage back to the original base point.
  have hzero :
      (T.endpointDiffeomorph.symm (Set.inclusion T.contains_base x) : NM[n, m; M]) =
        Bundle.TotalSpace.mk x (0 : N[n, m; M; x]) := by
    exact congrArg Subtype.val (endpointDiffeomorph_symm_inclusion_eq_zeroVector T x)
  simpa [retraction_apply] using congrArg Bundle.TotalSpace.proj hzero

/-- Helper: the normal-bundle projection remains a smooth submersion after restricting its domain
to the open tube of a tubular neighborhood. -/
theorem tubeProjection_isSmoothSubmersion
    (h_toProd :
      IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M))
    (T : TubularNeighborhood n m M) :
    IsSmoothSubmersion (𝓡 n) (𝓡 m) (fun p : T.tube ↦ π_NM[n, m; M] p) := sorry

/-- Helper: the canonical map associated to a tubular neighborhood is a smooth submersion. -/
theorem retraction_isSmoothSubmersion
    (h_toProd :
      IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M))
    (T : TubularNeighborhood n m M) :
    IsSmoothSubmersion (𝓡 n) (𝓡 m) T.retraction := by
  -- Transport the restricted smooth-submersion property across the inverse endpoint diffeomorphism.
  have h_symm : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ T.endpointDiffeomorph.symm := by
    simpa using Diffeomorph.isLocalDiffeomorph T.endpointDiffeomorph.symm
  simpa [retraction_apply, Function.comp] using
    (Manifold.IsSmoothSubmersion.comp_isLocalDiffeomorph
      (T.tubeProjection_isSmoothSubmersion h_toProd) h_symm)

end NormalBundle.TubularNeighborhood

end TubularNeighborhoodRetraction

section TubularNeighborhoodRetractionCanonical

variable {n m : ℕ}
variable {M : Set (EuclideanSpace ℝ (Fin n))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
variable [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
variable [NormalBundle.CompatibleSmoothStructure n m M]

-- Semantic recall note: `lean_leansearch` only surfaced generic `Manifold.IsSmoothEmbedding` API,
-- so this item stays source-facing for a tubular neighborhood and its canonical retraction,
-- while the normal-bundle smooth-structure compatibility remains internal helper data above.
/-- Proposition 6.25. Let `M ⊆ ℝ^n` be an embedded submanifold. If `T` is a tubular neighborhood
of `M`, there exists a smooth map `r : T.neighborhood → M` that is both a retraction and a
smooth submersion. -/
theorem tubular_neighborhood_has_retraction_and_smooth_submersion
    (T : NormalBundle.TubularNeighborhood n m M) :
    Function.LeftInverse T.retraction (Set.inclusion T.contains_base) ∧
      IsSmoothSubmersion (𝓡 n) (𝓡 m) T.retraction := sorry

/-- Companion corollary: the canonical tubular retraction yields the existential formulation of
Proposition 6.25. -/
theorem tubular_neighborhood_exists_retraction_and_smooth_submersion
    (T : NormalBundle.TubularNeighborhood n m M) :
    ∃ r : T.neighborhood → M,
      Function.LeftInverse r (Set.inclusion T.contains_base) ∧
        IsSmoothSubmersion (𝓡 n) (𝓡 m) r := sorry

end TubularNeighborhoodRetractionCanonical

end
