import Mathlib
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Notation_5_35_extra_1

open Manifold
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

section EuclideanNormalBundle

variable (n m : ℕ)
variable (M : Set (EuclideanSpace ℝ (Fin n)))
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]

-- Domain sampling pass: this file lies in the embedded-submanifold / tangent-space / bundle
-- domain.
-- Relevant owner declarations checked before refinement:
-- `Manifold.submanifoldTangentSpace` (`T[J; p]`) for the tangent space of the chosen subtype
-- manifold inside the ambient tangent space,
-- `Bundle.TotalSpace.proj` for the canonical bundle projection,
-- and `NormedSpace.fromTangentSpace` for the Euclidean identification of ambient tangent spaces.
-- Source/core/bridge triage:
-- * source-facing owner data: the chosen smooth manifold structure on the subtype `M`;
-- * source-facing constructions in this file: `normal_space` and `normal_bundle`;
-- * bridge/view API: `normal_bundle_inclusion` into the ambient tangent bundle.
-- Primitive data is the chosen smooth structure on the subtype; the normal-space and normal-bundle
-- API are derived from that owner, and the embedded-submanifold predicate is not needed for these
-- linear-algebraic constructions.

/-- Helper for Definition 6.42-extra-1: for a chosen smooth
`m`-dimensional manifold structure on the
subset `M ⊆ ℝ^n`, the normal space at `x : M` is the subspace of `Tₓℝ^n` consisting of vectors
orthogonal to the tangent space `TₓM`, where orthogonality is computed after the canonical
identification `Tₓℝ^n ≃ ℝ^n` given by `NormedSpace.fromTangentSpace`. -/
def normal_space (x : M) :
    Submodule ℝ (TangentSpace (𝓡 n) (x : EuclideanSpace ℝ (Fin n))) :=
  let e :
      TangentSpace (𝓡 n) (x : EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n))).toLinearMap
  (((T[𝓡 m; x]).map e)ᗮ).comap e

namespace NormalBundle

/- Source-facing notation for the textbook normal-space object `NₓM`. -/
scoped notation "N[" n ", " m "; " M "; " x "]" => normal_space n m M x

end NormalBundle

open scoped NormalBundle

omit [IsManifold (𝓡 m) ∞ M] in
/-- Definition 6.42-extra-1: a tangent vector lies in the normal space exactly when it is
orthogonal to every tangent vector
of the submanifold at the same base point, using the Euclidean inner product on `ℝ^n`. -/
theorem mem_normal_space_iff (x : M)
    (v : TangentSpace (𝓡 n) (x : EuclideanSpace ℝ (Fin n))) :
    v ∈ N[n, m; M; x] ↔
      ∀ w ∈ T[𝓡 m; x],
        inner ℝ
            (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n)) v)
            (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n)) w) = 0 := by
  let e :
      TangentSpace (𝓡 n) (x : EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n))).toLinearMap
  -- Rewrite the normal-space definition through the Euclidean identification of `Tₓℝⁿ`.
  change e v ∈ ((T[𝓡 m; x]).map e)ᗮ ↔
      ∀ w ∈ T[𝓡 m; x], inner ℝ (e v) (e w) = 0
  -- Turn orthogonal-complement membership into the textbook pointwise orthogonality condition.
  rw [Submodule.mem_orthogonal']
  constructor
  · intro hv w hw
    -- Push tangent vectors into the mapped tangent subspace before applying orthogonality.
    exact hv (e w) (Submodule.mem_map_of_mem hw)
  · intro hv y hy
    -- Pull vectors in the mapped tangent space back to genuine tangent vectors.
    rcases Submodule.mem_map.mp hy with ⟨w, hw, rfl⟩
    exact hv w hw

/-- Helper for Definition 6.42-extra-1: for a chosen smooth
`m`-dimensional manifold structure on the
subset `M ⊆ ℝ^n`, the normal bundle of `M` is the family of normal vectors over the points of `M`,
equivalently the subset of the ambient tangent bundle `Tℝ^n ≃ ℝ^n × ℝ^n` consisting of pairs
`(x, v)` with `x ∈ M` and `v ∈ NₓM`. -/
abbrev normal_bundle :=
  Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) (fun x : M ↦ ↥(normal_space n m M x))

namespace NormalBundle

/- Source-facing notation for the textbook bundle objects `NM` and `π_NM`. -/
scoped notation "NM[" n ", " m "; " M "]" => normal_bundle n m M
scoped notation "π_NM[" n ", " m "; " M "]" =>
  (Bundle.TotalSpace.proj : normal_bundle n m M → M)

end NormalBundle

/-
A point of the normal bundle carries a vector in the normal space over its base point.
-/
omit [IsManifold (𝓡 m) ∞ M] in
theorem normal_bundle_vector_mem (v : NM[n, m; M]) :
    (v.snd : TangentSpace (𝓡 n) (v.proj : EuclideanSpace ℝ (Fin n))) ∈ N[n, m; M; v.proj] :=
  v.snd.property

omit [IsManifold (𝓡 m) ∞ M] in
/-- The normal bundle carries the tautological inclusion into the ambient tangent bundle `Tℝ^n`. -/
abbrev normal_bundle_inclusion :
    NM[n, m; M] → TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)) :=
  fun v ↦ ⟨(v.proj : EuclideanSpace ℝ (Fin n)), v.snd⟩

omit [IsManifold (𝓡 m) ∞ M] in
/-- The normal bundle inherits the subspace topology from its tautological inclusion into the
ambient tangent bundle. -/
instance instTopologicalSpaceNormalBundle : TopologicalSpace (NM[n, m; M]) :=
  TopologicalSpace.induced (normal_bundle_inclusion n m M) inferInstance

/-
The inclusion of the normal bundle into the ambient tangent bundle preserves the base point.
-/
omit [IsManifold (𝓡 m) ∞ M] in
@[simp] theorem normal_bundle_inclusion_proj (v : NM[n, m; M]) :
    (normal_bundle_inclusion n m M v).proj = (v.proj : EuclideanSpace ℝ (Fin n)) := rfl

/- Definition 6.42-extra-1 (3): the natural projection `π_NM : NM → M` is the canonical total-space
projection `Bundle.TotalSpace.proj`. -/
recall Bundle.TotalSpace.proj

end EuclideanNormalBundle
