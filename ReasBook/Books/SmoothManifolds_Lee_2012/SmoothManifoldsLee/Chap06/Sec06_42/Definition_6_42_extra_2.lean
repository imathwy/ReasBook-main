import Mathlib.Geometry.Manifold.Diffeomorph
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_1
import SmoothManifolds_Lee_2012.Chap06.Sec06_42.Definition_6_42_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped ContDiff Manifold NormalBundle

universe u

noncomputable section

section TubularNeighborhoods

variable (n m : ℕ)
variable (M : Set (EuclideanSpace ℝ (Fin n)))
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]

-- Domain sampling pass: the target declarations lie in the normal-bundle / embedded-submanifold
-- manifold domain. The owner abstraction is the canonical carrier `NM[n, m; M]` from
-- `Definition_6_42_extra_1`; the relevant upstream declarations are:
-- `normal_bundle`,
-- `Bundle.TotalSpace.proj`,
-- `normal_bundle_inclusion`,
-- and `Manifold.IsSmoothEmbedding`.
-- Primitive data in this file is the source-facing endpoint map / radius-cut construction and the
-- tubular-neighborhood data built on the canonical normal-bundle owner `NM[n, m; M]`.
-- The smooth structure on an open tube is derived from the ambient normal bundle, not stored as
-- extra owner fields.

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Bridge/view: the canonical Euclidean representative of a normal vector in the total space of
the normal bundle. -/
abbrev normal_bundle_vector
    (v : NM[n, m; M]) : EuclideanSpace ℝ (Fin n) :=
  (NormedSpace.fromTangentSpace (v.proj : EuclideanSpace ℝ (Fin n)) :
    TangentSpace (𝓡 n) (v.proj : EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n)) v.snd

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Bridge/view: the canonical Euclidean coordinates on the normal bundle total space record the
base point in `M ⊆ ℝ^n` together with the ambient Euclidean representative of the normal vector. -/
abbrev normal_bundle_toProd
    (v : NM[n, m; M]) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  ((v.proj : EuclideanSpace ℝ (Fin n)), normal_bundle_vector n m M v)

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
@[simp] theorem normal_bundle_toProd_fst
    (v : NM[n, m; M]) :
    (normal_bundle_toProd n m M v).1 = (v.proj : EuclideanSpace ℝ (Fin n)) := rfl

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
@[simp] theorem normal_bundle_toProd_snd
    (v : NM[n, m; M]) :
    (normal_bundle_toProd n m M v).2 = normal_bundle_vector n m M v := rfl

namespace NormalBundle

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Definition 6.42-extra-2: the endpoint map of the normal bundle sends `(x, v)` to
`x + v`. -/
def endpointMap : NM[n, m; M] → EuclideanSpace ℝ (Fin n) :=
  fun p ↦ (p.proj : EuclideanSpace ℝ (Fin n)) + normal_bundle_vector n m M p

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- The endpoint map is given by vector addition in the ambient Euclidean space. -/
@[simp] theorem endpointMap_apply (p : NM[n, m; M]) :
    endpointMap n m M p = (p.proj : EuclideanSpace ℝ (Fin n)) + normal_bundle_vector n m M p :=
  rfl

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- The radius-cut subset `{(x, v) : ‖v‖ < δ(x)}` of the normal bundle. -/
def radiusSlice (δ : M → ℝ) : Set (NM[n, m; M]) :=
  {p | ‖normal_bundle_vector n m M p‖ < δ p.proj}

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Membership in the radius-cut subset is exactly the norm inequality from equation `(6.4)`. -/
@[simp] theorem mem_radiusSlice_iff (δ : M → ℝ) (p : NM[n, m; M]) :
    p ∈ radiusSlice n m M δ ↔ ‖normal_bundle_vector n m M p‖ < δ p.proj :=
  Iff.rfl

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Definition 6.42-extra-2 (2): the endpoint map is smooth as the restriction of the addition map
on `ℝ^n × ℝ^n` to the embedded submanifold `NM`. -/
theorem contMDiff_endpointMap
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (h_toProd :
      IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M)) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (endpointMap n m M) := by
  -- The normal-bundle coordinate map is smooth because a smooth embedding is an immersion.
  have hSmoothToProd :
      ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M) :=
    h_toProd.isImmersion.contMDiff
  -- Compose the ambient addition map with the normal-bundle coordinates and simplify.
  simpa [endpointMap, normal_bundle_toProd] using
    (contMDiff_add (𝓡 n) ∞).comp hSmoothToProd

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
variable [IsManifold (𝓡 n) ∞ (NM[n, m; M])]

/-- Helper for Definition 6.42-extra-2: a tubular neighborhood of `M` is an open neighborhood of
`M` in `ℝ^n` obtained from the endpoint map on an open tube of the form `{(x, v) : ‖v‖ < δ(x)}`
for some positive continuous radius function `δ`, where the tube carries the canonical smooth
structure inherited from the ambient normal bundle `NM[n, m; M]`. -/
structure TubularNeighborhood where
  /-- The open neighborhood of `M` in `ℝ^n`. -/
  neighborhood : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))
  /-- The continuous positive radius function cutting out the tube in the normal bundle. -/
  δ : M → ℝ
  /-- The radius function is continuous on the base manifold. -/
  δ_continuous : Continuous δ
  /-- The radius function is pointwise positive. -/
  δ_pos (x : M) : 0 < δ x
  /-- The chosen open subset of the normal bundle on which the endpoint map is a diffeomorphism. -/
  tube : TopologicalSpace.Opens (NM[n, m; M])
  /-- The tube has the textbook form `‖v‖ < δ(x)`. -/
  tube_eq : (tube : Set (NM[n, m; M])) = radiusSlice n m M δ
  /-- The resulting open set is genuinely a neighborhood of the base set `M`. -/
  contains_base : M ⊆ neighborhood
  /-- The endpoint map identifies the chosen open tube diffeomorphically with the neighborhood. -/
  endpointDiffeomorph : tube ≃ₘ⟮𝓡 n, 𝓡 n⟯ neighborhood
  /-- The diffeomorphism is realized pointwise by the endpoint map. -/
  endpointDiffeomorph_eq (p : tube) :
    (endpointDiffeomorph p : EuclideanSpace ℝ (Fin n)) = endpointMap n m M p

/-- A tubular neighborhood coerces to its underlying open neighborhood in `ℝ^n`. -/
instance : CoeOut (TubularNeighborhood n m M)
    (TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) where
  coe T := T.neighborhood

/-- A tubular neighborhood inherits membership from its underlying open neighborhood in `ℝ^n`. -/
instance : Membership (EuclideanSpace ℝ (Fin n)) (TubularNeighborhood n m M) where
  mem T x := x ∈ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n)))

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Membership in a tubular neighborhood means membership in its underlying open subset. -/
@[simp] theorem mem_tubularNeighborhood_iff
    {T : TubularNeighborhood n m M} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ T ↔ x ∈ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))) := Iff.rfl

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- The chosen open tube of a tubular neighborhood has the radius-cut form from equation `(6.4)`. -/
theorem tube_eq_radiusSlice (T : TubularNeighborhood n m M) :
    (T.tube : Set (NM[n, m; M])) = radiusSlice n m M T.δ :=
  T.tube_eq

end NormalBundle

end TubularNeighborhoods
