import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_7_1 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for planar `[p, q]` maps with disc-or-annulus component
decompositions.

Layer triage:
- `source-facing`: `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents`,
  expressing that the planar map itself admits a finite connected-component decomposition whose
  pieces are either simply connected or annular in the induced planar embedding.
- `core/canonical`: `TwoComplex.Subcomplex.IsComponentDecomposition` is the owner abstraction for
  the primitive component data, while `TwoComplex.IsSimplyConnected`,
  `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles`, and
  `TwoComplex.TwoManifoldEmbedding.boundaryVertexAdjustedDefectSum` are the owner predicates and
  construction used by the theorem.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1`
  is the owner restriction bridge to the induced embedding on each listed component.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents` from Lemma `5-6-1`
   is the source-facing owner for the finite disc-or-annulus component hypothesis.
2. `TwoComplex.Subcomplex.IsComponentDecomposition` from Proposition `3-9-1` is the owner
   abstraction for the finite component decomposition.
3. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1` is the owner
   restriction bridge to a component embedding.
4. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for the simply
   connected branch.
5. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the owner
   predicate for the annular branch.
6. `TwoComplex.TwoManifoldEmbedding.boundaryVertexAdjustedDefectSum` from Theorem `5-3-2` is the
   owner construction for the boundary curvature sum in the conclusion.

Primitive vs. derived:
- primitive public data: the planar embedding `embedding`, positive integers `p` and `q`
  satisfying `1 / p + 1 / q = 1 / 2`, the `[p, q]` hypothesis, and the existence of a finite
  component decomposition of the ambient map whose pieces satisfy one of the two owner
  component-shape
  hypotheses;
- derived API: the lower bound `0 ≤ embedding.boundaryVertexAdjustedDefectSum p q`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: choose the component decomposition from
-- `embedding.HasSimplyConnectedOrAnnularComponents`. Apply the simply connected
-- boundary-curvature estimate to each disc component and the annular analogue to each annular
-- component via the owner restricted embedding `embedding.restrictToSubcomplex (components i)`.
-- Summing the componentwise inequalities gives a nonnegative total boundary curvature sum for the
-- whole map.
/-- Lemma 5-7-1: if a `[p, q]` map admits a finite connected-component decomposition in which each
component is either simply connected or annular in the induced restricted embedding, then the
curvature sum `∑_M [p / q + 2 - d(v)]`, represented here by
`boundaryVertexAdjustedDefectSum p q`, is nonnegative. -/
theorem boundaryVertexAdjustedDefectSum_nonnegative_of_hasSimplyConnectedOrAnnularComponents
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2) (hPQ : embedding Is[p, q])
    (hcomponents : embedding.HasSimplyConnectedOrAnnularComponents) :
    0 ≤ embedding.boundaryVertexAdjustedDefectSum p q := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Lemma_5_7_2 (from Items/Chap05) -/
set_option autoImplicit false

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: duality of planar maps after deleting boundary layers.

Layer triage:
- `source-facing`: a planar map `embedding`, a dual planar map `dualEmbedding`, and the induced
  deleted maps obtained by restricting both embeddings to chosen boundary-layer complements.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsDualMap` is the chapter owner for dual
  planar maps, while `TwoComplex.Duality` is the underlying owner for the ambient vertex-face-edge
  duality data.
- `bridge/view`: `TwoComplex.Subcomplex.IsBoundaryLayerComplement` records that `S` is exactly the
  carried complement of the deleted boundary layer, while
  `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` is the canonical bridge to the induced
  submap, and `TwoComplex.TwoManifoldEmbedding.boundaryLayerRemoval_preservesDuality` is the
  canonical restricted-duality construction on the deleted maps.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsDualMap` from `Corollary_5_7_3` is the best owner
   abstraction for the source claim that one planar map is dual to another.
2. `TwoComplex.Subcomplex.IsBoundaryLayerComplement` from `Corollary_5_7_3` is the chapter owner
   for the carried subcomplex left after deleting the boundary layer.
3. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from `Definition_5_1_1` is the canonical
   bridge from a chosen carried subcomplex to the induced planar embedding on that submap.
4. `TwoComplex.TwoManifoldEmbedding.boundaryLayerRemoval_preservesDuality` from
   `Corollary_5_7_3` is the upstream owner construction for the restricted duality on the two
   deleted maps, so this file should reuse that data instead of keeping an existential wrapper.

Primitive vs. derived:
- primitive public data: the planar embeddings `embedding` and `dualEmbedding`, the chosen
  boundary-layer complements `S` and `SStar`, and the source duality/removal hypotheses;
- derived API: the direct `IsDualMap` witness for the two induced deleted maps, built from the
  canonical restricted `TwoComplex.Duality`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C K : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) (dualEmbedding : TwoManifoldEmbedding K 𝔼²)
variable (hdual : embedding.IsDualMap dualEmbedding)
variable (S : Subcomplex C) (hS : S.IsBoundaryLayerComplement embedding)
variable (SStar : Subcomplex K) (hSStar : SStar.IsBoundaryLayerComplement dualEmbedding)

/- Lemma 5-7-2: deleting the boundary layers on both sides of a dual pair yields deleted maps
that are again dual.

`Corollary_5_7_3` already provides the exact source-facing deleted-map witness with the canonical
owner abstraction and without an existential wrapper, so this file keeps only a direct recall of
that declaration instead of a parallel local copy. -/
#check
  (boundaryLayerRemoval_preservesDuality embedding dualEmbedding hdual S hS SStar hSStar :
    (embedding.restrictToSubcomplex S).IsDualMap
      (dualEmbedding.restrictToSubcomplex SStar))

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Corollary_5_7_3 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: duality of planar maps after removing boundary layers.

Layer triage:
- `source-facing`: a map `M`, a dual map `M*`, and the maps `M₁`, `M₁*` obtained by deleting the
  boundary layers of `M` and `M*`.
- `core/canonical`: `TwoComplex.Duality` is the project owner for the underlying duality data
  between the carried `2`-complexes, while the predicates
  `TwoManifoldEmbedding.IsInteriorVertex`, `TwoManifoldEmbedding.IsInteriorRegion`, and the
  boundary-layer edge owner `TwoManifoldEmbedding.IsBoundaryLayerEdge` describe the cells that
  survive or are deleted.
- `bridge/view`: `TwoComplex.Subcomplex.IsBoundaryLayerComplement` is the chapter bridge saying
  which carried subcomplex remains after deleting the boundary layer, and
  `TwoManifoldEmbedding.restrictToSubcomplex` is the canonical induced planar embedding on that
  carried deleted map.

Domain sampling:
1. `TwoComplex.Duality` from `Proposition_3_7_1` is the existing owner abstraction for the
   underlying vertex-face-edge duality between two `2`-complexes.
2. `TwoManifoldEmbedding.IsInteriorVertex` and `TwoManifoldEmbedding.IsInteriorRegion` from
   `Definition_5_2_7` are the existing owner predicates for the surviving vertices and regions.
3. `TwoManifoldEmbedding.IsBoundaryLayerEdge` from `Definition_5_6_2` is the existing chapter
   owner predicate for the deleted geometric edges.
4. `TwoManifoldEmbedding.restrictToSubcomplex` from `Definition_5_1_1` is the canonical bridge
   from a carried subcomplex to the induced deleted planar map.

Primitive vs. derived:
- primitive public data: two planar embeddings, an explicit dual-map witness carrying the ambient
  `TwoComplex.Duality`, and explicit carried subcomplexes `S`, `SStar` with the two complement
  hypotheses;
- derived API: the statement that the ambient duality restricts to the carried deleted maps left
  after removing those boundary layers.
-/

namespace TwoComplex

private def equivSubtype
    {α β : Type*} (e : α ≃ β) (p : α → Prop) (q : β → Prop)
    (h : ∀ a, p a ↔ q (e a)) :
    {a // p a} ≃ {b // q b} where
  toFun a := ⟨e a.1, (h a.1).1 a.2⟩
  invFun b := ⟨e.symm b.1, by
    have : q (e (e.symm b.1)) := by simpa using b.2
    exact (h (e.symm b.1)).2 this⟩
  left_inv a := by
    ext
    exact e.symm_apply_apply a.1
  right_inv b := by
    ext
    exact e.apply_symm_apply b.1

namespace Subcomplex

section

variable {C : TwoComplex}

/-- A chosen carried subcomplex is a complement of the boundary layer when its carried vertices,
geometric edges, and geometric faces are exactly the interior vertices, the geometric edges not
in the boundary layer, and the interior regions of the ambient planar map. -/
def IsBoundaryLayerComplement (S : Subcomplex C) (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  (∀ v : C.skeleton, v ∈ S.skeleton.vertexSet ↔ embedding.IsInteriorVertex v) ∧
    (∀ e : OneComplex.GeometricEdge C.skeleton,
      S.skeleton.ContainsGeometricEdge e ↔ ¬ embedding.IsBoundaryLayerEdge e) ∧
      (∀ D : GeometricFace C, S.ContainsGeometricFace D ↔ embedding.IsInteriorRegion D)

namespace IsBoundaryLayerComplement

theorem mem_vertexSet_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (v : C.skeleton) :
    v ∈ S.skeleton.vertexSet ↔ embedding.IsInteriorVertex v := by
  rcases hS with ⟨hvertex, _, _⟩
  exact hvertex v

theorem mem_edgeSet_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (e : C.skeleton.Edge) :
    e ∈ S.skeleton.edgeSet ↔ ¬ embedding.IsBoundaryLayerEdge ⟦e⟧ := by
  rcases hS with ⟨_, hedge, _⟩
  simpa using hedge (⟦e⟧ : OneComplex.GeometricEdge C.skeleton)

theorem mem_faceSet_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (D : C.Face) :
    D ∈ S.faceSet ↔ embedding.IsInteriorRegion (⟦D⟧ : GeometricFace C) := by
  rcases hS with ⟨_, _, hface⟩
  simpa using hface (⟦D⟧ : GeometricFace C)

theorem mem_geometricEdge_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding)
    (e : OneComplex.GeometricEdge C.skeleton) :
    S.skeleton.ContainsGeometricEdge e ↔ ¬ embedding.IsBoundaryLayerEdge e := by
  rcases hS with ⟨_, hedge, _⟩
  exact hedge e

theorem mem_geometricFace_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (D : GeometricFace C) :
    S.ContainsGeometricFace D ↔ embedding.IsInteriorRegion D := by
  rcases hS with ⟨_, _, hface⟩
  exact hface D

end IsBoundaryLayerComplement

private noncomputable def ambientGeometricFaceEquiv (S : Subcomplex C) :
    GeometricFace S.complex ≃ {D : GeometricFace C // S.ContainsGeometricFace D} where
  toFun :=
    Quotient.lift
      (fun D : S.complex.Face ↦
        ⟨(⟦D.1⟧ : GeometricFace C), by
          exact (S.containsGeometricFace_mk_iff D.1).2 D.2⟩)
      (fun D E h ↦ by
        apply Subtype.ext
        apply Quotient.sound
        rcases h with h | h
        · left
          exact congrArg Subtype.val h
        · right
          simpa using congrArg Subtype.val h)
  invFun D := by
    let E : C.Face := Quotient.out D.1
    have hE : S.ContainsGeometricFace (⟦E⟧ : GeometricFace C) := by
      simpa [E] using D.2
    exact ⟦⟨E, (S.containsGeometricFace_mk_iff E).1 hE⟩⟧
  left_inv := by
    sorry
  right_inv := by
    sorry

private noncomputable def ambientGeometricEdgeEquiv (S : Subcomplex C) :
    OneComplex.GeometricEdge S.complex.skeleton ≃
      {e : OneComplex.GeometricEdge C.skeleton // S.skeleton.ContainsGeometricEdge e} where
  toFun :=
    Quotient.lift
      (fun e ↦
        ⟨(⟦e.1⟧ : OneComplex.GeometricEdge C.skeleton), by
          exact (S.skeleton.containsGeometricEdge_mk_iff e.1).2 e.2⟩)
      (fun e f h ↦ by
        apply Subtype.ext
        apply Quotient.sound
        rcases h with h | h
        · left
          exact congrArg Subtype.val h
        · right
          simpa using congrArg Subtype.val h)
  invFun e := by
    let f : C.skeleton.Edge := Quotient.out e.1
    have hf : S.skeleton.ContainsGeometricEdge (⟦f⟧ : OneComplex.GeometricEdge C.skeleton) := by
      simpa [f] using e.2
    exact ⟦⟨f, (S.skeleton.containsGeometricEdge_mk_iff f).1 hf⟩⟧
  left_inv := by
    sorry
  right_inv := by
    sorry

end

end Subcomplex

namespace TwoManifoldEmbedding

section

variable {C K : TwoComplex}

/-- A planar map `dualEmbedding` is a dual of `embedding` when it comes equipped with a
`TwoComplex.Duality` whose vertex-face, face-vertex, and edge correspondences exchange the two
boundary layers. -/
structure IsDualMap
    (embedding : TwoManifoldEmbedding C 𝔼²) (dualEmbedding : TwoManifoldEmbedding K 𝔼²) where
  /-- The underlying duality between the carried `2`-complexes. -/
  duality : TwoComplex.Duality C K
  /-- Boundary vertices correspond to boundary regions under the duality. -/
  vertex_boundary_iff (v : C.skeleton) :
      embedding.IsBoundaryVertex v ↔
        dualEmbedding.IsBoundaryRegion (duality.vertexToFace v)
  /-- Boundary regions correspond to boundary vertices under the duality. -/
  region_boundary_iff (D : GeometricFace C) :
      embedding.IsBoundaryRegion D ↔
        dualEmbedding.IsBoundaryVertex (duality.faceToVertex D)
  /-- Boundary-layer edges correspond to boundary-layer edges under the duality. -/
  edge_boundary_iff (e : OneComplex.GeometricEdge C.skeleton) :
      embedding.IsBoundaryLayerEdge e ↔
        dualEmbedding.IsBoundaryLayerEdge (duality.edgeToEdge e)

namespace IsDualMap

theorem interiorVertex_iff
    {embedding : TwoManifoldEmbedding C 𝔼²} {dualEmbedding : TwoManifoldEmbedding K 𝔼²}
    (hdual : embedding.IsDualMap dualEmbedding) (v : C.skeleton) :
    embedding.IsInteriorVertex v ↔
      dualEmbedding.IsInteriorRegion (hdual.duality.vertexToFace v) := by
  simpa [IsInteriorVertex, IsInteriorRegion] using
    not_congr (hdual.vertex_boundary_iff v)

theorem interiorRegion_iff
    {embedding : TwoManifoldEmbedding C 𝔼²} {dualEmbedding : TwoManifoldEmbedding K 𝔼²}
    (hdual : embedding.IsDualMap dualEmbedding) (D : GeometricFace C) :
    embedding.IsInteriorRegion D ↔
      dualEmbedding.IsInteriorVertex (hdual.duality.faceToVertex D) := by
  simpa [IsInteriorRegion, IsInteriorVertex] using
    not_congr (hdual.region_boundary_iff D)

theorem not_isBoundaryLayerEdge_iff
    {embedding : TwoManifoldEmbedding C 𝔼²} {dualEmbedding : TwoManifoldEmbedding K 𝔼²}
    (hdual : embedding.IsDualMap dualEmbedding)
    (e : OneComplex.GeometricEdge C.skeleton) :
    ¬ embedding.IsBoundaryLayerEdge e ↔
      ¬ dualEmbedding.IsBoundaryLayerEdge (hdual.duality.edgeToEdge e) := by
  simpa using not_congr (hdual.edge_boundary_iff e)

end IsDualMap

-- Proof sketch: restrict the ambient duality carried by `hdual` to the surviving vertices,
-- geometric edges, and geometric faces singled out by the carried boundary-layer complements. The
-- boundary-layer correspondence in `hdual` identifies those surviving cells on the two sides, and
-- the incidence-compatibility axiom of the ambient duality descends to the carried deleted maps.
/-- Corollary 5-7-3: if `embedding` is a map, `dualEmbedding` is a dual of it, and `S`, `SStar`
are the carried complements of the boundary layers of `embedding` and `dualEmbedding`, then the
induced deleted maps on `S` and `SStar` are themselves dual. The restricted ambient
`TwoComplex.Duality` is the underlying field of this source-facing dual-map witness. -/
def boundaryLayerRemoval_preservesDuality
    (embedding : TwoManifoldEmbedding C 𝔼²) (dualEmbedding : TwoManifoldEmbedding K 𝔼²)
    (hdual : embedding.IsDualMap dualEmbedding)
    (S : Subcomplex C) (hS : S.IsBoundaryLayerComplement embedding)
    (SStar : Subcomplex K) (hSStar : SStar.IsBoundaryLayerComplement dualEmbedding)
    : (embedding.restrictToSubcomplex S).IsDualMap
        (dualEmbedding.restrictToSubcomplex SStar) :=
  let Γ := S.skeleton
  let ΓStar := SStar.skeleton
  let faceEquiv := S.ambientGeometricFaceEquiv
  let faceEquivStar := SStar.ambientGeometricFaceEquiv
  let edgeEquiv := S.ambientGeometricEdgeEquiv
  let edgeEquivStar := SStar.ambientGeometricEdgeEquiv
  let restrictedDuality : TwoComplex.Duality S.complex SStar.complex :=
    { vertexToFace :=
        (equivSubtype hdual.duality.vertexToFace
          (fun v ↦ v ∈ Γ.vertexSet)
          (fun D ↦ SStar.ContainsGeometricFace D)
          fun v ↦ by
            simpa [Γ] using
              (hS.mem_vertexSet_iff v).trans
                ((hdual.interiorVertex_iff v).trans
                  (hSStar.mem_geometricFace_iff (hdual.duality.vertexToFace v)).symm)).trans
          faceEquivStar.symm
      faceToVertex :=
        faceEquiv.trans <|
          equivSubtype hdual.duality.faceToVertex
            (fun D ↦ S.ContainsGeometricFace D)
            (fun v ↦ v ∈ ΓStar.vertexSet)
            fun D ↦ by
              simpa [ΓStar] using
                (hS.mem_geometricFace_iff D).trans
                  ((hdual.interiorRegion_iff D).trans
                    (hSStar.mem_vertexSet_iff (hdual.duality.faceToVertex D)).symm)
      edgeToEdge :=
        edgeEquiv.trans <|
          (equivSubtype hdual.duality.edgeToEdge
            (fun e ↦ Γ.ContainsGeometricEdge e)
            (fun e ↦ ΓStar.ContainsGeometricEdge e)
            fun e ↦ by
              simpa [Γ, ΓStar] using
                (hS.mem_geometricEdge_iff e).trans
                  ((hdual.not_isBoundaryLayerEdge_iff e).trans
                    (hSStar.mem_geometricEdge_iff (hdual.duality.edgeToEdge e)).symm)).trans
            edgeEquivStar.symm
      vertexOnFace_iff := by
        sorry }
  { duality := restrictedDuality
    vertex_boundary_iff := by
      sorry
    region_boundary_iff := by
      sorry
    edge_boundary_iff := by
      sorry }

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Theorem_5_7_4 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: boundary-layer peeling for planar small-cancellation maps.

Layer triage:
- `source-facing`: a `(q, p)` map `M`, the iterated sequence obtained by repeatedly deleting the
  boundary layer, and the resulting bound on the largest boundary complexity `β(Mᵢ)`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner for `(q, p)`
  maps, `TwoComplex.TwoManifoldEmbedding.IsBoundaryLayerEdge` together with the interior predicates
  from Definition `5-2-7` are the owners for deleting a boundary layer, and
  `TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum`, with source-facing
  notation `σ'(M)[p, q]`, is the existing owner for the starred sum `σ'(M)`. The disc-or-annulus
  component hypothesis is owned by
  `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents` from Lemma `5-6-1`.
- `bridge/view`: the source quantity `β(M)` is realized as the number of boundary regions, while
  the successive maps `M₀, ..., M_k` are represented by an inductive boundary-layer deletion
  sequence built from carried subcomplexes and their induced planar embeddings; the relation
  `TwoComplex.Subcomplex.IsBoundaryLayerComplement` is the thin bridge saying which subcomplex is
  kept at each step.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum` from
   `Corollary_5_3_5`, with notation `σ'(M)[p, q]`, is the established owner for the source sum
   `σ'(M)`.
2. `TwoComplex.Subcomplex.IsBoundaryLayerComplement` from `Corollary_5_7_3` is the bridge/view
   predicate expressing that a chosen subcomplex is the complement of the boundary layer.
3. `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents` from Lemma `5-6-1` is
   the chapter owner for the disc-or-annulus component hypothesis.
4. `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` from `Definition_5_3_1` is the owner for
   the source `(q, p)` hypothesis.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- The source quantity `β(M)`, realized as the number of boundary regions of a finite planar
map and viewed in `ℚ`. -/
abbrev boundaryRegionCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card { D : GeometricFace C // embedding.IsBoundaryRegion D }

/-- Source-facing notation for the textbook quantity `β(M)`. -/
syntax:max "β(" term:max ")" : term

macro_rules
  | `(β($embedding)) => `(TwoComplex.TwoManifoldEmbedding.boundaryRegionCount $embedding)

/-- A planar map is equal to its boundary layer when every vertex, geometric edge, and region is
already part of that boundary layer. -/
def BoundaryLayerEqualsMap (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  (∀ v : C.skeleton, ¬ embedding.IsInteriorVertex v) ∧
    (∀ e : OneComplex.GeometricEdge C.skeleton, embedding.IsBoundaryLayerEdge e) ∧
      ∀ D : GeometricFace C, ¬ embedding.IsInteriorRegion D

/-- A boundary-layer deletion sequence starts from a planar map and repeatedly replaces the
current map by the carried subcomplex obtained from it by deleting the boundary layer, stopping
when the final map is equal to its own boundary layer. -/
inductive BoundaryLayerDeletionSequence :
    {C : TwoComplex} → TwoManifoldEmbedding C 𝔼² → ℕ → Type _
  | terminal {C : TwoComplex} {embedding : TwoManifoldEmbedding C 𝔼²}
      (hterminal : embedding.BoundaryLayerEqualsMap) :
      BoundaryLayerDeletionSequence embedding 0
  | step {C : TwoComplex} {embedding : TwoManifoldEmbedding C 𝔼²} {k : ℕ}
      (S : Subcomplex C) (hS : S.IsBoundaryLayerComplement embedding)
      (tail : BoundaryLayerDeletionSequence (embedding.restrictToSubcomplex S) k) :
      BoundaryLayerDeletionSequence embedding (k + 1)

namespace BoundaryLayerDeletionSequence

/-- The maximum of the source quantities `β(Mᵢ)` along a boundary-layer deletion sequence,
realized as the maximum boundary-region count among its stages. -/
def maxBoundaryRegionCount
    {C : TwoComplex} {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] :
    {k : ℕ} → BoundaryLayerDeletionSequence embedding k → ℚ
  | _, .terminal _ => β(embedding)
  | _, .step _ _ tail => max (β(embedding)) tail.maxBoundaryRegionCount

end BoundaryLayerDeletionSequence

-- Proof sketch: first pass to a dual boundary-layer deletion sequence and use Corollary `5-7-3`
-- to keep duality after each peeling step. Lemma `5-7-1` gives monotonicity of the corresponding
-- dual boundary-vertex sum under each deletion, so the initial starred sum `σ'(M)` dominates the
-- starred sums of all later stages. Duality identifies `β(Mᵢ)` with the boundary-vertex count of
-- the dual stage, and the boundary-count estimate from Lemma `5-6-1` then yields the stated
-- factor `q / p`.
/-- Theorem 5-7-4: if `M` is a `(q, p)` map whose connected components are each simply connected
or annular, and `M = M₀, M₁, ..., M_k` is a sequence obtained by repeatedly deleting the boundary
layer until the last map is equal to its own boundary layer, then the maximum of the source
quantities `β(Mᵢ)` is bounded by `(q / p) σ'(M)`, represented here by
`((q : ℚ) / p) * σ'(embedding)[p, q]` for the initial map and by
`maxBoundaryRegionCount` for the boundary-layer deletion sequence. -/
theorem maxBoundaryRegionCount_le_scaled_sigmaPrime_of_boundaryLayerDeletionSequence
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hQP : embedding Is(q, p))
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hcomponents : embedding.HasSimplyConnectedOrAnnularComponents)
    {k : ℕ} (sequence : BoundaryLayerDeletionSequence embedding k) :
    sequence.maxBoundaryRegionCount ≤
      ((q : ℚ) / p) * σ'(embedding)[p, q] := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Lemma_5_7_5 (from Items/Chap05) -/
set_option autoImplicit false

open Quiver.Path
open OneComplex

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: annular planar maps after removing the boundary layer.

Layer triage:
- `source-facing`: an annular planar map `A`, the boundary-layer peeling construction producing
  `H`, and the exclusion of boundary linking pairs.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` is the owner of the planar map,
  `TwoManifoldEmbedding.HasAnnularBoundaryCycles` is the owner of annularity, and
  `TwoManifoldEmbedding.IsInteriorRegion` is the owner predicate for the faces remaining after the
  boundary layer is removed.
- `bridge/view`: `Subcomplex.IsBoundaryLayerComplement` is the existing chapter bridge for the
  chosen surviving subcomplex after deleting a boundary layer, `TwoManifoldEmbedding
  .restrictToSubcomplex` is the owner-side bridge to the induced embedding on that carried
  subcomplex, and `Subcomplex.ContainsGeometricFace`,
  `OneComplex.Subcomplex.ContainsGeometricEdge`, `TwoComplex.boundaryGeometricEdges`, and
  `TwoComplex.VertexOnFace` describe the extra gap-removal incidence conditions on the surviving
  `1`-skeleton. `TwoManifoldEmbedding.boundaryCycleSupport` and
  `TwoManifoldEmbedding.faceBoundarySupport` compare boundary regions with the chosen outer and
  inner boundary cycles.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the chapter
   owner for annular boundary data.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` and `IsInteriorRegion` from Definition `5-2-7`
   are the chapter owners for the boundary/interior face partition.
3. `TwoComplex.Subcomplex.IsBoundaryLayerComplement` from Corollary `5-7-3` is the existing
   chapter bridge for the chosen carried complement of the boundary layer, so the extra
   gap-removal content here should refine that owner rather than introduce a second
   embedding-owned predicate.
4. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1`, together with
   `Subcomplex.ContainsGeometricFace`, `OneComplex.Subcomplex.ContainsGeometricEdge`,
   `TwoComplex.boundaryGeometricEdges`, and `TwoComplex.VertexOnFace`, gives the canonical
   induced-subcomplex and incidence API for the peeled annular map.

Primitive vs. derived:
- primitive public data: the annular embedding, its chosen outer and inner boundary cycles, a
  chosen surviving subcomplex extending `Subcomplex.IsBoundaryLayerComplement` by the extra
  face-incidence conditions recording gap removal, and the boundary-linking-pair exclusion;
- derived API: annularity and region nonemptiness for the canonical restricted embedding of the
  peeled subcomplex.
-/

namespace TwoComplex
namespace Subcomplex

section

variable {C : TwoComplex}

/-- A chosen carried subcomplex is obtained by removing the boundary layer and its gaps when it is
already the chapter's canonical boundary-layer complement and its surviving geometric edges and
vertices are exactly those incident with the surviving faces. -/
def IsBoundaryLayerGapRemoval (H : Subcomplex C) (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  H.IsBoundaryLayerComplement embedding ∧
    (∀ e : GeometricEdge C.skeleton,
      H.skeleton.ContainsGeometricEdge e ↔
        ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ e ∈ C.boundaryGeometricEdges ⟦D⟧) ∧
      ∀ v : C.skeleton,
        v ∈ H.skeleton.vertexSet ↔
          ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ C.VertexOnFace v D

namespace IsBoundaryLayerGapRemoval

theorem toIsBoundaryLayerComplement
    {H : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hH : H.IsBoundaryLayerGapRemoval embedding) :
    H.IsBoundaryLayerComplement embedding :=
  hH.1

theorem mem_geometricEdge_iff
    {H : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hH : H.IsBoundaryLayerGapRemoval embedding) (e : GeometricEdge C.skeleton) :
    H.skeleton.ContainsGeometricEdge e ↔
      ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ e ∈ C.boundaryGeometricEdges ⟦D⟧ := by
  rcases hH with ⟨_, hedge, _⟩
  exact hedge e

theorem mem_vertexSet_iff
    {H : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hH : H.IsBoundaryLayerGapRemoval embedding) (v : C.skeleton) :
    v ∈ H.skeleton.vertexSet ↔
      ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ C.VertexOnFace v D := by
  rcases hH with ⟨_, _, hvertex⟩
  exact hvertex v

end IsBoundaryLayerGapRemoval

end

end Subcomplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- A boundary linking pair is a pair of boundary regions on opposite annular boundary components
whose boundary supports meet. This includes the degenerate case `D₁ = D₂`, corresponding to a
single region meeting both boundary components. -/
def IsBoundaryLinkingPair (embedding : TwoManifoldEmbedding C 𝔼²)
    (σ τ : CyclicPath C.skeleton) (D₁ D₂ : GeometricFace C) : Prop :=
  let onOuterBoundary (D : GeometricFace C) :=
    (embedding.faceBoundarySupport D ∩ embedding.boundaryCycleSupport σ).Nonempty
  let onInnerBoundary (D : GeometricFace C) :=
    (embedding.faceBoundarySupport D ∩ embedding.boundaryCycleSupport τ).Nonempty
  ((onOuterBoundary D₁ ∧ onInnerBoundary D₂) ∨
      (onInnerBoundary D₁ ∧ onOuterBoundary D₂)) ∧
    (embedding.faceBoundarySupport D₁ ∩ embedding.faceBoundarySupport D₂).Nonempty

-- Proof sketch: the no-linking-pair hypothesis separates the deleted boundary layer into an outer
-- shell and an inner shell, so deleting the boundary regions leaves a connected annular middle
-- submap. The restricted planar embedding of that induced interior-face subcomplex then carries
-- two disjoint boundary cycles, and at least one region survives because the peeled annulus
-- cannot collapse completely under the stated hypothesis.
/-- Lemma 5-7-5: if `A` is an annular planar map, `H` is the subcomplex obtained from `A` by
removing the boundary layer and its gaps, and `A` has no boundary linking pairs, then the induced
restricted embedding of `H.complex` is again annular and has at least one region. -/
theorem boundaryLayerGapRemoval_has_annularRealizationWithRegion_of_no_boundaryLinkingPairs
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (σ τ : CyclicPath C.skeleton) (hannular : embedding.HasAnnularBoundaryCycles σ τ)
    (H : Subcomplex C) (hH : H.IsBoundaryLayerGapRemoval embedding)
    (hnoLink :
      ∀ D₁ D₂ : GeometricFace C, ¬ embedding.IsBoundaryLinkingPair σ τ D₁ D₂) :
    ∃ σH τH : CyclicPath H.complex.skeleton,
      (embedding.restrictToSubcomplex H).HasAnnularBoundaryCycles σH τH ∧
        Nonempty (GeometricFace H.complex) := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Theorem_5_7_6 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open FreeGroupBasis

section

variable {X : Type u}

local instance instDecidableEqX_5_7_6 : DecidableEq X := Classical.decEq X

private abbrev basis : FreeGroupBasis X (FreeGroup X) := FreeGroupBasis.ofFreeGroup X

namespace GroupPresentation

/-!
Primary domain: algorithmic solvability of the conjugacy problem for small-cancellation quotients
of finitely generated free groups.

Layer triage:
- `source-facing`: a finitely generated free group `FreeGroup X`, a finite relator set `R`, one
  of the small-cancellation hypotheses `C(6)`, `C(4)` together with `T(4)`, or `C(3)` together
  with `T(6)`, and the conclusion that the quotient by the normal closure of `R` has solvable
  conjugacy problem.
- `core/canonical`: `HasSolvableConjugacyProblem R` is the chapter owner predicate for the
  conclusion, while `FreeGroupBasis.condition_c` and `FreeGroupBasis.condition_t` are the chapter
  owners for the small-cancellation hypotheses.
- `bridge/view`: `basis = FreeGroupBasis.ofFreeGroup X` is the canonical chosen basis used by the
  Chapter `5` small-cancellation surface `C(p)[basis, R]` and `T(q)[basis, R]`.

Domain sampling:
1. `GroupPresentation.HasSolvableConjugacyProblem R` from Definition `2-1-4` is the owner
   predicate for the conclusion.
2. `FreeGroupBasis.condition_c` from Definition `5-2-2`, with notation `C(p)[basis, R]`, is the
   owner predicate for the `C(p)` hypotheses.
3. `FreeGroupBasis.condition_t` from Definition `5-2-3`, with notation `T(q)[basis, R]`, is the
   owner predicate for the `T(q)` hypotheses; it now reads those hypotheses on the symmetrized
   relator set generated by `R`.
4. `GroupPresentation.hasSolvableWordProblem_of_finite_smallCancellation` from Theorem `5-6-3`
   already uses the direct disjunction of these owner predicates through `basis`, so this file
   should reuse the same hypothesis shape rather than introducing a parallel wrapper proposition.

Primitive vs. derived:
- primitive public data: the relator set `R`, finiteness of the generator type and relator set,
  and the small-cancellation alternative stated directly in the chapter owner predicates;
- derived API: the presentation-level conclusion `HasSolvableConjugacyProblem R`.
- API refinement note: the three source alternatives already live directly in the owner predicates
  `C(p)[basis, R]` and `T(q)[basis, R]`, so this file should state their disjunction directly
  instead of spelling raw `@condition_c` / `@condition_t` applications.
-/

-- Proof sketch: finite relator sets are effectively enumerable, and the small-cancellation
-- hypotheses `C(6)`, `C(4)` with `T(4)`, or `C(3)` with `T(6)` give the annular reduction
-- needed to bound possible conjugators. One can then search through the finitely many candidates
-- and decide whether two quotient elements are conjugate, yielding `HasSolvableConjugacyProblem`.
/-- Theorem 5-7-6: if `R` is a finite relator set in the finitely generated free group
`FreeGroup X` and `R` satisfies `C(6)`, or `C(4)` together with `T(4)`, or `C(3)` together with
`T(6)`, then the quotient by the normal closure of `R` has solvable conjugacy problem. The source
assumption that `R` is symmetrized is absorbed by the Chapter `5` owner predicates
`C(p)[basis, R]` and `T(q)[basis, R]`: `C(p)` is stated directly on the symmetrized relator
family, while `T(q)` is stated on the corresponding symmetrized relator set transported back to
actual relators through the canonical basis `basis`. -/
theorem hasSolvableConjugacyProblem_of_finite_smallCancellation
    (R : Set (FreeGroup X)) [Finite X] [Primcodable X] (hR : R.Finite)
    (hcase :
      C(6)[basis, R] ∨
        (C(4)[basis, R] ∧ T(4)[basis, R]) ∨
          (C(3)[basis, R] ∧ T(6)[basis, R])) :
    HasSolvableConjugacyProblem R := sorry

end GroupPresentation

end
