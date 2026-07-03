import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_1_1 (from Items/Chap05) -/
set_option autoImplicit false

open Set

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: planar realizations of maps in the Euclidean plane.

Layer triage:
- `source-facing`: the source treats a map as vertices, edges, and regions drawn in `𝔼²`, with
  closure and boundary operations on those planar pieces.
- `core/canonical`: `TwoComplex` is the project owner for the underlying oriented map,
  `TwoComplex.TwoManifoldEmbedding` is the owner for a realization of that map in a surface, and
  `OneComplex.GeometricEdge` / `TwoComplex.GeometricFace` are the canonical unoriented edge and
  region carriers.
- `bridge/view`: from a chosen planar embedding we recover the source-style vertex set, open
  edges, regions, support, and boundary as derived subsets of `𝔼²`.

Domain sampling:
1. `TwoComplex` from Definition `3-2-4` is the established owner abstraction for the map itself.
2. `TwoComplex.TwoManifoldEmbedding C 𝔼²` from Proposition `3-5-6` is the owner for a planar
   realization of that map.
3. `OneComplex.GeometricEdge` and `TwoComplex.GeometricFace` are the canonical unoriented cell
   carriers, so the source's plain "edges" and "regions" should be derived from them rather than
   rebuilt as a second root structure.
4. `closure`, `frontier`, and `sUnion` are the canonical topological owners for closed edge and
   face images, region boundaries, and finite unions of planar pieces.

Primitive vs. derived:
- primitive owner data: a `TwoComplex` and a chosen planar `TwoManifoldEmbedding`;
- derived API: source-style planar edges, regions, support, boundary, and the textbook planar-map
  axioms phrased as a property of that embedding.
-/

/- Definition 5-1-1: the chapter owner for the underlying oriented map is `TwoComplex`. -/
#check TwoComplex

/- A planar realization of that map is a `TwoManifoldEmbedding` into the Euclidean plane. -/
#check TwoComplex.TwoManifoldEmbedding

/- Existence of such a realization is the owner predicate `TwoComplex.EmbedsInPlane`. -/
#check TwoComplex.EmbedsInPlane

namespace Set

/-- A planar edge is a bounded subset of the Euclidean plane homeomorphic to the open unit
interval. -/
def IsPlanarEdge (e : Set 𝔼²) : Prop :=
  Bornology.IsBounded e ∧ Nonempty (Homeomorph (Set.Ioo (0 : ℝ) 1) e)

/-- A planar region is a bounded subset of the Euclidean plane homeomorphic to the open unit
disk. -/
def IsPlanarRegion (D : Set 𝔼²) : Prop :=
  Bornology.IsBounded D ∧ Nonempty (Homeomorph (Metric.ball (0 : 𝔼²) 1) D)

/-- Two vertices are endpoints of an edge when adjoining them to the edge gives its closure. -/
def HasEndpoints (e : Set 𝔼²) (a b : 𝔼²) : Prop :=
  closure e = e ∪ ({a, b} : Set 𝔼²)

end Set

namespace TwoComplex

/-- The unoriented geometric edge traversed by a total boundary arrow in the `1`-skeleton. -/
def boundaryArrowGeometricEdge {C : TwoComplex} (e : Quiver.Total C.skeleton) :
    OneComplex.GeometricEdge C.skeleton :=
  ⟦e.hom.1⟧

@[simp] theorem boundaryArrowGeometricEdge_reverse {C : TwoComplex}
    (e : Quiver.Total C.skeleton) :
    C.boundaryArrowGeometricEdge (Quiver.Total.reverse e) = C.boundaryArrowGeometricEdge e := by
  change (⟦e.hom.1⁻¹⟧ : OneComplex.GeometricEdge C.skeleton) = ⟦e.hom.1⟧
  exact Quot.sound (Or.inr rfl)

/-- The geometric edges occurring in the boundary cycle of an oriented face. -/
private def orientedBoundaryGeometricEdges (C : TwoComplex) (D : C.Face) :
    Set (OneComplex.GeometricEdge C.skeleton) :=
  { e | ∃ a ∈ (C.boundary D).1, C.boundaryArrowGeometricEdge a = e }

private theorem orientedBoundaryGeometricEdges_faceInv (C : TwoComplex) (D : C.Face) :
    C.orientedBoundaryGeometricEdges (C.faceInv D) = C.orientedBoundaryGeometricEdges D := by
  ext e
  constructor
  · rintro ⟨a, ha, hae⟩
    rw [C.boundary_faceInv D] at ha
    change a ∈ ((Quiver.Path.inverseCycle (C.boundary D)).1) at ha
    change a ∈ ((C.boundary D).1.reverse.map Quiver.Total.reverse) at ha
    rcases Cycle.mem_map.1 ha with ⟨b, hb, rfl⟩
    exact ⟨b, Cycle.mem_reverse_iff.1 hb, by simpa using hae⟩
  · rintro ⟨a, ha, hae⟩
    refine ⟨Quiver.Total.reverse a, ?_, by simpa using hae⟩
    rw [C.boundary_faceInv D]
    change Quiver.Total.reverse a ∈ ((C.boundary D).1.reverse.map Quiver.Total.reverse)
    exact Cycle.mem_map.2 ⟨a, Cycle.mem_reverse_iff.2 ha, rfl⟩

/-- The geometric edges occurring in the boundary cycle of a geometric face. -/
def boundaryGeometricEdges (C : TwoComplex) :
    GeometricFace C → Set (OneComplex.GeometricEdge C.skeleton) :=
  Quotient.lift (C.orientedBoundaryGeometricEdges) fun D E h ↦ by
    rcases h with rfl | h
    · rfl
    · simpa [h] using C.orientedBoundaryGeometricEdges_faceInv E

@[simp] theorem boundaryGeometricEdges_mk (C : TwoComplex) (D : C.Face) :
    C.boundaryGeometricEdges ⟦D⟧ = C.orientedBoundaryGeometricEdges D :=
  rfl

@[simp] theorem mem_boundaryGeometricEdges_mk_iff (C : TwoComplex) (D : C.Face)
    (e : OneComplex.GeometricEdge C.skeleton) :
    e ∈ C.boundaryGeometricEdges ⟦D⟧ ↔
      ∃ a ∈ (C.boundary D).1, C.boundaryArrowGeometricEdge a = e :=
  Iff.rfl

namespace TwoManifoldEmbedding

variable {C : TwoComplex}

/-- The set of vertices of a planar realization. -/
def vertexSet (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  Set.range embedding.vertexMap

/-- The closed image of an unoriented edge of the map. -/
def geometricEdgeSet
    (embedding : TwoManifoldEmbedding C 𝔼²) :
    OneComplex.GeometricEdge C.skeleton → Set 𝔼² :=
  Quotient.lift embedding.edgeSet fun e f h ↦ by
    rcases h with rfl | h
    · rfl
    · simpa [h] using embedding.edgeInv_set f

/-- The union of all closed edge-images of the planar realization. -/
def closedEdgeSupport (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  ⋃ e : OneComplex.GeometricEdge C.skeleton, embedding.geometricEdgeSet e

/-- The source-style edge corresponding to an unoriented edge is the closed edge-image with the
vertex set removed. -/
def edge
    (embedding : TwoManifoldEmbedding C 𝔼²)
    (e : OneComplex.GeometricEdge C.skeleton) : Set 𝔼² :=
  embedding.geometricEdgeSet e \ embedding.vertexSet

/-- The source-style region corresponding to a geometric face is the closed face-image with the
vertex set and all closed edge-images removed. -/
def region (embedding : TwoManifoldEmbedding C 𝔼²) (D : GeometricFace C) : Set 𝔼² :=
  embedding.geometricFaceSet D \ (embedding.vertexSet ∪ embedding.closedEdgeSupport)

/-- The underlying subset of the plane occupied by the planar realization. -/
def support (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  embedding.vertexSet ∪
    (⋃ e : OneComplex.GeometricEdge C.skeleton, embedding.edge e) ∪
      ⋃ D : GeometricFace C, embedding.region D

/-- The boundary of a planar realization is the frontier of its support. -/
def boundary (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  frontier embedding.support

/-- The closed-edge support prescribed by the combinatorial boundary of an oriented face. -/
def faceBoundarySupport (embedding : TwoManifoldEmbedding C 𝔼²) (D : GeometricFace C) : Set 𝔼² :=
  sUnion (embedding.geometricEdgeSet '' C.boundaryGeometricEdges D)

@[simp] theorem geometricEdgeSet_mk (embedding : TwoManifoldEmbedding C 𝔼²) (e : C.skeleton.Edge) :
    embedding.geometricEdgeSet ⟦e⟧ = embedding.edgeSet e :=
  rfl

@[simp] theorem faceBoundarySupport_mk (embedding : TwoManifoldEmbedding C 𝔼²) (D : C.Face) :
    embedding.faceBoundarySupport ⟦D⟧ =
      sUnion (embedding.geometricEdgeSet '' C.orientedBoundaryGeometricEdges D) :=
  rfl

/-- Definition 5-1-1, expressed on the canonical owner: a planar realization of a `TwoComplex`
is a finite planar map when its source-style edges and regions satisfy the textbook interval,
disk, endpoint, disjointness, and boundary-incidence conditions. -/
class IsPlanarMap (embedding : TwoManifoldEmbedding C 𝔼²) : Prop where
  finite_vertex : Finite C.skeleton
  finite_edge : Finite (OneComplex.GeometricEdge C.skeleton)
  finite_face : Finite (GeometricFace C)
  edge_isPlanar (e : OneComplex.GeometricEdge C.skeleton) :
    (embedding.edge e).IsPlanarEdge
  region_isPlanar (D : GeometricFace C) :
    (embedding.region D).IsPlanarRegion
  region_closure (D : GeometricFace C) :
    closure (embedding.region D) = embedding.geometricFaceSet D
  edge_closedEdge (e : OneComplex.GeometricEdge C.skeleton) :
    closure (embedding.edge e) = embedding.geometricEdgeSet e
  edge_hasEndpoints (e : C.skeleton.Edge) :
    (embedding.edge ⟦e⟧).HasEndpoints
      (embedding.vertexMap (C.skeleton.initial e))
      (embedding.vertexMap (C.skeleton.terminal e))
  edge_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set (OneComplex.GeometricEdge C.skeleton))
      embedding.edge
  region_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set (GeometricFace C))
      embedding.region
  edge_region_disjoint (e : OneComplex.GeometricEdge C.skeleton) (D : GeometricFace C) :
    Disjoint (embedding.edge e) (embedding.region D)
  region_boundary_connected (D : GeometricFace C) :
    IsConnected (frontier (embedding.region D))
  region_boundary_eq_faceBoundarySupport (D : GeometricFace C) :
    frontier (embedding.region D) = embedding.faceBoundarySupport D

/-- A face-boundary incidence in a carried subcomplex is also a face-boundary incidence for the
corresponding ambient face. -/
private theorem vertexOnFace_of_subcomplex
    {S : Subcomplex C} {v : S.complex.skeleton} {D : S.complex.Face} :
    S.complex.VertexOnFace v D → C.VertexOnFace v.1 D.1 := by
  sorry

/-- Restricting a surface embedding to a carried subcomplex keeps the same geometric images of
the surviving vertices, edges, and faces. -/
def restrictToSubcomplex (embedding : TwoManifoldEmbedding C 𝔼²) (S : Subcomplex C) :
    TwoManifoldEmbedding S.complex 𝔼² where
  vertexMap v := embedding.vertexMap v.1
  edgeMap e := embedding.edgeMap e.1
  faceMap D := embedding.faceMap D.1
  vertex_injective := fun _ _ h ↦ Subtype.ext (embedding.vertex_injective h)
  edge_isClosedEmbedding := fun e ↦ embedding.edge_isClosedEmbedding e.1
  face_isClosedEmbedding := fun D ↦ embedding.face_isClosedEmbedding D.1
  source_eq_edgeMap_zero := fun e ↦ embedding.source_eq_edgeMap_zero e.1
  target_eq_edgeMap_one := fun e ↦ embedding.target_eq_edgeMap_one e.1
  edgeInv_range := fun e ↦ embedding.edgeInv_range e.1
  faceInv_range := fun D ↦ embedding.faceInv_range D.1
  boundary_edge_subset_face := by
    sorry
  boundary_vertex_mem_face := fun hv ↦
    embedding.boundary_vertex_mem_face (vertexOnFace_of_subcomplex hv)

/-- Restricting a planar map to a carried subcomplex again yields a planar map. -/
instance isPlanarMap_restrictToSubcomplex
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] (S : Subcomplex C) :
    (embedding.restrictToSubcomplex S).IsPlanarMap := by
  sorry

/-- Restricting a planar map to a nested subcomplex again yields a planar map. -/
instance isPlanarMap_restrict {C : TwoComplex} {S T : TwoComplex.Subcomplex C}
    (embedding : TwoManifoldEmbedding S.complex 𝔼²) [embedding.IsPlanarMap]
    (hvertex : T.skeleton.vertexSet ⊆ S.skeleton.vertexSet)
    (hedge : T.skeleton.edgeSet ⊆ S.skeleton.edgeSet)
    (hface : T.faceSet ⊆ S.faceSet) :
    (embedding.restrict hvertex hedge hface).IsPlanarMap := by
  sorry

/-- A finite planar map has only finitely many oriented edges, since each geometric edge has the
two possible orientations. -/
theorem finite_orientedEdge {C : TwoComplex} (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] :
    Finite C.skeleton.Edge := by
  classical
  let hplanar : embedding.IsPlanarMap := inferInstance
  let _ : Finite (OneComplex.GeometricEdge C.skeleton) := hplanar.finite_edge
  let f : OneComplex.GeometricEdge C.skeleton × Bool → C.skeleton.Edge := fun x ↦
    if x.2 then (Quotient.out x.1)⁻¹ else Quotient.out x.1
  have hf : Function.Surjective f := by
    intro e
    let q : OneComplex.GeometricEdge C.skeleton := ⟦e⟧
    rcases Quotient.eq.mp (Quotient.out_eq q) with h | h
    · refine ⟨(q, false), ?_⟩
      simp [f, q, h]
    · refine ⟨(q, true), ?_⟩
      have h' : q.out⁻¹ = e := by
        exact (congrArg C.skeleton.edgeInv h).trans (C.skeleton.edgeInv_involutive e)
      simp [f, q, h']
  exact Finite.of_surjective f hf

end TwoManifoldEmbedding
end TwoComplex

/-! ### Definition_5_1_2 (from Items/Chap05) -/
open Quiver.Path

universe u v

-- Layer triage:
-- `source-facing`: Definition 5-1-2 introduces paths, closed paths, reduced paths, and simple
-- paths in a fixed `1`-complex.
-- `core/canonical`: `OneComplex` from Definition 3-2-1 is the owner abstraction for oriented
-- edges, while `Quiver.Path`, `Quiver.Path.Loop`, `Quiver.Path.IsReduced`, and
-- `Quiver.Path.IsSimple` are the canonical owner declarations for the path notions in this item.
-- `bridge/view`: `OneComplex.Path.edges` recovers the textbook sequence of oriented edges from the
-- canonical total-edge list `Quiver.Path.edgeList`.
-- Domain sampling:
-- 1. `Quiver.Path` is mathlib's canonical endpoint-aware finite path type and already includes the
--    empty path.
-- 2. `Quiver.Path.Loop` is the established owner for closed paths with a remembered basepoint.
-- 3. `Quiver.Path.IsReduced` and `Quiver.Path.IsSimple` already define the reduced/simple path
--    predicates upstream in Chapter 3.
-- 4. `Quiver.Path.edgeList` is the canonical ordered total-edge list, from which the textbook
--    oriented-edge sequence is derived.
-- Primitive vs. derived:
-- this item contributes no new owner object beyond the existing path API on `Quiver.Path`; the
-- only additional source-facing bridge needed here is the oriented-edge list of a path.

namespace OneComplex

/- Definition 5-1-2: a path in a `1`-complex from `a` to `b` is the canonical quiver path
`Quiver.Path a b`, with empty path `Quiver.Path.nil`. -/
#check Quiver.Path

/- A closed path is the special case `Quiver.Path a a`; the owner bundled API for based closed
paths is `Quiver.Path.Loop`. -/
#check Quiver.Path.Loop

/- Reduced paths in a `1`-complex are given by the owner predicate `Quiver.Path.IsReduced`. -/
#check Quiver.Path.IsReduced

/- Simple paths in a `1`-complex are given by the owner predicate `Quiver.Path.IsSimple`. -/
#check Quiver.Path.IsSimple

namespace Path

variable {C : OneComplex.{u, v}}

/-- The underlying sequence of oriented edges traversed by a path. -/
abbrev edges {a b : C} (p : Quiver.Path a b) : List C.Edge :=
  p.edgeList.map fun e ↦ e.hom.1

/-- The empty path traverses no oriented edges. -/
@[simp] theorem edges_nil (a : C) : edges (nil : Quiver.Path a a) = [] := rfl

@[simp] theorem edges_cons {a b c : C} (p : Quiver.Path a b) (e : b ⟶ c) :
    edges (cons p e) = edges p ++ [e.1] := by
  simp [edges, Quiver.Path.edgeList, List.map_append]

end Path

end OneComplex

/-! ### Definition_5_1_3 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

section

variable {F : Type u} [Group F]

/-!
Primary domain: combinatorial group theory of group-labelled oriented maps.

Layer triage:
- `source-facing`: a diagram over a group is an oriented map together with a label on each
  oriented edge, compatible with reversal of orientation.
- `core/canonical`: `TwoComplex` is the project owner for oriented maps, while the edge-reversal
  operation on its `1`-skeleton is the canonical owner for the opposite orientation of an edge.
- `bridge/view`: a diagram is used via its underlying oriented map through a coercion to
  `TwoComplex`.

Domain sampling:
1. `TwoComplex` from Definition `3-2-4` is the existing owner abstraction for oriented maps.
2. The inverse-edge owner API on the `1`-skeleton is the notation `e⁻¹`, coming from
   `OneComplex.edgeInv`.
3. A group-valued edge-labelling is naturally a function on `source.skeleton.Edge`, and the
   textbook compatibility condition is a single structure field rather than a separate wrapper.

Primitive vs. derived:
- primitive data: the oriented map, the edge-label function, and the inverse-edge compatibility
  law;
- derived API: viewing a diagram as its underlying oriented map.
-/

/-- Definition 5-1-3: a diagram over a group `F` is an oriented map together with a label on each
oriented edge such that the label of the oppositely oriented edge is the inverse of the original
label. -/
structure GroupDiagram (F : Type u) [Group F] where
  /-- The underlying oriented map. -/
  source : TwoComplex.{v}
  /-- The label assigned to each oriented edge of the underlying map. -/
  label : source.skeleton.Edge → F
  /-- Reversing the orientation of an edge inverts its label. -/
  label_inv (e : source.skeleton.Edge) : label e⁻¹ = (label e)⁻¹

namespace GroupDiagram

attribute [simp] GroupDiagram.label_inv

/-- A group diagram is used via its underlying oriented map. -/
instance : CoeOut (GroupDiagram F) TwoComplex where
  coe := source

end GroupDiagram

end

/-! ### Definition_5_1_4 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

open Quiver.Path
open OneComplex
open scoped TwoComplex

section

variable {F : Type u} [Group F]

/-!
Primary domain: group-labelled paths and region labels in oriented `2`-complexes.

Layer triage:
- `source-facing`: multiply the edge labels along a path, then use loops representing the boundary
  cycle of a face to define the labels of that face.
- `core/canonical`: `GroupDiagram` is the owner of the edge-labelling, `Quiver.Path` is the owner
  of endpoint-aware paths, and `Loop` together with `cyclicPath` is the owner API for a
  basepoint-free boundary cycle.
- `bridge/view`: `TwoComplex.BoundaryPath` is the based closed-path representative API for a
  chosen basepoint on the face boundary, while `OneComplex.Path.edges` remains the chapter bridge
  to the textbook oriented-edge word of a path.

Domain sampling:
1. `GroupDiagram.label` is the canonical edge-labelling function attached to the diagram.
2. `Quiver.Path` is the owner path type, so path evaluation should be defined recursively on
   paths rather than through a derived edge-list wrapper.
3. `Loop` and `cyclicPath` are the owner boundary-cycle API without a preferred basepoint.
4. `TwoComplex.BoundaryPath` is the project owner for a based representative of a face boundary.
-/

namespace GroupDiagram

/-- The group element obtained by multiplying the labels of the oriented edges traversed by a path
in their path order. -/
def pathLabel (M : GroupDiagram F) {a b : M.source.skeleton} (p : Quiver.Path a b) : F :=
  match p with
  | .nil => 1
  | .cons p e => M.pathLabel p * M.label e.1

/-- The empty path has trivial label product. -/
-- Proof sketch: unfold `pathLabel`; the edge list of the empty path is empty, so the list product
-- is the empty product `1`.
@[simp]
theorem pathLabel_nil (M : GroupDiagram F) (a : M.source.skeleton) :
    M.pathLabel (nil : Quiver.Path a a) = 1 :=
  rfl

/-- Appending one oriented edge multiplies the path label by the label of that edge. -/
@[simp] theorem pathLabel_cons (M : GroupDiagram F) {a b c : M.source.skeleton}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    M.pathLabel (.cons p e) = M.pathLabel p * M.label e.1 :=
  rfl

/-- Definition 5-1-4: the labels of a region `D` are the group elements obtained by applying
`pathLabel` to loops representing the boundary cycle `∂D`. -/
def regionLabels (M : GroupDiagram F) (D : M.source.Face) : Set F :=
  { g | ∃ p : Loop M.source.skeleton, cyclicPath p = (∂ D) ∧ M.pathLabel p.2 = g }

/-- A group element belongs to `regionLabels D` exactly when it is the label of some loop
representing the boundary cycle of `D`. -/
theorem mem_regionLabels_iff_exists_loop (M : GroupDiagram F) (D : M.source.Face) (g : F) :
    g ∈ M.regionLabels D ↔
      ∃ p : Loop M.source.skeleton, cyclicPath p = (∂ D) ∧ M.pathLabel p.2 = g :=
  Iff.rfl

/-- A group element belongs to `regionLabels D` exactly when it is the label of some based
boundary path of `D`. -/
theorem mem_regionLabels_iff (M : GroupDiagram F) (D : M.source.Face) (g : F) :
    g ∈ M.regionLabels D ↔
      ∃ v : M.source.skeleton, ∃ q : M.source.BoundaryPath D v, M.pathLabel q.1 = g := by
  constructor
  · rintro ⟨⟨v, p⟩, hp, rfl⟩
    exact ⟨v, ⟨p, hp⟩, rfl⟩
  · rintro ⟨v, q, rfl⟩
    exact ⟨⟨v, q.1⟩, q.2, rfl⟩

/-- The label of any loop representing the boundary cycle of `D` is one of the labels of `D`. -/
theorem boundaryCycleLabel_mem_regionLabels (M : GroupDiagram F) (D : M.source.Face)
    (p : Loop M.source.skeleton) (hp : cyclicPath p = (∂ D)) :
    M.pathLabel p.2 ∈ M.regionLabels D :=
  ⟨p, hp, rfl⟩

end GroupDiagram

end

/-! ### Definition_5_1_5 (from Items/Chap05) -/
universe u v w

open CategoryTheory Quiver.Path OneComplex OneComplex.Hom

set_option autoImplicit false

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqFreeGroupDiagram : DecidableEq X := Classical.decEq X

-- Primary domain: small-cancellation diagrams over a free group with a chosen basis.
--
-- Layer triage:
-- `source-facing`: a group-labelled singular disc in the free group whose chosen outer boundary
-- loop reads the prescribed product `c₁ ⋯ cₙ` and whose region boundary words read the listed
-- relators up to conjugacy.
-- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
-- basis, `GroupDiagram F` is the owner abstraction for an oriented map labelled by group
-- elements, `TwoComplex.Subcomplex.IsSingularDisc` is the chapter owner for genuine disc-diagram
-- geometry, and `Loop` together with `cyclicPath` are the owner abstractions for boundary loops
-- and boundary cycles.
-- `bridge/view`: `TwoComplex.fullSubcomplex` turns the whole labelled map into the ambient
-- subcomplex required by `IsSingularDisc`, `basis.repr` reads an intrinsic element of `F` as a
-- reduced word in the chosen basis, and `GroupDiagram.pathLabelWord` is the source-facing
-- boundary word obtained by concatenating those reduced edge-label words along a path.
--
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the established owner for “a free group with a given basis”.
-- 2. `GroupDiagram F` from Definition `5-1-3` is the existing owner for a labelled oriented map.
-- 3. `GroupDiagram.pathLabel` from Definition `5-1-4` is the existing owner for multiplying edge
--    labels along a path.
-- 4. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for a
--    planar simply connected disc with explicit boundary cycle and geometric edge incidence.
-- 5. `IsConj` is mathlib's owner relation for “is a conjugate of”, while
--    `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclically reduced reduced words.
--
-- Primitive vs. derived:
-- the primitive data are the underlying `GroupDiagram`, the chosen outer boundary loop, the
-- singular-disc owner proof for its cyclic boundary, and the relator conditions. The ambient
-- connectedness and simple connectedness of the whole labelled map are derived from the
-- singular-disc owner on the full subcomplex. Finiteness is likewise derived from that owner,
-- while the reduced and cyclically reduced boundary conditions are stated directly on the
-- source-facing boundary word `pathLabelWord`; the bridge back to the intrinsic product
-- `pathLabel` is derived via `basis.repr`.

namespace TwoComplex

/-- The full `1`-skeleton subcomplex of a `2`-complex, carrying every vertex and edge. -/
def fullOneSubcomplex (C : TwoComplex) : OneComplex.Subcomplex C.skeleton where
  vertexSet := Set.univ
  edgeSet := Set.univ
  initial_mem _ := by simp
  terminal_mem _ := by simp
  edgeInv_mem _ := by simp

/-- The ambient `1`-skeleton maps canonically onto the `1`-skeleton of the full subcomplex. -/
def toFullOneSubcomplex (C : TwoComplex) :
    OneComplex.Hom C.skeleton C.fullOneSubcomplex.toOneComplex where
  toVertex v := ⟨v, by simp [fullOneSubcomplex]⟩
  toEdge e := ⟨e, by simp [fullOneSubcomplex]⟩
  map_initial _ := Subtype.ext rfl
  map_terminal _ := Subtype.ext rfl
  map_edgeInv _ := Subtype.ext rfl

/-- The full subcomplex of a `2`-complex, carrying every vertex, edge, and face. -/
def fullSubcomplex (C : TwoComplex) : Subcomplex C where
  skeleton := C.fullOneSubcomplex
  faceSet := Set.univ
  faceInv_mem _ := by simp
  boundary D := C.toFullOneSubcomplex.mapCyclicPath (C.boundary D.1)
  boundary_eq D := by
    let fullInclusion := C.fullOneSubcomplex.inclusion
    let toFull := C.toFullOneSubcomplex
    apply Subtype.ext
    change Cycle.map fullInclusion.mapTotal
        (Cycle.map toFull.mapTotal ↑(C.boundary D.1)) = ↑(C.boundary D.1)
    refine Quotient.inductionOn' (C.boundary D.1).1 ?_
    intro l
    have hmap :
        fullInclusion.mapTotal ∘ toFull.mapTotal = id := by
      funext e
      cases e
      rfl
    have hmapList :
        List.map (fullInclusion.mapTotal ∘ toFull.mapTotal) l = l := by
      simpa using congrArg (fun f ↦ List.map f l) hmap
    apply Cycle.coe_eq_coe.2
    simpa [hmapList] using List.IsRotated.refl l

end TwoComplex

namespace GroupDiagram

/-- The basis word obtained by reading the labels of the oriented edges traversed by a based path,
expanding each label into its reduced word in the chosen basis. -/
def pathLabelWord (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    {a b : M.source.skeleton} : Quiver.Path a b → List (X × Bool)
  | .nil => []
  | .cons p e => M.pathLabelWord basis p ++ (basis.repr (M.label e.1)).toWord

/-- The empty path reads as the empty basis word. -/
@[simp] theorem pathLabelWord_nil (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    (a : M.source.skeleton) :
    M.pathLabelWord basis (nil : Quiver.Path a a) = [] :=
  rfl

/-- Appending one oriented edge appends the reduced word of its label. -/
@[simp] theorem pathLabelWord_cons (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    {a b c : M.source.skeleton} (p : Quiver.Path a b) (e : b ⟶ c) :
    M.pathLabelWord basis (.cons p e) =
      M.pathLabelWord basis p ++ (basis.repr (M.label e.1)).toWord :=
  rfl

/-- Reading a path label through the chosen basis gives the free-group word obtained by
concatenating the reduced words of the successive edge labels. -/
-- Proof sketch: expand `GroupDiagram.pathLabel` as the ordered product of the path edge labels,
-- use that `basis.repr` is a multiplicative equivalence, and rewrite each factor by
-- `FreeGroup.mk_toWord`.
theorem repr_pathLabel (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    {a b : M.source.skeleton} (p : Quiver.Path a b) :
    basis.repr (M.pathLabel p) = FreeGroup.mk (M.pathLabelWord basis p) :=
  by
    induction p with
    | nil =>
        simp [FreeGroup.one_eq_mk]
    | cons p e ih =>
        have hw :
            FreeGroup.mk ((basis.repr (M.label e.1)).toWord) = basis.repr (M.label e.1) :=
          FreeGroup.mk_toWord
        rw [M.pathLabel_cons p e, map_mul, ih, ← hw]
        simp [FreeGroup.mul_mk]

end GroupDiagram

/-- Definition 5-1-5: a diagram for the finite sequence `(c₁, ..., cₙ)` in the free group with
chosen basis `basis` is a group-labelled singular disc whose oriented edges have nontrivial
labels, whose chosen outer boundary loop reads the reduced product `c₁ ⋯ cₙ`, and whose
geometric regions admit an orientation whose boundary word is cyclically reduced and whose label
product is conjugate to one of the listed relators. -/
structure FreeGroupDiagram (basis : FreeGroupBasis X F) (relators : List F) extends GroupDiagram F where
  /-- A chosen outer boundary loop of the diagram, viewed in the full subcomplex of the
  underlying map. -/
  outerBoundary :
    let S := source.fullSubcomplex
    Loop S.skeleton.toOneComplex
  /-- The whole labelled map is a genuine singular disc with boundary given by the chosen outer
  boundary loop. -/
  singularDisc :
    let S := source.fullSubcomplex
    S.IsSingularDisc (cyclicPath outerBoundary)
  /-- Every oriented edge has nontrivial label. -/
  label_ne_one (e : source.skeleton.Edge) : label e ≠ 1
  /-- The outer boundary word is reduced without cancellation. -/
  outerBoundary_reduced :
    let S := source.fullSubcomplex
    let p := mapLoop S.skeleton.inclusion outerBoundary
    FreeGroup.IsReduced (toGroupDiagram.pathLabelWord basis p.2)
  /-- The outer boundary label product is exactly `c₁ ⋯ cₙ`. -/
  outerBoundary_product :
    let S := source.fullSubcomplex
    let p := mapLoop S.skeleton.inclusion outerBoundary
    toGroupDiagram.pathLabel p.2 = relators.prod
  /-- Every geometric region admits an oriented representative together with a based boundary path
  whose boundary word is cyclically reduced and whose label product is conjugate to one of the
  listed relators. -/
  regionBoundary_condition (D : TwoComplex.GeometricFace source) :
    ∃ E : source.Face, ⟦E⟧ = D ∧
      ∃ v : source.skeleton, ∃ q : source.BoundaryPath E v,
        FreeGroup.IsCyclicallyReduced (toGroupDiagram.pathLabelWord basis q.1) ∧
          ∃ i : Fin relators.length, IsConj (toGroupDiagram.pathLabel q.1) (relators.get i)

namespace FreeGroupDiagram

variable {basis : FreeGroupBasis X F} {relators : List F}

private theorem mapPath_edgeList_eq {C D : OneComplex} (f : OneComplex.Hom C D)
    {a b : C} (p : Quiver.Path a b) :
    (f.mapPath p).edgeList = List.map f.mapTotal p.edgeList := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change (f.toPrefunctor.mapPath (p.cons e)).edgeList =
        List.map f.mapTotal (p.cons e).edgeList
      have ih' : (f.toPrefunctor.mapPath p).edgeList = List.map f.mapTotal p.edgeList := ih
      rw [Prefunctor.mapPath_cons, Quiver.Path.edgeList, Quiver.Path.edgeList,
        List.map_append, ih']
      rfl

private theorem inclusion_toFull_mapPath {C : TwoComplex} {a b : C.skeleton} (p : Quiver.Path a b) :
    C.fullOneSubcomplex.inclusion.toPrefunctor.mapPath (C.toFullOneSubcomplex.toPrefunctor.mapPath p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons]
      have hcons :=
        congrArg
          (fun q ↦ q.cons
            (C.fullOneSubcomplex.inclusion.toPrefunctor.map
              (C.toFullOneSubcomplex.toPrefunctor.map e))) ih
      simpa [TwoComplex.toFullOneSubcomplex, OneComplex.Subcomplex.inclusion,
        OneComplex.Hom.toPrefunctor, OneComplex.Hom.mapQuiverEdge] using hcons

private def complexInclusion {C : TwoComplex} (S : TwoComplex.Subcomplex C) :
    TwoComplex.Hom S.complex C where
  toVertex := S.skeleton.inclusion.toVertex
  toEdge := S.skeleton.inclusion.toEdge
  map_initial := S.skeleton.inclusion.map_initial
  map_terminal := S.skeleton.inclusion.map_terminal
  map_edgeInv := S.skeleton.inclusion.map_edgeInv
  mapFace D := D.1
  map_faceInv D := rfl
  mapBoundary {D} {v} q := by
    have h := (congrArg S.skeleton.inclusion.mapCyclicPath q.2).trans (S.boundary_eq D)
    refine ⟨S.skeleton.inclusion.mapPath q.1, ?_⟩
    have hm :
        cyclicPath ⟨S.skeleton.inclusion.toVertex v, S.skeleton.inclusion.mapPath q.1⟩ =
          S.skeleton.inclusion.mapCyclicPath (cyclicPath ⟨v, q.1⟩) := by
      apply Subtype.ext
      apply Cycle.coe_eq_coe.2
      simpa [mapPath_edgeList_eq] using
        List.IsRotated.refl (List.map S.skeleton.inclusion.mapTotal q.1.edgeList)
    exact hm.trans h

/-- The chosen boundary loop of a free-group diagram, viewed in the ambient labelled map. -/
abbrev outerBoundaryLoop (D : FreeGroupDiagram basis relators) : Loop D.source.skeleton :=
  let S := D.source.fullSubcomplex
  mapLoop S.skeleton.inclusion D.outerBoundary

/-- A free-group diagram is used via its underlying oriented `2`-complex. -/
instance : CoeOut (FreeGroupDiagram basis relators) TwoComplex where
  coe D := D.source

/-- The underlying `1`-skeleton of a free-group diagram is finite. -/
theorem finite_vertex (D : FreeGroupDiagram basis relators) : Finite D.source.skeleton := by
  classical
  let hsingular := D.singularDisc.toIsSingularSubcomplex
  exact
    Set.finite_univ_iff.mp <| by
      simpa [TwoComplex.fullSubcomplex, TwoComplex.fullOneSubcomplex] using
        hsingular.finite_vertexSet

/-- The underlying `1`-skeleton of a free-group diagram is finite. -/
instance (D : FreeGroupDiagram basis relators) : Finite D.source.skeleton :=
  D.finite_vertex

/-- The oriented edge set of a free-group diagram is finite. -/
theorem finite_edge (D : FreeGroupDiagram basis relators) :
    Finite (OneComplex.Edge D.source.skeleton) := by
  classical
  let hsingular := D.singularDisc.toIsSingularSubcomplex
  exact
    Set.finite_univ_iff.mp <| by
      simpa [TwoComplex.fullSubcomplex, TwoComplex.fullOneSubcomplex] using
        hsingular.finite_edgeSet

/-- The oriented edge set of a free-group diagram is finite. -/
instance (D : FreeGroupDiagram basis relators) : Finite (OneComplex.Edge D.source.skeleton) :=
  D.finite_edge

/-- The oriented face set of a free-group diagram is finite. -/
theorem finite_face (D : FreeGroupDiagram basis relators) : Finite (TwoComplex.Face D.source) := by
  classical
  let hsingular := D.singularDisc.toIsSingularSubcomplex
  exact
    Set.finite_univ_iff.mp <| by
      simpa [TwoComplex.fullSubcomplex] using
        hsingular.finite_faceSet

/-- The oriented face set of a free-group diagram is finite. -/
instance (D : FreeGroupDiagram basis relators) : Finite (TwoComplex.Face D.source) := D.finite_face

/-- The chosen outer boundary loop presents a simple boundary cycle. -/
theorem outerBoundary_simpleCycle (D : FreeGroupDiagram basis relators) :
    IsSimpleCycle (cyclicPath D.outerBoundary) :=
  D.singularDisc.simpleCycle

/-- The chosen outer boundary loop is cyclically reduced as a combinatorial boundary cycle. -/
theorem outerBoundary_cyclicallyReducedCycle (D : FreeGroupDiagram basis relators) :
    IsCyclicallyReducedCycle (cyclicPath D.outerBoundary) :=
  D.singularDisc.cyclicallyReducedCycle

theorem pathClass_eq_one (D : FreeGroupDiagram basis relators) {v : D.source.skeleton}
    (p : Quiver.Path v v) :
    (Quotient.mk'' p : End (⟨v⟩ : D.source.pi)) = (𝟙 (⟨v⟩ : D.source.pi)) := by
  let S := D.source.fullSubcomplex
  let φ : TwoComplex.Hom S.complex D.source := complexInclusion S
  let v' : S.complex.skeleton := ⟨v, by
    change v ∈ (Set.univ : Set D.source.skeleton)
    exact Set.mem_univ _⟩
  let p' : Quiver.Path v' v' := D.source.toFullOneSubcomplex.mapPath p
  haveI : TwoComplex.IsSimplyConnected S.complex := D.singularDisc.simplyConnected
  have hp' : (Quotient.mk'' p' : End (⟨v'⟩ : S.complex.pi)) =
      (𝟙 (⟨v'⟩ : S.complex.pi)) :=
    TwoComplex.fundamentalGroup_eq_one v' (Quotient.mk'' p')
  have hφ := congrArg (φ.inducedFundamentalGroupHom v') hp'
  have hmap : φ.inducedFundamentalGroupHom v' (Quotient.mk'' p') = Quotient.mk'' p := by
    change Quotient.map' φ.mapPath (fun _ _ h ↦ φ.mapPath_path_two_equiv h) (Quotient.mk'' p') =
      Quotient.mk'' p
    exact congrArg Quotient.mk'' (inclusion_toFull_mapPath p)
  have hid :
      φ.inducedFundamentalGroupHom v' (𝟙 (⟨v'⟩ : S.complex.pi)) =
        𝟙 (⟨v⟩ : D.source.pi) := by
    rfl
  exact hmap.symm.trans (hφ.trans hid)

/-- The underlying `1`-skeleton of a free-group diagram is connected. -/
theorem connected (D : FreeGroupDiagram basis relators) :
    Quiver.IsStronglyConnected (Quiver.Symmetrify D.source.skeleton) := by
  intro v w
  let S := D.source.fullSubcomplex
  let v' : S.complex.skeleton := ⟨v, by
    change v ∈ (Set.univ : Set D.source.skeleton)
    exact Set.mem_univ _⟩
  let w' : S.complex.skeleton := ⟨w, by
    change w ∈ (Set.univ : Set D.source.skeleton)
    exact Set.mem_univ _⟩
  rcases D.singularDisc.connected v' w' with ⟨p⟩
  exact ⟨S.skeleton.inclusion.toPrefunctor.symmetrify.mapPath p⟩

/-- The underlying oriented map of a free-group diagram is simply connected. -/
theorem simplyConnected (D : FreeGroupDiagram basis relators) :
    TwoComplex.IsSimplyConnected D := by
  refine ⟨?_⟩
  intro v
  refine ⟨?_⟩
  intro g h
  refine Quotient.inductionOn₂ g h ?_
  intro p q
  exact (FreeGroupDiagram.pathClass_eq_one D p).trans
    (FreeGroupDiagram.pathClass_eq_one D q).symm

/-- The underlying oriented map of a free-group diagram is simply connected. -/
instance (D : FreeGroupDiagram basis relators) :
    TwoComplex.IsSimplyConnected D :=
  D.simplyConnected

end FreeGroupDiagram

end

/-! ### Theorem_5_1_6 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

section

variable {X : Type u} {F : Type v} [Group F]

/-!
Primary domain: free-group diagrams for an ordered finite sequence of nontrivial relators in a
free group with chosen basis.

Layer triage:
- `source-facing`: a basis `basis : FreeGroupBasis X F` together with a finite ordered sequence
  `relators : List F` of nontrivial elements, and a diagram whose geometric faces are in ordered
  bijection with that full sequence.
- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
  basis, while `FreeGroupDiagram basis relators` from Definition `5-1-5` is the chapter owner for
  such diagrams.
- `bridge/view`: `GroupDiagram.pathLabel` and `GroupDiagram.pathLabelWord` are the canonical
  boundary-label evaluators used in the owner fields of `FreeGroupDiagram` and in the ordered
  face-realization conclusion asserted below.

Domain sampling:
1. `FreeGroupBasis X F` is the established owner for a free group with chosen basis.
2. `FreeGroupDiagram basis relators` from Definition `5-1-5` is the chapter owner abstraction
   for a diagram with relator list `relators`.
3. `GroupDiagram.pathLabel` is the canonical boundary-label evaluation map already built into the
   owner field `FreeGroupDiagram.outerBoundary_product`.
4. `GroupDiagram.pathLabelWord` is the canonical source-facing boundary-word API used in the
   cyclically reduced region condition from Definition `5-1-5`.
5. Chapter `2` owner-level statements such as
   `FreeGroupBasis.basisLetterOccurs_of_mem_normalClosure_singleton_of_isCyclicallyReduced` are
   organized around an arbitrary `basis : FreeGroupBasis X F`, confirming that the ambient owner
   is the free group with chosen basis rather than the concrete model `FreeGroup X`.

Primitive vs. derived:
- primitive public data: the chosen basis `basis : FreeGroupBasis X F`, the relator list
  `relators : List F`, and the pointwise nontriviality hypothesis on that ordered sequence;
- derived API: the geometric `2`-complex, boundary loop, reducedness, and conjugacy conditions
  already stored by `FreeGroupDiagram basis relators`, together with the ordered face-by-face
  realization conclusion asserted directly by Theorem `5-1-6`.
-/

namespace FreeGroupDiagram

-- Proof sketch: write each nontrivial relator `cᵢ` as a conjugate of a cyclically reduced word,
-- build the corresponding one-face lollipop diagram for each factor, and attach those diagrams in
-- the given order around a common basepoint. This gives one geometric face for each index `i`.
-- Whenever the outer boundary word has adjacent inverse letters, fold or delete the cancellable
-- boundary pair; this preserves the cyclically reduced face labels and the ordered face data while
-- strictly shortening the boundary. Iterating terminates with a reduced outer boundary word.
/-- Theorem 5-1-6: every finite ordered sequence of nontrivial elements of a free group with
chosen basis `basis` admits a chapter-`5` free-group diagram whose geometric faces are in ordered
bijective correspondence with the full relator sequence. -/
theorem exists_orderedFaceRealization (basis : FreeGroupBasis X F) (relators : List F)
    (hrelators : ∀ i : Fin relators.length, relators.get i ≠ 1) :
    ∃ D : FreeGroupDiagram basis relators,
      ∃ e : Fin relators.length ≃ D.source.GeometricFace,
        ∀ i : Fin relators.length,
          ∃ E : D.source.Face, ⟦E⟧ = e i ∧
            ∃ v : D.source.skeleton, ∃ q : D.source.BoundaryPath E v,
              FreeGroup.IsCyclicallyReduced (D.toGroupDiagram.pathLabelWord basis q.1) ∧
                IsConj (D.toGroupDiagram.pathLabel q.1) (relators.get i) := by
  sorry

end FreeGroupDiagram

end

/-! ### Lemma_5_1_7 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

open Quiver.Path
open Group
open OneComplex.Hom

section

variable {F : Type u} [Group F]

/-!
Primary domain: group-labelled singular disc diagrams and boundary words as products of
region-label conjugates.

Layer triage:
- `source-facing`: a group-labelled ambient `2`-complex together with a singular disc subcomplex
  and its chosen outer boundary loop.
- `core/canonical`: `GroupDiagram` is the owner for the edge-labelling,
  `TwoComplex.Subcomplex.IsSingularDisc` is the owner for the disc-boundary data,
  `GroupDiagram.regionLabels` is the owner for oriented face labels, `TwoComplex.GeometricFace` is
  the owner for actual regions, and `Loop` is the owner for the chosen boundary loop.
- `bridge/view`: the disc boundary loop lives on the subcomplex `1`-skeleton and is compared with
  the ambient labelled diagram through `OneComplex.Hom.mapLoop` applied to
  `S.skeleton.inclusion`; finite enumeration of the geometric region set is expressed by an
  equivalence `Fin n ≃ TwoComplex.GeometricFace S.complex`.

Domain sampling:
1. `GroupDiagram` from Definition `5-1-3` is the existing owner abstraction for a diagram over a
   group.
2. `GroupDiagram.regionLabels` from Definition `5-1-4` is the existing owner for the admissible
   labels read around a region boundary.
3. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for a
   singular disc together with its explicit outer boundary cycle.
4. `OneComplex.Hom.mapLoop` applied to `S.skeleton.inclusion` is the canonical bridge from the
   disc boundary loop to the ambient labelled diagram.
5. `IsConj` is mathlib's canonical owner for “is a conjugate of”, so explicit conjugator data are
   derived witnesses rather than primitive public output.

Primitive vs. derived:
- primitive public data: the ambient group diagram `M`, the singular disc subcomplex `S`, and the
  chosen boundary loop `p` recorded in the owner predicate
  `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`;
- derived API: an enumeration of the geometric faces of `S.complex` and an ordered `List` of
  factors whose entries lie in the canonical conjugacy owner
  `conjugatesOfSet (M.regionLabels D.1)` for corresponding oriented representatives `D` of those
  regions, and whose product is the ambient label of the chosen disc boundary loop.
-/

/-- Lemma 5-1-7: if `S` is a singular disc in a group-labelled `2`-complex `M`, then the label of
its chosen outer boundary loop is an ordered product of conjugates of labels chosen from the
regions of `S`. -/
-- Proof sketch: argue by induction on the number of geometric faces of the singular disc. When
-- there is a single face, the boundary label is itself a region label. Otherwise remove an outer
-- face along the disc boundary, apply the induction hypothesis to the remaining singular disc, and
-- reinsert one conjugate of a label read from an oriented representative of the deleted geometric
-- face.
theorem boundaryCycleWord_eq_list_prod_conjugates_of_regionLabels
    (M : GroupDiagram F) (S : M.source.Subcomplex)
    (p : Loop S.skeleton.toOneComplex)
    (hS : S.IsSingularDisc (cyclicPath p)) :
    ∃ cs : List F,
      ∃ e : Fin cs.length ≃ S.complex.GeometricFace,
        (∀ i, ∃ D : S.complex.Face, ⟦D⟧ = e i ∧ cs[i] ∈ conjugatesOfSet (M.regionLabels D.1)) ∧
          let q := mapLoop S.skeleton.inclusion p
          M.pathLabel q.2 = cs.prod := by
  sorry

end

/-! ### Definition_5_1_8 (from Items/Chap05) -/
universe u

set_option autoImplicit false

open Quiver.Path

section

variable {F : Type u} [Group F]

namespace GroupDiagram

/-!
Primary domain: Chapter `5` group-labelled diagrams whose region labels are constrained by a
fixed subset of the ambient group.

Layer triage:
- `source-facing`: an `R`-diagram is a labelled diagram whose region boundary labels all lie in
  `R`.
- `core/canonical`: `GroupDiagram.regionLabels` from Definition `5-1-4` is the owner for the set
  of labels read around a face boundary.
- `bridge/view`: `Loop` and `cyclicPath` give the basepoint-free boundary-cycle presentation used
  to read one particular region label.

Domain sampling:
1. `GroupDiagram` from Definition `5-1-3` is the owner abstraction for labelled oriented maps.
2. `GroupDiagram.regionLabels` from Definition `5-1-4` is the owner for admissible face labels.
3. `GroupDiagram.boundaryCycleLabel_mem_regionLabels` is the canonical bridge from a displayed
   boundary loop to `regionLabels`.
-/

/-- Definition 5-1-8: for a symmetrized subset `R` of `F`, an `R`-diagram is a group diagram
whose label on every boundary cycle of every region belongs to `R`. -/
def IsRDiagram (M : GroupDiagram F) (R : Set F) : Prop :=
  ∀ D : M.source.Face, M.regionLabels D ⊆ R

namespace IsRDiagram

/-- Every region label set of an `R`-diagram is contained in `R`. -/
theorem regionLabels_subset {M : GroupDiagram F} {R : Set F} (hM : M.IsRDiagram R)
    (D : M.source.Face) :
    M.regionLabels D ⊆ R :=
  hM D

/-- In an `R`-diagram, the label read around any boundary cycle of any region belongs to `R`. -/
theorem boundaryCycleLabel_mem {M : GroupDiagram F} {R : Set F} (hM : M.IsRDiagram R)
    (D : M.source.Face) (p : Loop M.source.skeleton) (hp : cyclicPath p = M.source.boundary D) :
    M.pathLabel p.2 ∈ R :=
  hM.regionLabels_subset D (M.boundaryCycleLabel_mem_regionLabels D p hp)

end IsRDiagram

end GroupDiagram

end
