import Mathlib
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_3_1 (from Items/Chap03) -/
universe u v

open CategoryTheory
open Quiver
open Quiver.Path
open scoped Quiver.Path

-- Layer triage:
-- `source-facing`: a morphism of `1`-complexes, the covering-map condition on outgoing oriented
-- edges, and the induced monomorphism on based fundamental groups.
-- `core/canonical`: `OneComplex.Hom` is the chapter owner for morphisms of `1`-complexes,
-- `Quiver.Prefunctor.IsCovering`, `Π¹(C)`, `CategoryTheory.Cat.freeMap`,
-- `CategoryTheory.Quotient.functor`, and `CategoryTheory.Functor.mapEnd` are the owners for the
-- covering condition, the fundamental groupoid, the induced path-category and quotient functors,
-- and the resulting based fundamental group homomorphism, while `Function.Injective` is the owner
-- API for a monomorphism of groups.
-- `bridge/view`: a `1`-complex morphism induces a quiver prefunctor and hence the canonical path
-- and quotient maps; the proposition is stated on `π(C, v)` rather than on raw loop
-- representatives.
-- Domain sampling:
-- 1. `Quiver.Prefunctor` and `Prefunctor.mapPath` are mathlib's owners for maps of quivers and
--    their induced path maps.
-- 2. `Quiver.Prefunctor.IsCovering` is the owner abstraction for coverings of quivers, and in a
--    `1`-complex its star-bijectivity presentation matches the textbook local covering condition.
-- 3. `Quiver.Path.path_one_equiv`, `Quiver.Path.pathOneHomRel`, and `Π¹(C)` are the owners for
--    backtracking-cancellation classes of paths and the resulting quotient groupoid.
-- 4. `CategoryTheory.Cat.freeMap` and `CategoryTheory.Quotient.functor` are the canonical owners
--    for the induced functor on path categories and the resulting map of fundamental groupoids.
-- 5. `OneComplex.fundamentalGroup`, written `π(C, v)`, is the chapter owner for the based
--    fundamental group, and `CategoryTheory.Functor.mapEnd` is the owner for the induced
--    homomorphism on the endomorphism monoids of base objects.

namespace OneComplex

/-- A morphism of `1`-complexes sends vertices to vertices and oriented edges to oriented edges,
preserving endpoints and the edge-reversing involution. -/
structure Hom (C D : OneComplex.{u, v}) where
  /-- The induced map on vertices. -/
  toVertex : C → D
  /-- The induced map on oriented edges. -/
  toEdge : C.Edge → D.Edge
  /-- Initial vertices are preserved. -/
  map_initial (e : C.Edge) : toVertex (C.initial e) = D.initial (toEdge e)
  /-- Terminal vertices are preserved. -/
  map_terminal (e : C.Edge) : toVertex (C.terminal e) = D.terminal (toEdge e)
  /-- Reversing an edge commutes with the edge map. -/
  map_edgeInv (e : C.Edge) : toEdge (C.edgeInv e) = D.edgeInv (toEdge e)

namespace Hom

variable {C D : OneComplex.{u, v}} (f : Hom C D)

/-- Mapping an arrow of the quiver underlying a `1`-complex preserves its initial vertex. -/
-- Proof sketch: unpack the source arrow subtype and rewrite with `f.map_initial`.
theorem mapQuiverEdge_initial {x y : C} (e : x ⟶ y) :
    D.initial (f.toEdge e.1) = f.toVertex x := sorry

/-- Mapping an arrow of the quiver underlying a `1`-complex preserves its terminal vertex. -/
-- Proof sketch: unpack the source arrow subtype and rewrite with `f.map_terminal`.
theorem mapQuiverEdge_terminal {x y : C} (e : x ⟶ y) :
    D.terminal (f.toEdge e.1) = f.toVertex y := sorry

/-- A morphism of `1`-complexes induces a map on arrows in the associated quivers. -/
def mapQuiverEdge {x y : C} (e : x ⟶ y) : f.toVertex x ⟶ f.toVertex y :=
  ⟨f.toEdge e.1, f.mapQuiverEdge_initial e, f.mapQuiverEdge_terminal e⟩

/-- A morphism of `1`-complexes commutes with edge reversal on quiver arrows. -/
-- Proof sketch: extensionality on the underlying edge together with `f.map_edgeInv` identifies
-- the mapped reversed arrow with the reverse of the mapped arrow.
theorem mapQuiverEdge_reverse {x y : C} (e : x ⟶ y) :
    f.mapQuiverEdge (Quiver.reverse e) = Quiver.reverse (f.mapQuiverEdge e) := sorry

/-- The quiver prefunctor underlying a morphism of `1`-complexes. -/
def toPrefunctor : C ⥤q D where
  obj := f.toVertex
  map := f.mapQuiverEdge

/-- The underlying quiver prefunctor of a `1`-complex morphism preserves edge reversal. -/
instance toPrefunctor_mapReverse : f.toPrefunctor.MapReverse where
  map_reverse' e := by
    simpa using f.mapQuiverEdge_reverse e

/-- A morphism of `1`-complexes maps a path by applying the edge map to each oriented edge. -/
abbrev mapPath {x y : C} (p : Quiver.Path x y) : Quiver.Path (f.toVertex x) (f.toVertex y) :=
  f.toPrefunctor.mapPath p

/-- A morphism of `1`-complexes maps a based loop by transporting its base vertex and path. -/
abbrev mapLoop (p : Loop C) : Loop D :=
  ⟨f.toVertex p.1, f.mapPath p.2⟩

/-- A morphism of `1`-complexes maps a total edge by transporting its endpoints and arrow. -/
def mapTotal (e : Quiver.Total C) : Quiver.Total D :=
  ⟨f.toVertex e.left, f.toVertex e.right, f.mapQuiverEdge e.hom⟩

/-- Mapping the cyclically ordered total-edge list of a cyclic path along a `1`-complex
morphism preserves cyclic composability. -/
theorem cycle_chain_mapTotal (c : CyclicPath C) :
    (c.1.map f.mapTotal).Chain Quiver.Total.Composable := by
  rw [Cycle.chain_map]
  exact c.2.imp fun _ _ h ↦ congrArg f.toVertex h

/-- A morphism of `1`-complexes maps a cyclic path by transporting each total edge. -/
def mapCyclicPath (c : CyclicPath C) : CyclicPath D :=
  ⟨c.1.map f.mapTotal, f.cycle_chain_mapTotal c⟩

/-- Path mapping commutes with path reversal. -/
-- Proof sketch: induct on the path, rewrite the last edge with `f.mapQuiverEdge_reverse`, and
-- use the recursive description of `Quiver.Path.reverse`.
theorem mapPath_reverse {x y : C} (p : Quiver.Path x y) :
    f.mapPath p.reverse = (f.mapPath p).reverse := sorry

/-- A morphism of `1`-complexes preserves the elementary cancellation relation on paths. -/
-- Proof sketch: map every path segment and use `f.mapQuiverEdge_reverse` to show that an inserted
-- or deleted spur still has the form `ee⁻¹` after applying `f`.
theorem mapPath_reduction_step {x y : C} {p q : Quiver.Path x y}
    (h : Quiver.Path.path_one_reduction_step p q) :
    Quiver.Path.path_one_reduction_step (f.mapPath p) (f.mapPath q) := sorry

/-- A morphism of `1`-complexes preserves `1`-equivalence of paths. -/
-- Proof sketch: lift `f.mapPath_reduction_step` through the equivalence closure defining
-- `Quiver.Path.path_one_equiv`.
theorem mapPath_path_one_equiv {x y : C} {p q : Quiver.Path x y}
    (h : Quiver.Path.path_one_equiv p q) :
    Quiver.Path.path_one_equiv (f.mapPath p) (f.mapPath q) := sorry

/-- A morphism of `1`-complexes induces the canonical functor on fundamental groupoids. -/
def pi1Functor : Π¹(C) ⥤ Π¹(D) :=
  CategoryTheory.Quotient.lift _
    (Cat.freeMap f.toPrefunctor ⋙
      CategoryTheory.Quotient.functor (Quiver.Path.pathOneHomRel D))
    (by
      intro x y p q h
      sorry)

/-- A morphism of `1`-complexes induces a homomorphism on based fundamental groups. -/
noncomputable def inducedFundamentalGroupHom (x : C) : π(C, x) →* π(D, f.toVertex x) :=
  f.pi1Functor.mapEnd (⟨x⟩ : Π¹(C))

/-- If a morphism sends `x` to `y`, then it induces the usual homomorphism
`π(C, x) → π(D, y)`. -/
noncomputable def inducedFundamentalGroupHomOver (x : C) (y : D) (hxy : f.toVertex x = y) :
    π(C, x) →* π(D, y) :=
  hxy ▸ f.inducedFundamentalGroupHom x

/-- The induced homomorphism on based fundamental groups is computed by mapping loop
representatives. -/
-- Proof sketch: unfold `f.inducedFundamentalGroupHom`; it is the vertex-group map induced by the
-- functor `f.pi1Functor`, whose action on a loop class is represented by `f.mapPath`.
theorem inducedFundamentalGroupHom_apply_path (x : C) (p : Quiver.Path x x) :
    f.inducedFundamentalGroupHom x
      ((CategoryTheory.Quotient.functor (Quiver.Path.pathOneHomRel C)).map p) =
    ((CategoryTheory.Quotient.functor (Quiver.Path.pathOneHomRel D)).map (f.mapPath p)) :=
  sorry

/-- Proposition 3-3-1: if `f : C' → C` is a covering map of `1`-complexes and `v'` is a vertex of
`C'`, then the induced homomorphism
`f.inducedFundamentalGroupHom v' : π(C', v') →* π(C, f.toVertex v')`
is injective, hence a monomorphism of fundamental groups. -/
-- Proof sketch: a quiver covering gives unique lifting of reduced paths from the chosen base
-- vertex via `Prefunctor.IsCovering.pathStar_bijective`; applying this to a loop whose image is
-- trivial shows that the original loop class is already trivial.
theorem inducedFundamentalGroupHom_injective_of_isCovering
    (hf : f.toPrefunctor.IsCovering) (v' : C) :
    Function.Injective (f.inducedFundamentalGroupHom v') := sorry

end Hom

end OneComplex

/-! ### Proposition_3_3_2 (from Items/Chap03) -/
universe u v

namespace OneComplex

/-
Layer triage:
- `source-facing`: a connected `1`-complex `C`, a base vertex `v : C`, a subgroup
  `H ≤ π(C, v)`, and a connected covering of `C` whose induced map on the based fundamental
  group realizes exactly `H`.
- `core/canonical`: `OneComplex.Hom` is the owner abstraction for maps of `1`-complexes,
  `Quiver.Prefunctor.IsCovering` for `φ.toPrefunctor` is the canonical covering-side structure,
  `Hom.inducedFundamentalGroupHomOver` is the induced based fundamental-group homomorphism, and
  `Subgroup` is the owner abstraction for subgroups.
- `bridge/view`: the chosen vertex `v'` over `v` gives an equality `φ.toVertex v' = v`, which
  transports the canonical induced map to codomain `π(C, v)`.

Domain sampling:
1. `OneComplex.Hom` from Proposition `3-3-1` is the chapter owner for morphisms of `1`-complexes.
2. `Quiver.Prefunctor.IsCovering` for `Hom.toPrefunctor` is the owner predicate for coverings of
   the underlying quivers.
3. `Hom.inducedFundamentalGroupHomOver` is the canonical induced map on based fundamental groups.
4. `Subgroup` is the owner abstraction for subgroups of `π(C, v)`.

Primitive vs. derived:
- primitive data: the covering morphism `φ : Hom C' C` with its chosen lift `v'` of `v`, and the
  equality identifying the image of the induced homomorphism with `H`;
- derived API: injectivity of the induced homomorphism, which is already the canonical conclusion
  of Proposition `3-3-1` for any covering map, and hence should not be packaged as primitive
  output here.
-/

/-- Proposition 3-3-2: every subgroup `H ≤ π(C, v)` is realized by a connected covering
`1`-complex over `C`, with a chosen vertex over `v`, such that the induced homomorphism
`π(C', v') → π(C, v)` has image exactly `H`. Injectivity is the canonical downstream consequence
of Proposition `3-3-1` for covering maps. -/
-- Proof sketch: choose a maximal tree in `C`, form the covering complex whose vertices are the
-- right cosets of `H`, use the canonical quiver covering map to show local bijectivity on stars,
-- and apply path lifting to identify the induced fundamental-group map with the subgroup `H`.
theorem exists_connected_covering_inducing_subgroup
    (C : OneComplex.{u, v}) (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C))
    (v : C) (H : Subgroup (π(C, v))) :
    ∃ (C' : OneComplex.{u, v})
      (_ : Quiver.IsStronglyConnected (Quiver.Symmetrify C')) (φ : Hom C' C)
      (_ : φ.toPrefunctor.IsCovering) (v' : C') (hv' : φ.toVertex v' = v),
      (φ.inducedFundamentalGroupHomOver v' v hv').range = H := by
  sorry

end OneComplex

/-! ### Proposition_3_3_3 (from Items/Chap03) -/
/- Proposition 3-3-3: every subgroup of a free group is free.

This source-facing item is exactly the canonical Nielsen-Schreier theorem already available in
mathlib as `subgroupIsFreeOfIsFree`. The geometric covering-space proof sketched in the text gives
an alternative derivation, but it does not change the public statement, so this item stays a
direct recall of the canonical theorem rather than introducing a parallel wrapper. -/
#check subgroupIsFreeOfIsFree

/-! ### Proposition_3_3_4 (from Items/Chap03) -/
open CategoryTheory
open Quiver.Path

namespace TwoComplex

/-
Layer triage:
- `source-facing`: a connected `2`-complex `C`, a base vertex `v : C.skeleton`, a subgroup
`H ≤ π(C, v)`, and a connected covering `2`-complex whose induced map on fundamental groups
identifies the covering group with `H`.
- `core/canonical`: `TwoComplex.Hom`, extending the chapter owner `OneComplex.Hom` on the
  `1`-skeleton, is the source-faithful owner for maps of `2`-complexes,
  `TwoComplex.Hom.IsCoveringMap` is the owner abstraction for coverings of `2`-complexes,
  `Quiver.Prefunctor.IsCovering` for `φ.toPrefunctor` is the canonical owner for the
  `1`-skeleton covering data reused by that class, and `CategoryTheory.Functor.mapEnd` is the
  owner API for the induced map on based fundamental groups.
- `bridge/view`: `TwoComplex.Hom.piFunctor` and
  `TwoComplex.Hom.inducedFundamentalGroupHomOver` are the induced functor on fundamental
  groupoids and its based vertex-group specialization, while `TwoComplex.BoundaryStar` and
  `TwoComplex.Hom.mapBoundaryStar` express the `2`-cell lifting condition using the existing
  path-based `BoundaryPath` owner API.

Domain sampling:
1. `OneComplex.Hom` from Proposition `3-3-1` is the chapter owner for morphisms of `1`-complexes.
2. `TwoComplex.BoundaryPath` is the project owner for a face corner based at a chosen vertex.
3. `Quiver.Prefunctor.IsCovering` is the canonical owner predicate for the `1`-skeleton part of a
   covering, accessed here through `OneComplex.Hom.toPrefunctor`.
4. `OneComplex.Hom.pi1Functor` and `CategoryTheory.Functor.mapEnd` give the chapter/mathlib owner
   pattern for passing from a map of path groupoids to the induced homomorphism on based
   fundamental groups.

Primitive vs. derived:
- primitive data: the skeleton morphism, the face map, and compatibility saying that mapped face
  boundary loops are boundary loops of the image face; for coverings, the primitive extra data is
  the existing `1`-skeleton covering owner together with the bijective lifting condition on based
  boundary paths over each vertex;
- derived API: the induced functor on `2`-dimensional path classes, the induced homomorphism on
  fundamental groups, and injectivity for covering maps.
-/

/-- The boundary star of a vertex records an oriented face together with a chosen boundary path of
that face beginning at the vertex. This is the `2`-cell analogue of the outgoing edge star used
for coverings of `1`-complexes. -/
abbrev BoundaryStar (C : TwoComplex) (v : C.skeleton) :=
  Σ D : C.Face, C.BoundaryPath D v

/-- A morphism of `2`-complexes is a morphism of the underlying `1`-skeletons together with a map
of oriented faces that respects face reversal and sends each boundary loop to the boundary loop of
the image face. -/
structure Hom (C' C : TwoComplex) extends OneComplex.Hom C'.skeleton C.skeleton where
  /-- The induced map on oriented faces. -/
  mapFace : C'.Face → C.Face
  /-- The face map preserves orientation reversal. -/
  map_faceInv (D : C'.Face) :
      mapFace (C'.faceInv D) = C.faceInv (mapFace D)
  /-- The image of a based boundary path of `D` is a based boundary path of `∂(mapFace D)`. -/
  mapBoundary {D : C'.Face} {v : C'.skeleton} (q : C'.BoundaryPath D v) :
      C.BoundaryPath (mapFace D) (toVertex v)

namespace Hom

variable {C' C : TwoComplex} (φ : Hom C' C)

/-- The map induced by a `2`-complex morphism on boundary stars over a chosen vertex. -/
def mapBoundaryStar (v : C'.skeleton) :
    C'.BoundaryStar v → C.BoundaryStar (φ.toVertex v)
  | ⟨D, q⟩ => ⟨φ.mapFace D, φ.mapBoundary q⟩

/-- A morphism of `2`-complexes induces the canonical map on geometric faces. -/
def mapGeometricFace : C'.GeometricFace → C.GeometricFace :=
  Quotient.map' φ.mapFace fun D E h ↦ by
    rcases h with h | h
    · exact Or.inl (congrArg φ.mapFace h)
    · exact Or.inr (by simpa [h] using φ.map_faceInv E)

@[simp] theorem mapGeometricFace_mk (D : C'.Face) :
    φ.mapGeometricFace (⟦D⟧ : C'.GeometricFace) = (⟦φ.mapFace D⟧ : C.GeometricFace) :=
  rfl

/-- A morphism of `2`-complexes is a covering map when it is a covering on the `1`-skeleton and
it bijectively lifts based face-boundary paths at every vertex. -/
class IsCoveringMap : Prop extends φ.toPrefunctor.IsCovering where
  /-- The induced map on incident oriented face corners at any chosen vertex is bijective. -/
  boundaryStar_bijective (v : C'.skeleton) : Function.Bijective (φ.mapBoundaryStar v)

/-- A `2`-complex morphism preserves the boundary-path reduction relation. -/
theorem mapPath_boundary_path_reduction_step {a b : C'.skeleton} {p q : Quiver.Path a b}
    (h : C'.boundary_path_reduction_step p q) :
    C.boundary_path_reduction_step (φ.mapPath p) (φ.mapPath q) := sorry

/-- A `2`-complex morphism preserves elementary `2`-reduction steps. -/
theorem mapPath_path_two_reduction_step {a b : C'.skeleton} {p q : Quiver.Path a b}
    (h : C'.path_two_reduction_step p q) :
    C.path_two_reduction_step (φ.mapPath p) (φ.mapPath q) := by
  rcases h with h | h
  · exact Or.inl (φ.mapPath_reduction_step h)
  · exact Or.inr (φ.mapPath_boundary_path_reduction_step h)

/-- A `2`-complex morphism preserves `2`-equivalence of paths. -/
theorem mapPath_path_two_equiv {a b : C'.skeleton} {p q : Quiver.Path a b}
    (h : C'.path_two_equiv p q) :
    C.path_two_equiv (φ.mapPath p) (φ.mapPath q) := sorry

/-- A morphism of `2`-complexes induces the canonical functor on fundamental groupoids. -/
def piFunctor : C'.pi ⥤ C.pi where
  obj a := ⟨φ.toVertex a.vertex⟩
  map := fun p ↦
    Quotient.map' φ.mapPath (fun _ _ h ↦ φ.mapPath_path_two_equiv h) p
  map_id a := by
    rfl
  map_comp p q := by
    sorry

/-- A `2`-complex morphism induces a homomorphism on based fundamental groups. -/
noncomputable def inducedFundamentalGroupHom (v : C'.skeleton) :
    π(C', v) →* π(C, φ.toVertex v) :=
  φ.piFunctor.mapEnd ⟨v⟩

/-- If a `2`-complex morphism sends `v'` to `v`, then it induces the usual homomorphism
`π(C', v') → π(C, v)`. -/
noncomputable def inducedFundamentalGroupHomOver (v' : C'.skeleton) (v : C.skeleton)
    (hv : φ.toVertex v' = v) :
    π(C', v') →* π(C, v) :=
  hv ▸ φ.inducedFundamentalGroupHom v'

/-- A covering map of `2`-complexes induces an injective homomorphism on based fundamental
groups. -/
theorem inducedFundamentalGroupHomOver_injective_of_isCoveringMap
    (hφ : IsCoveringMap φ) (v' : C'.skeleton) (v : C.skeleton) (hv : φ.toVertex v' = v) :
    Function.Injective (φ.inducedFundamentalGroupHomOver v' v hv) := sorry

end Hom

/-- Proposition 3-3-4: for any subgroup `H ≤ π(C, v)` of the fundamental group of a connected
`2`-complex `C`, there exists a connected covering `2`-complex `C' → C` with a chosen vertex `v'`
over `v` whose induced homomorphism `π(C', v') → π(C, v)` has image exactly `H`; injectivity is
the canonical consequence of the covering-map owner. -/
-- Proof sketch: first build the covering of the `1`-skeleton corresponding to the subgroup of
-- `π(C.skeleton, v)` from Proposition `3-3-2`. Then attach a `2`-cell over each lifted boundary
-- loop of a face of `C`, obtaining a connected `2`-complex covering whose induced map on
-- fundamental groups has image `H`; injectivity follows from covering-space lifting.
theorem exists_connected_covering_inducing_subgroup
    (C : TwoComplex) (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    (v : C.skeleton)
    (H : Subgroup (π(C, v))) :
    ∃ (C' : TwoComplex)
      (_ : Quiver.IsStronglyConnected (Quiver.Symmetrify C'.skeleton)) (φ : Hom C' C)
      (_ : Hom.IsCoveringMap φ) (v' : C'.skeleton) (hv' : φ.toVertex v' = v),
      (φ.inducedFundamentalGroupHomOver v' v hv').range = H := sorry

end TwoComplex

/-! ### Proposition_3_3_5 (from Items/Chap03) -/
universe u v w uI

open Monoid
open Quiver.Path

noncomputable section

namespace OneComplex

variable (C : OneComplex.{u, v})

/-- A subcomplex of a `1`-complex is given by vertex and edge subsets closed under endpoints and
edge reversal. -/
structure Subcomplex (C : OneComplex.{u, v}) where
  /-- The vertices belonging to the subcomplex. -/
  vertexSet : Set C
  /-- The oriented edges belonging to the subcomplex. -/
  edgeSet : Set C.Edge
  /-- The initial vertex of every edge of the subcomplex again lies in the subcomplex. -/
  initial_mem {e : C.Edge} : e ∈ edgeSet → C.initial e ∈ vertexSet
  /-- The terminal vertex of every edge of the subcomplex again lies in the subcomplex. -/
  terminal_mem {e : C.Edge} : e ∈ edgeSet → C.terminal e ∈ vertexSet
  /-- The reverse of every edge of the subcomplex again lies in the subcomplex. -/
  edgeInv_mem {e : C.Edge} : e ∈ edgeSet → C.edgeInv e ∈ edgeSet

namespace Subcomplex

variable {C : OneComplex.{u, v}}

/-- A geometric edge belongs to a subcomplex when one, equivalently every, oriented
representative belongs to its oriented edge set. -/
def ContainsGeometricEdge (S : Subcomplex C) : GeometricEdge C → Prop :=
  Quotient.lift
    (fun e ↦ e ∈ S.edgeSet)
    (fun e f h ↦ by
      apply propext
      rcases h with rfl | rfl
      · rfl
      · constructor
        · intro he
          change C.edgeInv f ∈ S.edgeSet at he
          have hf : C.edgeInv (C.edgeInv f) ∈ S.edgeSet := S.edgeInv_mem he
          exact (C.edgeInv_involutive f) ▸ hf
        · intro he
          change C.edgeInv f ∈ S.edgeSet
          exact S.edgeInv_mem he)

/-- A geometric edge represented by `e` belongs to the subcomplex exactly when `e` itself belongs
to the oriented edge set. -/
@[simp] theorem containsGeometricEdge_mk_iff
    (S : Subcomplex C) (e : C.Edge) :
    S.ContainsGeometricEdge ⟦e⟧ ↔ e ∈ S.edgeSet :=
  Iff.rfl

/-- A subcomplex inherits a canonical `1`-complex structure from the ambient complex. -/
def toOneComplex (K : Subcomplex C) : OneComplex where
  Vertex := { v : C // v ∈ K.vertexSet }
  Edge := { e : C.Edge // e ∈ K.edgeSet }
  initial := fun e ↦ ⟨C.initial e.1, K.initial_mem e.2⟩
  terminal := fun e ↦ ⟨C.terminal e.1, K.terminal_mem e.2⟩
  edgeInv := fun e ↦ ⟨C.edgeInv e.1, K.edgeInv_mem e.2⟩
  edgeInv_involutive := fun e ↦ Subtype.ext (C.edgeInv_involutive e.1)
  edgeInv_ne := fun e h ↦ C.edgeInv_ne e.1 (congrArg Subtype.val h)
  initial_edgeInv := fun e ↦ by
    apply Subtype.ext
    exact C.initial_edgeInv e.1

/-- The canonical inclusion of a subcomplex into the ambient `1`-complex. -/
def inclusion (K : Subcomplex C) : OneComplex.Hom K.toOneComplex C where
  toVertex := fun v ↦ v.1
  toEdge := fun e ↦ e.1
  map_initial _ := rfl
  map_terminal _ := rfl
  map_edgeInv _ := rfl

/-- A nested subcomplex includes canonically into the larger carried `1`-complex. -/
def inclusionOfSubset {S T : Subcomplex C}
    (hvertex : S.vertexSet ⊆ T.vertexSet) (hedge : S.edgeSet ⊆ T.edgeSet) :
    OneComplex.Hom S.toOneComplex T.toOneComplex where
  toVertex := fun v ↦ ⟨v.1, hvertex v.2⟩
  toEdge := fun e ↦ ⟨e.1, hedge e.2⟩
  map_initial _ := Subtype.ext rfl
  map_terminal _ := Subtype.ext rfl
  map_edgeInv _ := Subtype.ext rfl

/-- Mapping a cyclic path through a nested subcomplex inclusion and then through the ambient
inclusion agrees with mapping it directly through the smaller ambient inclusion. -/
theorem inclusion_mapCyclicPath_inclusionOfSubset
    {S T : Subcomplex C}
    (hvertex : S.vertexSet ⊆ T.vertexSet) (hedge : S.edgeSet ⊆ T.edgeSet)
    (c : CyclicPath S.toOneComplex) :
    T.inclusion.mapCyclicPath ((inclusionOfSubset hvertex hedge).mapCyclicPath c) =
      S.inclusion.mapCyclicPath c := by
  rcases c with ⟨c, hc⟩
  apply Subtype.ext
  change Cycle.map T.inclusion.mapTotal (Cycle.map (inclusionOfSubset hvertex hedge).mapTotal c) =
    Cycle.map S.inclusion.mapTotal c
  refine Quotient.inductionOn' c ?_
  intro l
  apply Cycle.coe_eq_coe.2
  simpa [List.map_map, OneComplex.Hom.mapTotal, OneComplex.Subcomplex.inclusion,
    OneComplex.Subcomplex.inclusionOfSubset, Function.comp] using
    List.IsRotated.refl (List.map S.inclusion.mapTotal l)

/-- The intersection of a family of subcomplexes is again a subcomplex. -/
def iInter {ι : Sort uI} (K : ι → Subcomplex C) : Subcomplex C where
  vertexSet := { v | ∀ i, v ∈ (K i).vertexSet }
  edgeSet := { e | ∀ i, e ∈ (K i).edgeSet }
  initial_mem h i := (K i).initial_mem (h i)
  terminal_mem h i := (K i).terminal_mem (h i)
  edgeInv_mem h i := (K i).edgeInv_mem (h i)

@[inherit_doc iInter] scoped notation3 "⋂ " (...)", " r:60:(scoped K => iInter K) => r

@[simp] theorem mem_vertexSet_iInter {ι : Sort uI} (K : ι → Subcomplex C) {v : C} :
    v ∈ (iInter K).vertexSet ↔ ∀ i, v ∈ (K i).vertexSet :=
  Iff.rfl

@[simp] theorem mem_edgeSet_iInter {ι : Sort uI} (K : ι → Subcomplex C) {e : C.Edge} :
    e ∈ (iInter K).edgeSet ↔ ∀ i, e ∈ (K i).edgeSet :=
  Iff.rfl

/-- The common intersection of a family of subcomplexes includes canonically into each summand. -/
def iInterInclusion {ι : Sort uI} (K : ι → Subcomplex C) (i : ι) :
    OneComplex.Hom (⋂ j, K j).toOneComplex (K i).toOneComplex :=
  inclusionOfSubset
    (fun _ hv ↦ (mem_vertexSet_iInter K).1 hv i)
    (fun _ he ↦ (mem_edgeSet_iInter K).1 he i)

/-- The union of two subcomplexes is obtained by taking the unions of their vertex and edge
carriers. -/
def union (K L : Subcomplex C) : Subcomplex C where
  vertexSet := K.vertexSet ∪ L.vertexSet
  edgeSet := K.edgeSet ∪ L.edgeSet
  initial_mem h := by
    rcases h with h | h
    · exact Or.inl <| K.initial_mem h
    · exact Or.inr <| L.initial_mem h
  terminal_mem h := by
    rcases h with h | h
    · exact Or.inl <| K.terminal_mem h
    · exact Or.inr <| L.terminal_mem h
  edgeInv_mem h := by
    rcases h with h | h
    · exact Or.inl <| K.edgeInv_mem h
    · exact Or.inr <| L.edgeInv_mem h

/-- The left summand of a union is vertexwise contained in that union. -/
theorem vertexSet_subset_union_left (K L : Subcomplex C) :
    K.vertexSet ⊆ (union K L).vertexSet := fun _ hv ↦ Or.inl hv

/-- The left summand of a union is edgewise contained in that union. -/
theorem edgeSet_subset_union_left (K L : Subcomplex C) :
    K.edgeSet ⊆ (union K L).edgeSet := fun _ he ↦ Or.inl he

/-- The right summand of a union is vertexwise contained in that union. -/
theorem vertexSet_subset_union_right (K L : Subcomplex C) :
    L.vertexSet ⊆ (union K L).vertexSet := fun _ hv ↦ Or.inr hv

/-- The right summand of a union is edgewise contained in that union. -/
theorem edgeSet_subset_union_right (K L : Subcomplex C) :
    L.edgeSet ⊆ (union K L).edgeSet := fun _ he ↦ Or.inr he

end Subcomplex

end OneComplex

namespace OneComplex.Subcomplex

variable {C : OneComplex}

/-- The total-edge map induced by a subcomplex inclusion is injective. -/
theorem mapTotal_injective (K : Subcomplex C) :
    Function.Injective K.inclusion.mapTotal := by
  sorry

end OneComplex.Subcomplex

namespace TwoComplex

/-- A subcomplex of a `2`-complex is given by a subcomplex of the ambient `1`-skeleton together
with a family of ambient faces whose canonical attaching cycles already lie in that
`1`-skeleton subcomplex. -/
structure Subcomplex (C : TwoComplex.{w}) where
  /-- The underlying subcomplex of the ambient `1`-skeleton. -/
  skeleton : OneComplex.Subcomplex C.skeleton
  /-- The ambient faces belonging to the subcomplex. -/
  faceSet : Set C.Face
  /-- The face set is closed under orientation reversal. -/
  faceInv_mem {D : C.Face} : D ∈ faceSet → C.faceInv D ∈ faceSet
  /-- The boundary cycle of a face belonging to the subcomplex, regarded in the subcomplex
  `1`-skeleton. -/
  boundary (D : { D : C.Face // D ∈ faceSet }) : CyclicPath (skeleton.toOneComplex)
  /-- The subcomplex boundary cycle maps to the ambient attaching cycle. -/
  boundary_eq (D : { D : C.Face // D ∈ faceSet }) :
      skeleton.inclusion.mapCyclicPath (boundary D) = C.boundary D.1

namespace Subcomplex

variable {C : TwoComplex.{w}}

/-- A geometric face belongs to a subcomplex when one, equivalently every, oriented
representative belongs to its oriented face set. -/
def ContainsGeometricFace (S : Subcomplex C) : GeometricFace C → Prop :=
  Quotient.lift
    (fun D ↦ D ∈ S.faceSet)
    (fun D E h ↦ by
      apply propext
      rcases h with rfl | rfl
      · rfl
      · constructor
        · intro hD
          change C.faceInv E ∈ S.faceSet at hD
          have hE : C.faceInv (C.faceInv E) ∈ S.faceSet := S.faceInv_mem hD
          exact (C.faceInv_involutive E) ▸ hE
        · intro hD
          change C.faceInv E ∈ S.faceSet
          exact S.faceInv_mem hD)

/-- A geometric face represented by `D` belongs to the subcomplex exactly when `D` itself belongs
to the oriented face set. -/
@[simp] theorem containsGeometricFace_mk_iff
    (S : Subcomplex C) (D : C.Face) :
    S.ContainsGeometricFace ⟦D⟧ ↔ D ∈ S.faceSet :=
  Iff.rfl

/-- The ambient total-edge map of a `2`-complex subcomplex reflects cyclic reduction. -/
theorem isCyclicallyReducedCycle_mapCyclicPath_iff (S : Subcomplex C)
    (c : CyclicPath S.skeleton.toOneComplex) :
    IsCyclicallyReducedCycle (S.skeleton.inclusion.mapCyclicPath c) ↔
      IsCyclicallyReducedCycle c := by
  sorry

/-- Mapping the inverse of a cyclic path along the inclusion of a subcomplex agrees with taking
the inverse after mapping. -/
theorem mapCyclicPath_inverseCycle (S : Subcomplex C)
    (c : CyclicPath S.skeleton.toOneComplex) :
    S.skeleton.inclusion.mapCyclicPath (inverseCycle c) =
      inverseCycle (S.skeleton.inclusion.mapCyclicPath c) := by
  sorry

/-- The ambient cyclic-path map induced by a subcomplex inclusion is injective. -/
theorem mapCyclicPath_injective (S : Subcomplex C) :
    Function.Injective S.skeleton.inclusion.mapCyclicPath := by
  sorry

/-- The `2`-complex carried by a subcomplex of an ambient `2`-complex. -/
def complex (S : Subcomplex C) : TwoComplex where
  skeleton := S.skeleton.toOneComplex
  Face := { D : C.Face // D ∈ S.faceSet }
  boundary := S.boundary
  boundary_cyclicallyReduced := by
    intro D
    have h : IsCyclicallyReducedCycle (S.skeleton.inclusion.mapCyclicPath (S.boundary D)) := by
      simpa [S.boundary_eq D] using C.boundary_cyclicallyReduced D.1
    exact (S.isCyclicallyReducedCycle_mapCyclicPath_iff (S.boundary D)).1 h
  faceInv := fun D ↦ ⟨C.faceInv D.1, S.faceInv_mem D.2⟩
  faceInv_involutive := by
    intro D
    ext
    exact C.faceInv_involutive D.1
  faceInv_ne := by
    intro D h
    exact C.faceInv_ne D.1 (congrArg Subtype.val h)
  boundary_faceInv := by
    intro D
    apply S.mapCyclicPath_injective
    rw [S.boundary_eq ⟨C.faceInv D.1, S.faceInv_mem D.2⟩, S.mapCyclicPath_inverseCycle,
      S.boundary_eq D]
    exact C.boundary_faceInv D.1

/-- Restricting a subcomplex to an inverse-closed face subset keeps the same `1`-skeleton and
inherits the boundary data from the ambient subcomplex. -/
def restrictFaces (S : Subcomplex C) (faceSet : Set C.Face) (hfaceSet : faceSet ⊆ S.faceSet)
    (hfaceInv : ∀ ⦃D : C.Face⦄, D ∈ faceSet → D⁻¹ ∈ faceSet) : Subcomplex C where
  skeleton := S.skeleton
  faceSet := faceSet
  faceInv_mem := fun hD ↦ hfaceInv hD
  boundary := fun D ↦ S.boundary ⟨D.1, hfaceSet D.2⟩
  boundary_eq := fun D ↦ S.boundary_eq ⟨D.1, hfaceSet D.2⟩

/-- Restricting to one geometric face keeps exactly one oriented face of `S` together with its
inverse. This is the canonical one-face specialization of `restrictFaces`. -/
def restrictFace (S : Subcomplex C) (D : C.Face) (hD : D ∈ S.faceSet) : Subcomplex C :=
  S.restrictFaces
    { E | E = D ∨ E = D⁻¹ }
    (fun E hE ↦ by
      rcases hE with rfl | rfl
      · exact hD
      · exact S.faceInv_mem hD)
    (fun {E} hE ↦ by
      rcases hE with rfl | hE
      · exact Or.inr rfl
      · exact Or.inl <| by simpa [hE] using C.faceInv_involutive D)

/-- The union of two subcomplexes is obtained by taking the union of their `1`-skeleta and face
sets. -/
def union (S T : Subcomplex C) : Subcomplex C where
  skeleton := S.skeleton.union T.skeleton
  faceSet := S.faceSet ∪ T.faceSet
  faceInv_mem h := by
    rcases h with h | h
    · exact Or.inl <| S.faceInv_mem h
    · exact Or.inr <| T.faceInv_mem h
  boundary D := by
    classical
    by_cases hD : D.1 ∈ S.faceSet
    · exact
        (OneComplex.Subcomplex.inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_left S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_left S.skeleton T.skeleton)).mapCyclicPath
          (S.boundary ⟨D.1, hD⟩)
    · exact
        (OneComplex.Subcomplex.inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_right S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_right S.skeleton T.skeleton)).mapCyclicPath
          (T.boundary ⟨D.1, Or.resolve_left D.2 hD⟩)
  boundary_eq D := by
    classical
    by_cases hD : D.1 ∈ S.faceSet
    · simpa [hD] using
        (OneComplex.Subcomplex.inclusion_mapCyclicPath_inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_left S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_left S.skeleton T.skeleton)
          (S.boundary ⟨D.1, hD⟩)).trans
          (S.boundary_eq ⟨D.1, hD⟩)
    · simpa [hD] using
        (OneComplex.Subcomplex.inclusion_mapCyclicPath_inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_right S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_right S.skeleton T.skeleton)
          (T.boundary ⟨D.1, Or.resolve_left D.2 hD⟩)).trans
          (T.boundary_eq ⟨D.1, Or.resolve_left D.2 hD⟩)

/-- A face-boundary vertex of a nested subcomplex remains a face-boundary vertex in the parent
subcomplex. -/
theorem vertexOnFace_of_subset (S T : Subcomplex C)
    (hvertex : T.skeleton.vertexSet ⊆ S.skeleton.vertexSet)
    (hedge : T.skeleton.edgeSet ⊆ S.skeleton.edgeSet)
    (hface : T.faceSet ⊆ S.faceSet)
    {v : T.complex.skeleton} {D : T.complex.Face} :
    T.complex.VertexOnFace v D →
      S.complex.VertexOnFace ⟨v.1, hvertex v.2⟩ ⟨D.1, hface D.2⟩ := by
  sorry

end Subcomplex

/-- Proposition 3-3-5: if a `2`-complex `C` is the union of a family of subcomplexes indexed by
`I`, all containing the same base vertex `v`, and distinct subcomplexes meet only in that vertex,
then the fundamental group `π(C, v)` is isomorphic to the indexed free product of the
fundamental groups of the subcomplexes. -/
-- Layer triage:
-- `source-facing`: an ambient `2`-complex `C`, a family of subcomplexes `pieces i`, a common
-- base vertex `v`, and the free-product decomposition of `π(C, v)`.
-- `core/canonical`: `TwoComplex.fundamentalGroup`, written `π(C, v)`, is the chapter owner for
-- the ambient and piecewise fundamental groups, `Monoid.CoprodI` is mathlib's owner for indexed
-- free products, `OneComplex.Subcomplex` is the upstream owner for the `1`-skeleton part of
-- each subcomplex, and `Quiver.Path.CyclicPath` is the owner for canonical face-boundary data.
-- `bridge/view`: `TwoComplex.Subcomplex` adds only the ambient face subset together with the
-- internal cyclic boundary data needed to view those faces as a genuine `2`-dimensional
-- subcomplex.
-- Domain sampling:
-- 1. `OneComplex.Subcomplex` is the project owner for subcomplexes of the `1`-skeleton.
-- 2. `OneComplex.Subcomplex.toOneComplex` is the derived `1`-complex carried by such a
--    subcomplex.
-- 3. `Quiver.Path.CyclicPath` is the canonical owner for face boundaries, and
--    `OneComplex.Hom.mapCyclicPath` applied to the inclusion `skeleton.inclusion` is the bridge
--    API comparing internal boundary cycles with ambient attaching cycles.
-- 4. `TwoComplex.fundamentalGroup`, written `π(C, v)`, and `Monoid.CoprodI` are the canonical
--    owners in the conclusion.
-- Proof sketch: choose maximal trees in the pieces through the common base vertex, observe that
-- their union is a maximal tree in `C`, identify the fundamental group of the `1`-skeleton with
-- the free product of the piecewise `1`-skeleton groups, and then show that the face relations of
-- `C` are exactly the union of the face relations contributed by the subcomplexes.
theorem fundamentalGroup_nonempty_mulEquiv_coprodI_of_subcomplex_cover
    {I : Type uI} (C : TwoComplex.{w}) (pieces : I → Subcomplex C) (v : C.skeleton)
    (hv : ∀ i, v ∈ (pieces i).skeleton.vertexSet)
    (hcover_vertex : ∀ x : C.skeleton, ∃ i, x ∈ (pieces i).skeleton.vertexSet)
    (hcover_edge : ∀ e : C.skeleton.Edge, ∃ i, e ∈ (pieces i).skeleton.edgeSet)
    (hcover_face : ∀ D : C.Face, ∃ i, D ∈ (pieces i).faceSet)
    (hinter_vertex :
      ∀ {i j : I} (hij : i ≠ j) {x : C.skeleton},
        x ∈ (pieces i).skeleton.vertexSet →
        x ∈ (pieces j).skeleton.vertexSet →
        x = v)
    (hdisjoint_edge :
      ∀ {i j : I} (hij : i ≠ j) {e : C.skeleton.Edge},
        e ∈ (pieces i).skeleton.edgeSet →
        e ∈ (pieces j).skeleton.edgeSet →
        False)
    (hdisjoint_face :
      ∀ {i j : I} (hij : i ≠ j) {D : C.Face},
        D ∈ (pieces i).faceSet →
        D ∈ (pieces j).faceSet →
        False) :
    Nonempty (π(C, v) ≃* CoprodI (fun i ↦ π((pieces i).complex, ⟨v, hv i⟩))) := sorry

end TwoComplex

/-! ### Proposition_3_3_6 (from Items/Chap03) -/
universe u v w

open Monoid
open scoped Pointwise

section

variable {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)]

-- Layer triage:
-- `source-facing`: a subgroup `H` of the indexed free product `CoprodI G`, together with a
-- decomposition of `H` as a free product of one free group and subgroup factors of `H` whose
-- ambient images are conjugates of subgroups of the ambient free factors.
-- `core/canonical`: `CoprodI` is mathlib's owner for indexed free products, `IsFreeGroup` is the
-- owner predicate for freeness, and subgroup conjugation is expressed using `MulAut.conj`
-- together with `Subgroup.map`.
-- `bridge/view`: the Chapter 1 owner `IsKuroshFactorDecomposition` packages the distinguished
-- free subgroup together with the subgroup factors into a `CoprodI` decomposition; the extra
-- source-facing content here is only the ambient conjugacy description of the factors.
-- Domain sampling:
-- 1. `CoprodI` and `CoprodI.of` are the canonical indexed free-product owners.
-- 2. `IsFreeGroup` is the canonical owner for the free group factor in the decomposition.
-- 3. `IsKuroshFactorDecomposition` from Proposition `1-11-24` is the project owner for the
--    underlying free-product decomposition data.
-- 4. `Subgroup.map`, `Subgroup.subtype`, and `MulAut.conj` are the standard subgroup and
--    conjugation APIs needed to express the Kurosh factors.

-- Primitive vs. derived:
-- the primitive source-facing data are the subgroup `H`, the distinguished free subgroup factor
-- `F ≤ H`, the subgroup-factor family `K : J → Subgroup H`, and the free-product equivalence
-- `CoprodI (kuroshFactorFamily F K) ≃* H`; the ambient conjugacy description of each `K j` is the
-- extra source-facing property asserted in this proposition.

/-- Proposition 3-3-6: every subgroup of an indexed free product is itself a free product of one
free group together with subgroup factors lying in the subgroup and equal in the ambient free
product to conjugates of subgroups of the original free factors. -/
-- Proof sketch: realize the ambient free product as the fundamental group of a complex obtained by
-- wedging complexes for the factors, then apply the covering-space description of subgroups from
-- Proposition 3-3-4. Decompose the lifted complex using Proposition 3-3-5; the components lying
-- above the original factor complexes contribute the conjugate subgroup factors, and the remaining
-- tree-complement contributes the free factor.
theorem exists_kurosh_freeProduct_decomposition
    (H : Subgroup (CoprodI G)) :
    ∃ (J : Type w) (K : J → Subgroup H) (F : Subgroup H)
      (e : CoprodI (kuroshFactorFamily F K) ≃* H),
      IsKuroshFactorDecomposition H K F e ∧
        ∀ j, ∃ i : ι, ∃ g : CoprodI G, ∃ L : Subgroup (G i),
          Subgroup.map H.subtype (K j) =
            MulAut.conj g • Subgroup.map (CoprodI.of : G i →* CoprodI G) L := sorry

end

/-! ### Proposition_3_3_7 (from Items/Chap03) -/
universe u v w

open Monoid

section

variable {ι : Type v} {F : Type u} {A : ι → Type w}
variable [Group F] [IsFreeGroup F] [Group.FG F]
variable [∀ i, Group (A i)]

-- Primary domain: indexed free products of groups and free-group decompositions.
--
-- Layer triage:
-- `source-facing`: a finitely generated free group `F`, a surjection `φ : F →* CoprodI A`
-- onto an indexed free product, and a family of subgroup factors in `F` mapping onto the given
-- factors.
-- `core/canonical`: `IsFreeGroup` is the owner predicate for free groups, `CoprodI` is the
-- owner abstraction for indexed free products, and `Subgroup.map` expresses the image of each
-- subgroup factor under `φ`.
-- `bridge/view`: the equality `F = * F_λ` is rendered by an isomorphism from the indexed free
-- product of subgroup factors onto `F` whose canonical inclusions agree with the subgroup
-- embeddings.
-- Domain sampling:
-- 1. `CoprodI` with its canonical inclusions `CoprodI.of` is the owner abstraction
--    for indexed free products.
-- 2. `CoprodI.lift` is the universal-property owner that would control the eventual proof.
-- 3. `IsFreeGroup` together with `[Group.FG F]` is the chapter/mathlib owner interface for a
--    finitely generated free group; any chosen finite basis is derived data.
-- 4. `Subgroup.map` is the canonical owner for the image condition `F_λ φ = A_λ`.
--
-- Primitive vs. derived:
-- the primitive public data are the finitely generated free group `F`, the factor family `A`, and
-- the surjection `φ : F →* CoprodI A`; the subgroup family `H`, the free-product equivalence
-- `CoprodI (fun i ↦ H i) ≃* F`, and the factor-image equalities are all derived API.

/-- Proposition 3-3-7: if a finitely generated free group `F` surjects onto a nonempty indexed
free product `CoprodI A`, then `F` splits as an indexed free product of subgroup factors whose
images under the surjection are exactly the canonical factor subgroups of `CoprodI A`. -/
-- Proof sketch: choose a finite graph model for `F` and refine the quotient map to a labelled
-- complex over the free product. Modify the complex by adjoining binding ties until the common
-- intersection of the factor subcomplexes is a tree. Seifert-van Kampen then identifies `F` with
-- the free product of the factor subgroups, and surjectivity of `φ` forces each factor image to be
-- the corresponding canonical factor subgroup.
theorem exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct
    (hι : Nonempty ι) (φ : F →* CoprodI A) (hφ : Function.Surjective φ) :
    ∃ H : ι → Subgroup F, ∃ e : CoprodI (fun i ↦ H i) ≃* F,
      (∀ i, e.toMonoidHom.comp CoprodI.of = (H i).subtype) ∧
      ∀ i, Subgroup.map φ (H i) = (CoprodI.of : A i →* CoprodI A).range := sorry

end

/-! ### Lemma_3_3_8 (from Items/Chap03) -/
universe u v w x

open Monoid
open Quiver

namespace OneComplex

namespace Subcomplex

variable {ι : Type w} {K : OneComplex.{u, v}}

-- Layer triage:
-- `source-facing`: an ambient `1`-complex `K`, a family of subcomplexes `K_λ`, a vertex-labelling
-- into an indexed free product, and the resulting notion of a binding tie.
-- `core/canonical`: `OneComplex`, `OneComplex.Subcomplex`, `OneComplex.Hom`,
-- `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `Quiver.Path (Quiver.Symmetrify _)`,
-- `CoprodI`, and `MonoidHom.range` are the owner abstractions for the ambient graph, the
-- subcomplexes, connectedness, ambient and
-- internal zigzag paths, and the target free product.
-- `bridge/view`: `Subcomplex.toOneComplex` and the canonical hom
-- `Subcomplex.iInterInclusion` convert the
-- source-facing subcomplex data to the canonical ambient/path owners.
--
-- Domain sampling:
-- 1. `OneComplex.Subcomplex` is the source-facing owner for the subcomplexes `K_λ`.
-- 2. `OneComplex.Hom` from Proposition `3-3-1` is the chapter owner for maps of carried
--    `1`-complexes, so the intersection inclusion should be phrased through that owner rather
--    than as a raw quiver prefunctor.
-- 3. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)` is the canonical owner for connectedness
--    of a reversible `1`-skeleton.
-- 4. `Quiver.Path (Quiver.Symmetrify K)` is the canonical path owner specialized to
--    symmetrified `1`-complexes.
-- 5. `CoprodI`, `CoprodI.of`, and `MonoidHom.range` are the owner abstractions for
--    the indexed free product and its canonical factor subgroups.

variable {A : ι → Type x} [∀ i, Group (A i)]

/-- A zigzag path in a `1`-complex is a path in its symmetrified quiver. -/
abbrev ZigzagPath {C : OneComplex.{u, v}} (a b : C) : Type _ :=
  @Quiver.Path (Quiver.Symmetrify C) _ a b

/-- The label displacement between two endpoints in the ambient free product. -/
def endpointDisplacement (label : K → CoprodI A) (a b : K) : CoprodI A :=
  (label a)⁻¹ * label b

/-- The source-facing labelled free-product context for a family `K_λ`: each `K_λ` is connected,
and the endpoint displacement between any two of its vertices lies in the corresponding
free-product factor. -/
class IsFreeProductLabelledFamily (Ksub : ι → Subcomplex K) (label : K → CoprodI A) : Prop where
  /-- Each subcomplex `K_λ` is connected. -/
  connected (i : ι) :
    Quiver.IsStronglyConnected (Quiver.Symmetrify (Ksub i).toOneComplex)
  /-- The label displacement between vertices of `K_λ` lies in the `λ`-factor subgroup. -/
  endpointDisplacement_mem_factor
      (i : ι) (start finish : (Ksub i).toOneComplex) :
      endpointDisplacement label start.1 finish.1 ∈
        (CoprodI.of : A i →* CoprodI A).range

/-- A binding tie is a path lying in one `K_λ`, with trivial image in the ambient indexed free
product, whose endpoints lie in different connected components of `⋂ K_λ`. -/
structure BindingTie (Ksub : ι → Subcomplex K) (label : K → CoprodI A) where
  /-- The chosen index `λ` for the subcomplex containing the tie. -/
  index : ι
  /-- The initial vertex of the tie lies in the common intersection. -/
  start : (⋂ i, Ksub i).toOneComplex
  /-- The terminal vertex of the tie lies in the common intersection. -/
  finish : (⋂ i, Ksub i).toOneComplex
  /-- The endpoints of the tie belong to different components of the common intersection. -/
  separated : ¬ Nonempty (ZigzagPath start finish)
  /-- The underlying zigzag path of the tie lies in the chosen subcomplex `K_λ`. -/
  path : ZigzagPath
      ((iInterInclusion Ksub index).toVertex start)
      ((iInterInclusion Ksub index).toVertex finish)
  /-- The endpoint displacement of the tie is trivial in the ambient free product. -/
  displacement_eq_one : endpointDisplacement label start.1 finish.1 = 1

private theorem coprodI_eq_one_of_mem_two_factors {i j : ι} (hij : i ≠ j) {g : CoprodI A}
    (hi : g ∈ (CoprodI.of : A i →* CoprodI A).range)
    (hj : g ∈ (CoprodI.of : A j →* CoprodI A).range) : g = 1 := by
  classical
  rcases hi with ⟨a, rfl⟩
  rcases hj with ⟨b, hab⟩
  have hproj :
      CoprodI.lift (Pi.mulSingle i (MonoidHom.id (A i))) (CoprodI.of a : CoprodI A) =
        CoprodI.lift (Pi.mulSingle i (MonoidHom.id (A i))) (CoprodI.of b : CoprodI A) := by
    simpa using (congrArg (CoprodI.lift (Pi.mulSingle i (MonoidHom.id (A i)))) hab).symm
  have ha : a = 1 := by
    simpa [hij] using hproj
  simp [ha]

/-- Lemma 3-3-8: in the labelled free-product setting, if the common intersection `⋂ K_λ` is not
connected, then any two distinct factors produce a binding tie in the chosen `i`-factor.

The source-facing data are the family `K_λ`, the ambient vertex-labelling into the indexed free
product, and the standard free-product property that endpoint displacements inside `K_λ` land in
the `λ`-factor subgroup. The trivial-image condition is derived by comparing the same endpoint pair
through two distinct factors, rather than assumed as an extra bridge hypothesis. -/
-- Proof sketch: choose two vertices of `⋂ K_λ` lying in different components. Since `Kᵢ` and `Kⱼ`
-- are connected, there are paths between these vertices inside each of the two factors. The two
-- endpoint displacements coincide by definition, while the labelled free-product hypotheses force
-- that common displacement to lie in the `i`- and `j`-factors respectively. Distinct free-product
-- factors intersect trivially, so the common displacement is `1`; the path in `Kᵢ` is therefore a
-- binding tie.
theorem exists_bindingTie_of_intersection_not_connected
    (Ksub : ι → Subcomplex K) (label : K → CoprodI A)
    (hlabel : IsFreeProductLabelledFamily Ksub label)
    (i j : ι) (hij : i ≠ j)
    (hnot :
      ¬ Quiver.IsStronglyConnected (Quiver.Symmetrify ((⋂ i, Ksub i).toOneComplex))) :
    ∃ tie : BindingTie Ksub label, tie.index = i := by
  classical
  have hseparated :
      ∃ start finish : (⋂ i, Ksub i).toOneComplex, ¬ Nonempty (ZigzagPath start finish) := by
    by_contra hseparated
    apply hnot
    intro start finish
    by_contra hpath'
    exact hseparated ⟨start, finish, hpath'⟩
  rcases hseparated with ⟨start, finish, hseparated⟩
  let starti := (iInterInclusion Ksub i).toVertex start
  let finishi := (iInterInclusion Ksub i).toVertex finish
  let startj := (iInterInclusion Ksub j).toVertex start
  let finishj := (iInterInclusion Ksub j).toVertex finish
  have hpathi :
      Nonempty (ZigzagPath starti finishi) := by
    exact hlabel.connected i _ _
  rcases hpathi with ⟨pathi⟩
  have hfactori :
      endpointDisplacement label start.1 finish.1 ∈
        (CoprodI.of : A i →* CoprodI A).range := by
    simpa [starti, finishi] using hlabel.endpointDisplacement_mem_factor i starti finishi
  have hfactorj :
      endpointDisplacement label start.1 finish.1 ∈
        (CoprodI.of : A j →* CoprodI A).range := by
    simpa [startj, finishj] using hlabel.endpointDisplacement_mem_factor j startj finishj
  have himage :
      endpointDisplacement label start.1 finish.1 = 1 :=
    coprodI_eq_one_of_mem_two_factors hij hfactori hfactorj
  refine ⟨
    { index := i
      start := start
      finish := finish
      separated := hseparated
      path := pathi
      displacement_eq_one := himage },
    rfl⟩

end Subcomplex

end OneComplex
