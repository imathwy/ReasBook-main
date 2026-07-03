import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_4_1 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: simple boundary cycles for regions in simply connected planar small-cancellation
maps.

Layer triage:
- `source-facing`: Lemma `5-4-1`, which asserts that every region of a simply connected `(q, p)`
  map satisfying the stated region-degree hypothesis has simple boundary.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for the planar map,
  `TwoComplex.IsSimplyConnected` is the owner for simply connectedness,
  `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner for the `(q, p)` condition,
  and `TwoComplex.HasSimpleBoundary` is the owner predicate expressing that a face boundary is a
  simple closed path.
- `bridge/view`: the source condition that `∂D` contains no edge of `∂M` is the inclusion
  `C.boundaryGeometricEdges D ⊆ {e | embedding.IsInteriorEdge e}` built from
  `TwoComplex.boundaryGeometricEdges D` and `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` from Definition `5-3-1` is the chapter owner
   for the source `(q, p)` hypothesis.
2. `TwoComplex.boundaryGeometricEdges` from Definition `5-1-1` is the owner API for the
   geometric edges occurring in a region boundary.
3. `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` from Definition `5-2-7` is the owner
   predicate for the ambient-map interior edges used in the source hypothesis that a region
   boundary contains no boundary edge of the ambient map.
4. `TwoComplex.HasSimpleBoundary` from Definition `3-2-4` is the owner predicate matching the
   conclusion that a region boundary is a simple closed path.

Primitive vs. derived:
- primitive public data: the planar embedding `embedding`, the simply connectedness hypothesis,
  the `(q, p)` hypothesis, the explicit classification of `(q, p)`, and the extra degree bound on
  regions whose boundaries contain no boundary edge of `M`;
- derived API: the conclusion that every oriented face, hence every region, has simple boundary.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

-- Proof sketch: argue by contradiction using a minimal submap cut off by a non-simple boundary
-- loop in the boundary of `D`. That submap inherits simple connectedness, all of its vertices
-- except possibly one boundary vertex have degree at least `q`, and every region in it has degree
-- at least `p` by the no-boundary-edge hypothesis. Corollary `3.3` then gives a curvature
-- inequality contradicting `(q, p) ∈ {(3, 6), (4, 4), (6, 3)}`.
/-- Lemma 5-4-1: in a simply connected `(q, p)` map with `(q, p)` equal to `(3, 6)`, `(4, 4)`,
or `(6, 3)`, if every region whose boundary contains no boundary edge of the ambient map has
degree at least `p`, then every oriented face, equivalently every region, has simple boundary. -/
theorem face_hasSimpleBoundary_of_simplyConnected_roundBracketQPMap
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] [TwoComplex.IsSimplyConnected C]
    (q p : ℕ) (hQP : embedding Is(q, p))
    (hPair : (q, p) = (3, 6) ∨ (q, p) = (4, 4) ∨ (q, p) = (6, 3))
    (hRegionDegree :
      ∀ D : GeometricFace C,
        C.boundaryGeometricEdges D ⊆ {e | embedding.IsInteriorEdge e} →
          p ≤ C.regionDegree D)
    (D : C.Face) :
    C.HasSimpleBoundary D := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Definition_5_4_2 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: extremal disc submaps in planar map theory.

Layer triage:
- `source-facing`: a submap `K` of a map `M` that is topologically a disk and whose boundary
  edges occur in order along some boundary cycle of `M`.
- `core/canonical`: `TwoComplex.Subcomplex` is the project owner for submaps,
  `TwoComplex.Subcomplex.IsSingularDisc` is the existing owner predicate for disc-like submaps
  together with a chosen boundary cycle, and `TwoComplex.TwoManifoldEmbedding.IsBoundaryEdge` is the
  owner predicate for ambient boundary edges of a planar map.
- `bridge/view`: `Loop`, `cyclicPath`, `edgeList`, and `OneComplex.Hom.mapLoop` applied to the
  inclusion `K.skeleton.inclusion` compare a boundary cycle in the submap with a boundary cycle
  in the ambient map through ordered total-edge lists.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the chapter owner for submaps.
2. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the owner predicate for a
   submap that is topologically a disk together with an explicit boundary cycle.
3. `TwoComplex.TwoManifoldEmbedding.IsBoundaryEdge` from Definition `5-2-7` is the owner predicate
   for edges lying on the boundary of the ambient planar map.
4. `Loop`, `cyclicPath`, and `edgeList` from Definition `3-2-3` are the canonical ordered
   boundary-cycle API, and `OneComplex.Hom.mapLoop` applied to `K.skeleton.inclusion` is the
   bridge from a submap boundary loop to the corresponding ambient boundary loop.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

variable {C : TwoComplex}

/-- The edges of a chosen submap boundary cycle occur in order in a chosen ambient boundary cycle
when some representatives of those cyclic paths give a sublist relation after mapping the submap
edges into the ambient map. This is a file-local bridge used only to state `IsExtremalDisk`. -/
private def boundaryCycleOccursInOrder (K : Subcomplex C)
    (boundaryK : CyclicPath K.skeleton.toOneComplex) (boundaryM : CyclicPath C.skeleton) : Prop :=
  let inclusion := K.skeleton.inclusion
  ∃ pK : Loop K.skeleton.toOneComplex, cyclicPath pK = boundaryK ∧
    ∃ pM : Loop C.skeleton, cyclicPath pM = boundaryM ∧
      List.Sublist (inclusion.mapLoop pK).2.edgeList pM.2.edgeList

/-- A boundary cycle of a surface embedding is a simple cycle all of whose geometric edges lie on
the boundary of the ambient map. -/
def IsBoundaryCycle (embedding : TwoManifoldEmbedding C 𝔼²)
    (c : CyclicPath C.skeleton) : Prop :=
  IsSimpleCycle c ∧
    ∀ ⦃e : OneComplex.GeometricEdge C.skeleton⦄,
      c.SupportsGeometricEdge e → embedding.IsBoundaryEdge e

/-- A planar map has simple boundary when one simple ambient boundary cycle carries exactly the
boundary edges of the whole map. -/
def HasSimpleBoundary (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  ∃ c : CyclicPath C.skeleton,
    embedding.IsBoundaryCycle c ∧
      ∀ e : OneComplex.GeometricEdge C.skeleton,
        embedding.IsBoundaryEdge e ↔ c.SupportsGeometricEdge e

/-- Definition 5-4-2: an extremal disk of a planar map `embedding` is a submap `K` that is a
topological disk and has a boundary cycle whose edges occur in order in some boundary cycle of the
whole map. -/
def IsExtremalDisk (embedding : TwoManifoldEmbedding C 𝔼²)
    (K : Subcomplex C) : Prop :=
  ∃ boundaryK : CyclicPath K.skeleton.toOneComplex, ∃ boundaryM : CyclicPath C.skeleton,
    K.IsSingularDisc boundaryK ∧
      embedding.IsBoundaryCycle boundaryM ∧
        boundaryCycleOccursInOrder K boundaryK boundaryM

end TwoManifoldEmbedding
end TwoComplex

/-! ### Lemma_5_4_3 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: simple closed boundaries and extremal discs of planar maps.

Layer triage:
- `source-facing`: Lemma `5-4-3`, which concludes the existence of two extremal discs from the
  failure of the whole-boundary simple-cycle condition on the whole map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.HasSimpleBoundary` from Definition `5-4-2`
  is the chapter owner for the actual boundary of a planar map being carried by one simple ambient
  boundary cycle.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` remains the chosen-cycle API
  used to witness map-level simple boundary and to state extremality of subdiscs.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the owner
   predicate for an individual simple ambient boundary cycle.
2. `TwoComplex.TwoManifoldEmbedding.HasSimpleBoundary` from Definition `5-4-2` is the owner
   predicate for the whole boundary of the map being one simple closed path.
3. `TwoComplex.TwoManifoldEmbedding.IsExtremalDisk` from Definition `5-4-2` is the owner
   predicate in the conclusion.
4. `TwoComplex.TwoManifoldEmbedding.IsBoundaryEdge` from Definition `5-2-7` is the canonical
   boundary-edge API used to tie a chosen boundary cycle to the actual ambient boundary.

Primitive vs. derived:
- primitive public data: the planar embedding, connectedness and simple-connectedness
  hypotheses, the no-degree-one assumption, and the canonical whole-boundary hypothesis
  `TwoManifoldEmbedding.HasSimpleBoundary embedding`;
- derived API: particular ambient boundary cycles witnessing `embedding.IsBoundaryCycle c` inside
  the owner `TwoManifoldEmbedding.HasSimpleBoundary embedding` and inside
  `embedding.IsExtremalDisk`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

-- Proof sketch: induct on the number of regions. Choose a shortest closed subpath of a boundary
-- cycle of `M`; the degree-one hypothesis makes this subpath simple, so it bounds an extremal
-- singular-disc submap. Delete the vertices of degree one from the complementary submap and
-- apply the induction hypothesis there; either the complement is itself extremal or it contains
-- another extremal disk that remains extremal in the ambient map, yielding an injective
-- `Fin 2`-indexed family of extremal disks.
/-- Lemma 5-4-3: if a connected simply connected planar map has no vertices of degree `1` and its
boundary is not a simple closed path, then the map
contains at least two distinct extremal disks. -/
theorem exists_two_extremalDisks_of_not_boundary_simpleClosedPath
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [TwoComplex.IsSimplyConnected C]
    (hnoDegreeOne :
      let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
      ∀ v : C.skeleton, C.skeleton.vertexDegree v ≠ 1)
    (hboundary : ¬ TwoManifoldEmbedding.HasSimpleBoundary embedding) :
    ∃ disks : Fin 2 → Subcomplex C,
      Function.Injective disks ∧ ∀ i : Fin 2, embedding.IsExtremalDisk (disks i) := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Definition_5_4_4 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

open Set Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: boundary regions in planar map theory.

Layer triage:
- `source-facing`: for a chosen region `D` of a planar map `M`, the intersection `∂D ∩ ∂M`
  should be realized by a consecutive string of closed edges that appears along both the boundary
  of `D` and some boundary cycle of `M`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` is the owner of the planar map,
  `TwoComplex.GeometricFace` is the owner of an unoriented region, `boundary`, `region`, and
  `geometricEdgeSet` are the source-facing planar subsets, and `IsBoundaryCycle` from
  Definition `5-4-2` is the existing owner predicate for boundary cycles of the whole map.
- `bridge/view`: `Quiver.Path.CyclicPath.HasPart` is the owner predicate for a consecutive segment
  of a cyclic boundary path, and `TwoComplex.boundaryArrowGeometricEdge` maps that total-arrow
  segment to the corresponding geometric-edge string used in the source statement.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the existing owner
   for ambient boundary cycles of a surface embedding.
2. `TwoComplex.boundaryArrowGeometricEdge` from Definition `5-1-1` is the canonical bridge from
   an oriented boundary arrow to the underlying closed geometric edge.
3. `Quiver.Path.CyclicPath.HasPart` is the owner-side consecutive-segment predicate on cyclic
   boundary data; it packages the representative-loop plus `List.IsInfix` formulation once.
4. `frontier (embedding.region D)` and `embedding.boundary` are the source-facing subsets for
   `∂D` and `∂M`, while `embedding.geometricEdgeSet e` is the closed edge corresponding to `e`.
-/

namespace Quiver.Path

/-- A cyclic path contains the consecutive part `part` when some representative loop has `part`
as a contiguous block in its total-edge list. -/
def CyclicPath.HasPart {V : Type*} [Quiver V] (c : CyclicPath V) (part : List (Quiver.Total V)) :
    Prop :=
  ∃ p : Loop V, cyclicPath p = c ∧ List.IsInfix part p.2.edgeList

end Quiver.Path

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- The planar support obtained by taking the union of the closed edges listed in `edges`. -/
private def edgeSequenceSupport (embedding : TwoManifoldEmbedding C 𝔼²)
    (edges : List (OneComplex.GeometricEdge C.skeleton)) : Set 𝔼² :=
  sUnion (embedding.geometricEdgeSet '' { e | e ∈ edges })

/-- A list of geometric edges occurs consecutively in the boundary of a geometric face when some
oriented representative of that face has a boundary cycle containing the list as a contiguous
block. -/
private def GeometricFaceHasConsecutiveEdgeSequence (C : TwoComplex) (D : GeometricFace C)
    (edges : List (OneComplex.GeometricEdge C.skeleton)) : Prop :=
  ∃ F : C.Face,
    (⟦F⟧ : GeometricFace C) = D ∧
      ∃ part : List (Quiver.Total C.skeleton),
        (C.boundary F).HasPart part ∧ part.map C.boundaryArrowGeometricEdge = edges

/-- A list of geometric edges occurs consecutively in the boundary of the planar map when some
boundary cycle of the map contains that list as a contiguous block. -/
private def BoundaryCycleHasConsecutiveEdgeSequence (embedding : TwoManifoldEmbedding C 𝔼²)
    (edges : List (OneComplex.GeometricEdge C.skeleton)) : Prop :=
  ∃ c : CyclicPath C.skeleton,
    IsBoundaryCycle embedding c ∧
      ∃ part : List (Quiver.Total C.skeleton),
        c.HasPart part ∧ part.map C.boundaryArrowGeometricEdge = edges

/-- Definition 5-4-4: the intersection `∂D ∩ ∂M` is a consecutive part of the planar map when it
is the union of a nonempty consecutive sequence of closed edges that occurs along a boundary cycle
of the region `D` and along some boundary cycle of the whole map. -/
def BoundaryIntersectionIsConsecutivePart (embedding : TwoManifoldEmbedding C 𝔼²)
    (D : GeometricFace C) : Prop :=
  ∃ edges : List (OneComplex.GeometricEdge C.skeleton),
    edges ≠ [] ∧
      frontier (embedding.region D) ∩ embedding.boundary = edgeSequenceSupport embedding edges ∧
      GeometricFaceHasConsecutiveEdgeSequence C D edges ∧
        BoundaryCycleHasConsecutiveEdgeSequence embedding edges

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Theorem_5_4_5 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for simply connected planar `(q, p)` maps with the
source-facing starred sum over boundary regions whose boundary intersection with the whole map is a
consecutive part of the ambient boundary.

Layer triage:
- `source-facing`: the starred curvature sum of Theorem `5-4-5`, indexed by those regions `D`
  for which `∂D ∩ ∂M` is a consecutive part of `∂M`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner of the planar map,
  `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner of the `(q, p)` condition,
  `TwoComplex.TwoManifoldEmbedding.adjustedInteriorEdgeDefectSum` is the owner construction for the
  curvature sum attached to a selected family of regions,
  `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` is the owner of the source quantity
  `i(D)`, and `TwoComplex.TwoManifoldEmbedding.BoundaryIntersectionIsConsecutivePart` from Definition
  `5-4-4` is the owner predicate selecting the starred summation domain.
- `bridge/view`: the textbook starred sum is the specialization of
  `adjustedInteriorEdgeDefectSum` to the consecutive-boundary-intersection predicate, while
  the source hypothesis that a region boundary contains no boundary edge of the ambient map is the
  inclusion `C.boundaryGeometricEdges D ⊆ {e | embedding.IsInteriorEdge e}`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum` from
   `Corollary_5_3_5.lean` is the existing owner for the bullet-sum version over all boundary
   regions.
2. `TwoComplex.TwoManifoldEmbedding.BoundaryIntersectionIsConsecutivePart` from
   `Definition_5_4_4.lean` is the source-facing owner for the extra starred-sum restriction.
3. `OneComplex.vertexDegree` and `TwoComplex.regionCount` are the chapter owners
   for the no-degree-one and more-than-one-region hypotheses.
4. `TwoComplex.boundaryGeometricEdges` and
   `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` are the owner APIs for the source condition
   that a region boundary contains no boundary edge of the ambient map.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: first handle the case where the map boundary is a simple closed path by
-- induction on the number of regions. If every boundary region has consecutive boundary
-- intersection, apply Corollary `5-3-5`; otherwise choose a region whose boundary intersection is
-- not consecutive, split the map along that region into two smaller maps, apply the induction
-- hypothesis to both pieces, and combine the resulting starred sums. When the boundary is not a
-- simple closed path, use Lemma `5-4-3` to obtain two extremal disks and add their contributions
-- to recover the same lower bound for the ambient starred sum.
/-- Theorem 5-4-5: in a connected simply connected `(q, p)` map with no vertices of degree `1`
and more than one region, if every region whose boundary contains no boundary edge of the ambient
map has degree at least `p`, then the starred curvature sum
`∑_M^* [p / q + 2 - i(D)]` is at least `p`. -/
theorem consecutiveBoundaryRegion_curvature_formula_lower_bound_of_simplyConnected_roundBracketQPMap
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [TwoComplex.IsSimplyConnected C]
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hQP : embedding Is(q, p))
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hnoDegreeOne :
      let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
      ∀ v : C.skeleton, C.skeleton.vertexDegree v ≠ 1)
    (hmoreThanOneRegion : (1 : ℚ) < embedding.regionCount)
    (hRegionDegree :
      ∀ D : GeometricFace C,
        C.boundaryGeometricEdges D ⊆
          { e : OneComplex.GeometricEdge C.skeleton | embedding.IsInteriorEdge e } →
          p ≤ C.regionDegree D) :
    (p : ℚ) ≤
      embedding.adjustedInteriorEdgeDefectSum embedding.BoundaryIntersectionIsConsecutivePart p q :=
  sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Definition_5_4_6 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance : DecidableEq X := Classical.decEq X

/-!
Primary domain: small-cancellation theory for relator sets in a free group with a chosen basis.

Layer triage:
- `source-facing`: a basis `basis : FreeGroupBasis X F`, a relator set `R : Set F`, a word
  `s : List (X × Bool)`, and a relator `r ∈ R` represented by `s` followed by exactly `j`
  ordered piece-words.
- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
  basis, `basis.is_piece R` from Definition `5-2-1` is the chapter owner predicate for piece
  words, and `FreeGroup.toWord` is the canonical reduced-word owner for relators transported by
  `basis.repr`, while `Vector` is the canonical owner for an ordered family of exactly `j`
  pieces.
- `bridge/view`: `(basis.repr r).toWord` and `pieces.toList.flatten` express the textbook word
  decomposition by a literal reduced-word equality saying that the reduced word of `r` is the
  concatenation of the initial segment `s` with exactly `j` ordered piece-words.

Domain sampling:
1. `FreeGroupBasis X F` is the established Chapter `5` owner for relator data with a chosen basis.
2. `FreeGroupBasis.is_piece` from Definition `5-2-1` is the existing owner predicate for the
   piece-words `b₁, ..., bⱼ`.
3. `(basis.repr r).toWord` is the chapter's canonical reduced-word model of a relator `r`.
4. `Vector (List (X × Bool)) j` is the canonical owner for a finite ordered family of exactly
   `j` piece-words, avoiding a separate length-equality witness.
5. `List.flatten` on `pieces.toList` is the natural owner for concatenating those piece-words.

Primitive vs. derived:
- primitive source data: `basis`, `R`, `j`, the word `s`, a relator `r ∈ R`, and an ordered
  family of exactly `j` piece-words whose concatenation follows `s`;
- derived API: the specification theorem unpacking the existential data of a `j`-remnant.
-/

namespace FreeGroupBasis

/-- Definition 5-4-6: a word `s` is a `j`-remnant with respect to `R` and `basis` if some relator
`r ∈ R` is represented by the concatenated word `s b₁ ⋯ bⱼ`, where `b₁, ..., bⱼ` are pieces with
respect to `R`. -/
def is_j_remnant (basis : FreeGroupBasis X F) (R : Set F) (j : ℕ) (s : List (X × Bool)) : Prop :=
  ∃ r ∈ R, ∃ pieces : Vector (List (X × Bool)) j,
    (∀ piece ∈ pieces.toList, basis.is_piece R piece) ∧
      (basis.repr r).toWord = s ++ pieces.toList.flatten

-- Proof sketch: unfold `is_j_remnant`; the theorem is exactly the existential witness data in the
-- definition.
/-- A `j`-remnant is exactly a word that occurs as an initial segment of some relator from `R`,
with the remaining suffix decomposed into exactly `j` pieces. -/
theorem is_j_remnant_iff
    (basis : FreeGroupBasis X F) {R : Set F} {j : ℕ} {s : List (X × Bool)} :
    basis.is_j_remnant R j s ↔
      ∃ r ∈ R, ∃ pieces : Vector (List (X × Bool)) j,
        (∀ piece ∈ pieces.toList, basis.is_piece R piece) ∧
          (basis.repr r).toWord = s ++ pieces.toList.flatten := Iff.rfl

end FreeGroupBasis

end

/-! ### Theorem_5_4_7 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

section

variable {X : Type u}

open FreeGroupBasis GroupPresentation

local instance : DecidableEq X := Classical.decEq X

private abbrev basis : FreeGroupBasis X (FreeGroup X) := FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: word-level Greendlinger alternatives for classical small-cancellation pairs.

Layer triage:
- `source-facing`: a relator set `R`, its normal closure `N`, a nontrivial element `w ∈ N`, and a
  cyclically reduced conjugate `w*` whose cyclic word either lies in the symmetrized relator
  family `R*` or has a decomposition `u₁ s₁ ⋯ uₙ sₙ` with each `sₖ` an `i(sₖ)`-remnant
  satisfying the displayed curvature inequality.
- `core/canonical`: `FreeGroup X` is the owner for reduced words, `Subgroup.normalClosure R` is
  the owner for `N`, `IsConj` is the owner relation for conjugacy,
  `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclic reduction,
  `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family,
  and `List.IsSuffix` / `List.IsInfix` are the canonical list owners for contiguous word
  occurrence and the remaining suffix after such an occurrence,
  and
  `FreeGroupBasis.is_j_remnant` is the chapter owner for the remnant condition attached to each
  segment.
- `bridge/view`: the reusable predicate
  `List.HasOrderedDisjointSublists` packages the repeated source pattern of successive disjoint
  ordered subword occurrences by recursively choosing the suffix left after each segment, and
  the reusable predicate
  `FreeGroup.HasGreendlingerRemnantConfiguration R p q` packages the source-facing decomposition
  as a single `Prop`, using only the direct witness data `(uₖ, sₖ, i(sₖ))` for each segment and
  the rational `List.sum` of the corresponding curvature terms.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the normal closure `N`.
2. `FreeGroup.IsCyclicallyReduced` and `IsConj` are the owner predicates for the cyclically
   reduced conjugate `w*`.
3. `GroupPresentation.symmetrizedRelatorFamily` from Proposition `3-11-2` is the owner for the
   cyclic-word relator family `R*`.
4. `FreeGroupBasis.is_j_remnant` from Definition `5-4-6` is the chapter owner for the statement
   that a word is an `i(sₖ)`-remnant.
5. `C(p)[basis, R]` and `T(q)[basis, R]` from Definitions `5-2-2` and `5-2-3` are the owner
   hypotheses for the small-cancellation assumptions in the theorem.
6. `List.IsSuffix` and `List.IsInfix` are the canonical list owners for contiguous occurrence,
   and `List.HasOrderedDisjointSublists` is the thin recursive bridge used by the sixth- and
   quarter-group source refinements.
-/

namespace List

/-- An ordered family of sublists occurs disjointly in `word` when one can successively split off
the listed parts from left to right, always continuing inside the suffix that remains. -/
def HasOrderedDisjointSublists {α : Type u} (word : List α) : List (List α) → Prop
  | [] => True
  | part :: parts =>
      ∃ right : List α, part ++ right <:+ word ∧ HasOrderedDisjointSublists right parts

end List

namespace FreeGroup

/-- A word `w` has a Greendlinger remnant configuration for the pair `(q, p)` when its reduced
word is an alternating product `u₁ s₁ ⋯ uₙ sₙ`, each `sₖ` is an `i(sₖ)`-remnant with respect to
`R`, and the indices satisfy the displayed curvature inequality
`∑ [p / q + 2 - i(sₖ)] ≥ p`. This is a thin bridge predicate around the direct source witnesses,
not a separate owner structure. -/
def HasGreendlingerRemnantConfiguration (w : FreeGroup X) (R : Set (FreeGroup X)) (p q : ℕ) :
    Prop :=
  ∃ segments : List (List (X × Bool) × List (X × Bool) × ℕ),
    w.toWord = segments.flatMap (fun seg ↦ match seg with | (u, s, _) => u ++ s) ∧
      (∀ seg ∈ segments, match seg with | (_, s, i) => basis.is_j_remnant R i s) ∧
        (p : ℚ) ≤
          (segments.map fun seg ↦ match seg with | (_, _, i) => (p : ℚ) / q + 2 - i).sum

-- Proof sketch: unfold `HasGreendlingerRemnantConfiguration`; the statement is exactly the
-- existential decomposition, remnant conditions, and curvature inequality appearing in the
-- definition.
/-- Unfolding a Greendlinger remnant configuration gives the alternating decomposition of `w`,
the remnant condition on each `sₖ`, and the displayed lower bound on
`∑ [p / q + 2 - i(sₖ)]`. -/
theorem hasGreendlingerRemnantConfiguration_iff (w : FreeGroup X) (R : Set (FreeGroup X))
    (p q : ℕ) :
    w.HasGreendlingerRemnantConfiguration R p q ↔
      ∃ segments : List (List (X × Bool) × List (X × Bool) × ℕ),
        w.toWord = segments.flatMap (fun seg ↦ match seg with | (u, s, _) => u ++ s) ∧
          (∀ seg ∈ segments, match seg with | (_, s, i) => basis.is_j_remnant R i s) ∧
            (p : ℚ) ≤
              (segments.map fun seg ↦ match seg with | (_, _, i) => (p : ℚ) / q + 2 - i).sum :=
  Iff.rfl

end FreeGroup

-- Proof sketch: choose a cyclically reduced conjugate `w*` of `w` with a minimal
-- relator-conjugate diagram. The hypotheses `C(p)` and `T(q)` together with the allowed pairs
-- `(6, 3)`, `(4, 4)`, and `(3, 6)` convert the boundary-region estimate of Theorem `5-4-5` into
-- the displayed inequality for the boundary remnants of that diagram. Reading the corresponding
-- consecutive boundary segments on the boundary cycle of the diagram gives the owner predicate
-- `w*.HasGreendlingerRemnantConfiguration R p q`. If the diagram has a single region, its
-- cyclically reduced boundary word represents an element of the symmetrized relator family `R*`,
-- so the first alternative should be stated through that cyclic-word owner rather than by the
-- raw membership predicate `w* ∈ R`.
/-- Theorem 5-4-7: if `R` satisfies `C(p)` and `T(q)` for one of the pairs `(q, p) = (6, 3)`,
`(4, 4)`, or `(3, 6)`, then every nontrivial element of the normal closure of `R` has a
cyclically reduced conjugate `w*` whose cyclic word either lies in the symmetrized relator
family `R*` or admits a decomposition `u₁ s₁ ⋯ uₙ sₙ` with each `sₖ` an `i(sₖ)`-remnant and
`∑ [p / q + 2 - i(sₖ)] ≥ p`; this second alternative is recorded through the canonical bridge
predicate `w*.HasGreendlingerRemnantConfiguration R p q` rather than by repeating its witness
data inline. -/
theorem greendlinger_remnant_alternative_for_small_cancellation_pairs
    (R : Set (FreeGroup X)) {p q : ℕ}
    (hpair : (q, p) = (6, 3) ∨ (q, p) = (4, 4) ∨ (q, p) = (3, 6))
    (hC : C(p)[basis, R]) (hT : T(q)[basis, R]) {w : FreeGroup X}
    (hw_ne : w ≠ 1) (hw_mem : w ∈ Subgroup.normalClosure R) :
    ∃ wStar : FreeGroup X,
      IsConj wStar w ∧
        ∃ hwStar_cyclic : FreeGroup.IsCyclicallyReduced wStar.toWord,
          ((⟨wStar.toWord, hwStar_cyclic⟩ : CyclicWord X) ∈ symmetrizedRelatorFamily R ∨
            wStar.HasGreendlingerRemnantConfiguration R p q) :=
  sorry

end

/-! ### Theorem_5_4_8 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open GroupPresentation

section

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: small-cancellation theory in free groups at the word level.

Layer triage:
- `source-facing`: a relator set `R`, its normal closure `N`, a nontrivial cyclically reduced word
  `w ∈ N`, together with the alternative that the cyclic word of `w` lies in the symmetrized
  relator family `R*`, and Greendlinger's five sixth-group long-subword alternatives.
- `core/canonical`: `FreeGroup X` is the owner for reduced words, `Subgroup.normalClosure R` is
  the owner for `N`, `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclic reduction,
  `IsConj` is the owner relation for conjugacy,
  `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family
  `R*`, `CyclicWord.HasPart` is the owner predicate for a cyclic segment of a symmetrized relator,
  `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` from Proposition `3-11-2` is the
  owner for the recurring fraction-length comparisons against `R*`,
  `basis.is_j_remnant` from Definition `5-4-6` is the chapter owner for remnant pieces, and
  `FreeGroup.HasGreendlingerRemnantConfiguration` from Theorem `5-4-7` is the generic Greendlinger
  owner abstraction for small-cancellation pairs, while `C'((1 / 6 : ℝ))[basis, R]` is the
  existing Chapter `5` owner for the small-cancellation
  hypothesis.
- `bridge/view`: the generic `(q, p) = (6, 3)` remnant configuration from Theorem `5-4-7` is
  translated to the source sixth-group alternatives by turning a `j`-remnant under `C'(1 / 6)`
  into a subword longer than `(6 - j) / 6` of a symmetrized relator.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the relator subgroup `N`.
2. `FreeGroup.IsCyclicallyReduced` is the owner predicate for the hypothesis that `w` is
   cyclically reduced and for the cyclically reduced conjugate `w*`.
3. `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family
   used in the source `>(5 / 6)`, `>(4 / 6)`, and `>(3 / 6)` comparisons.
4. `List.HasOrderedDisjointSublists` from Theorem `5-4-7` is the shared list-level owner for the
   ordered disjoint occurrence of the long subwords in the source alternatives.
5. `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` from Proposition `3-11-2` is the
   owner for the recurring “longer than `numerator / denominator` of a symmetrized relator”
   comparison.
6. `FreeGroup.HasGreendlingerRemnantConfiguration` from Theorem `5-4-7` is the established
   generic owner abstraction whose `(3, 6)` specialization should be kept only as a bridge here.

Primitive vs. derived:
- primitive public data: the relator set `R`, the word `w`, the normal-closure membership
  hypothesis, the cyclic reduction hypothesis, and the `C'(1 / 6)` assumption;
- derived API: the owner-level first alternative
  `⟨w.toWord, hw_cyclic⟩ ∈ symmetrizedRelatorFamily R`, the sixth-group long-subword
  configuration, the direct existential conclusion for a cyclically reduced conjugate, and the
  bridge from the generic `(3, 6)` remnant owner to that source-facing configuration.
-/

namespace FreeGroup

/-- A Greendlinger configuration for a sixth-group is one of Greendlinger's five explicit
long-subword alternatives: two disjoint `>(5 / 6) R` subwords, three disjoint `>(4 / 6) R`
subwords, two disjoint `>(4 / 6) R` subwords together with two disjoint `>(3 / 6) R` subwords,
one disjoint `>(4 / 6) R` subword together with four disjoint `>(3 / 6) R` subwords, or six
disjoint `>(3 / 6) R` subwords. -/
def HasGreendlingerSixthConfiguration (w : FreeGroup X) (R : Set (FreeGroup X)) : Prop :=
  (∃ part₁ part₂ : List (X × Bool),
      List.HasOrderedDisjointSublists w.toWord [part₁, part₂] ∧
        HasLongSymmetrizedRelatorFractionPart R 5 6 part₁ ∧
          HasLongSymmetrizedRelatorFractionPart R 5 6 part₂) ∨
    (∃ part₁ part₂ part₃ : List (X × Bool),
        List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃] ∧
          HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
            HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₃) ∨
      (∃ part₁ part₂ part₃ part₄ : List (X × Bool),
          List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄] ∧
            HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
                HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₄) ∨
        (∃ part₁ part₂ part₃ part₄ part₅ : List (X × Bool),
            List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄, part₅] ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₅) ∨
          ∃ part₁ part₂ part₃ part₄ part₅ part₆ : List (X × Bool),
            List.HasOrderedDisjointSublists w.toWord
              [part₁, part₂, part₃, part₄, part₅, part₆] ∧
              HasLongSymmetrizedRelatorFractionPart R 3 6 part₁ ∧
                HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₅ ∧
                        HasLongSymmetrizedRelatorFractionPart R 3 6 part₆

-- Proof sketch: unfold `HasGreendlingerSixthConfiguration`; the five disjuncts are exactly the
-- five source alternatives in the theorem.
/-- A sixth-group Greendlinger configuration is exactly one of Greendlinger's five explicit
long-subword alternatives. -/
theorem hasGreendlingerSixthConfiguration_iff (w : FreeGroup X) (R : Set (FreeGroup X)) :
    w.HasGreendlingerSixthConfiguration R ↔
      (∃ part₁ part₂ : List (X × Bool),
          List.HasOrderedDisjointSublists w.toWord [part₁, part₂] ∧
            HasLongSymmetrizedRelatorFractionPart R 5 6 part₁ ∧
              HasLongSymmetrizedRelatorFractionPart R 5 6 part₂) ∨
        (∃ part₁ part₂ part₃ : List (X × Bool),
            List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃] ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
                  HasLongSymmetrizedRelatorFractionPart R 4 6 part₃) ∨
          (∃ part₁ part₂ part₃ part₄ : List (X × Bool),
              List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄] ∧
                HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                  HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₄) ∨
            (∃ part₁ part₂ part₃ part₄ part₅ : List (X × Bool),
                List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄, part₅] ∧
                  HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                        HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                          HasLongSymmetrizedRelatorFractionPart R 3 6 part₅) ∨
              ∃ part₁ part₂ part₃ part₄ part₅ part₆ : List (X × Bool),
                List.HasOrderedDisjointSublists w.toWord
                  [part₁, part₂, part₃, part₄, part₅, part₆] ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₁ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                        HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                          HasLongSymmetrizedRelatorFractionPart R 3 6 part₅ ∧
                            HasLongSymmetrizedRelatorFractionPart R 3 6 part₆ :=
  Iff.rfl

-- Proof sketch: under `C'(1 / 6)`, every `j`-remnant from Definition `5-4-6` is longer than
-- `(6 - j) / 6` of the corresponding symmetrized relator from `R*`. Rewriting the `(3, 6)`
-- remnant data from Theorem `5-4-7` with these long-subword bounds converts the remnant-index
-- multisets `[1, 1]`, `[2, 2, 2]`, `[2, 2, 3, 3]`, `[2, 3, 3, 3, 3]`, and `[3, 3, 3, 3, 3, 3]`
-- into the source numerator multisets `[5, 5]`, `[4, 4, 4]`, `[4, 4, 3, 3]`, `[4, 3, 3, 3, 3]`,
-- and `[3, 3, 3, 3, 3, 3]`.
/-- Under `C'(1 / 6)`, the generic `(3, 6)` remnant configuration from Theorem `5-4-7` is
equivalent to Greendlinger's five sixth-group long-subword alternatives. -/
theorem hasGreendlingerRemnantConfiguration_sixth_iff
    (R : Set (FreeGroup X)) (hR : C'((1 / 6 : ℝ))[basis, R]) (w : FreeGroup X) :
    w.HasGreendlingerRemnantConfiguration R 3 6 ↔
      w.HasGreendlingerSixthConfiguration R :=
  sorry

end FreeGroup

-- Proof sketch: choose a cyclically reduced conjugate of `w` with a minimal van Kampen diagram
-- over `R`. Under `C'(1 / 6)`, translate boundary pieces into the degree bounds of the chapter's
-- planar small-cancellation lemmas and apply the curvature-counting alternative for `(q, p) =
-- (6, 3)` from Theorem `5-4-7`. If the resulting conjugate `wStar` lies in `R`, then the
-- cyclically reduced cyclic word `⟨w.toWord, hw_cyclic⟩` represents the same conjugacy class as
-- `wStar`, so it lies in `symmetrizedRelatorFamily R`. Otherwise the owner configuration
-- `HasGreendlingerRemnantConfiguration R 3 6` converts via the preceding bridge to one of the
-- five source sixth-group long-subword patterns.
/-- Theorem 5-4-8: if `R` satisfies `C'(1 / 6)` and `w` is a nontrivial cyclically reduced word in
the normal closure of `R`, then either the cyclic word of `w` lies in the symmetrized relator
family `R*`, or some cyclically reduced conjugate of `w` satisfies one of Greendlinger's five
sixth-group long-subword configurations. The existential conclusion is stated directly in terms of
the canonical owners `IsConj` and `IsCyclicallyReduced`, rather than through an extra witness
wrapper. -/
theorem greendlinger_alternatives_for_sixth_groups
    (R : Set (FreeGroup X)) {w : FreeGroup X} (hR : C'((1 / 6 : ℝ))[basis, R])
    (hw_ne : w ≠ 1) (hw_cyclic : FreeGroup.IsCyclicallyReduced w.toWord)
    (hw_mem : w ∈ Subgroup.normalClosure R) :
    (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) ∈ symmetrizedRelatorFamily R ∨
      ∃ wStar : FreeGroup X,
        IsConj wStar w ∧
          FreeGroup.IsCyclicallyReduced wStar.toWord ∧
            wStar.HasGreendlingerSixthConfiguration R := sorry

end

/-! ### Theorem_5_4_9 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open GroupPresentation

section

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: cyclic-word Greendlinger alternatives for quarter-groups.

Layer triage:
- `source-facing`: a relator set `R`, its normal closure `N`, a nontrivial cyclically reduced word
  `w ∈ N`, the alternative that the cyclic word of `w` lies in the symmetrized relator family
  `R*`, and the two Greendlinger quarter-group long-subword alternatives forced by `C'(1 / 4)`
  together with `T(4)`.
- `core/canonical`: `CyclicWord X` is the owner for cyclically reduced words modulo cyclic
  permutation, `Subgroup.normalClosure R` is the owner for `N`,
  `GroupPresentation.symmetrizedRelatorFamily` is the owner for the first source alternative,
  `CyclicWord.HasPart` is the Chapter `1` owner for cyclic segments, and
  `GroupPresentation.HasLongSymmetrizedRelatorPart` is the Chapter `3` owner for the canonical
  half-relator comparison, `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` is the owner
  for the remaining non-half fraction comparisons against `R*`, and the Chapter `5` owners
  `C'((1 / 4 : ℝ))[basis, R]` and `T(4)[basis, R]` express the small-cancellation hypotheses.
- `bridge/view`: `List.HasOrderedDisjointSublists` from Theorem `5-4-7` remains the list-level
  ordered-disjoint occurrence predicate, but here it is used only through a thin cyclic-word
  bridge recording that some representative list of the cyclic word contains the required ordered
  family of disjoint parts. The upstream `(4, 4)` remnant owner from Theorem `5-4-7` is then
  bridged to this cyclic-word owner.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the relator subgroup `N`.
2. `CyclicWord X` from Definition `1-4-17` is the chapter owner abstraction for cyclically
   reduced words modulo cyclic permutation, which is the right owner for Greendlinger's
   quarter-word alternatives.
3. `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family
   `R*` used in the first alternative and the quarter-length comparisons.
4. `CyclicWord.HasPart` from Proposition `1-7-9` is the owner for a cyclic part of a symmetrized
   relator, so the quarter configuration should be phrased using `SignedLetter X` parts on a
   cyclic word rather than on a chosen list representative.
5. `List.HasOrderedDisjointSublists` from Theorem `5-4-7` is the chapter owner for ordered
   disjoint occurrence on one representative list and therefore belongs only to a bridge layer.
6. `GroupPresentation.HasLongSymmetrizedRelatorPart` from Proposition `3-11-2` is the owner for
   the canonical “longer than half a symmetrized relator” condition.
7. `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` from Proposition `3-11-2` is the
   owner for the remaining numerator-over-denominator symmetrized-relator length comparisons.
8. `FreeGroup.HasGreendlingerRemnantConfiguration` from Theorem `5-4-7` is the upstream generic
   owner for `(4, 4)` witness data, but it is weaker than the explicit cyclic-word quarter
   alternative recorded here.
9. `C'((1 / 4 : ℝ))[basis, R]` and `T(4)[basis, R]` from Definitions `5-2-1` and `5-2-3` are the
   existing owner predicates for the quarter-group hypotheses.

Primitive vs. derived:
- primitive public data: the relator set `R`, the word `w`, the small-cancellation hypotheses,
  cyclic reduction, and normal-closure membership;
- derived API: the owner-level cyclic word `⟨w.toWord, hw_cyclic⟩ : CyclicWord X`, its membership
  in `symmetrizedRelatorFamily R`, the quarter-case long-subword configuration on that cyclic
  owner, and the bridge from the generic `(4, 4)` remnant owner to that cyclic-word
  configuration.
-/

namespace CyclicWord

/-- A cyclic word has the ordered disjoint parts `parts` when some representative list of that
cyclic word contains them successively and disjointly from left to right. -/
def HasOrderedDisjointParts (q : CyclicWord X) (parts : List (List (SignedLetter X))) : Prop :=
  ∃ word : List (SignedLetter X), ((word : Cycle (SignedLetter X)) = q.1) ∧
    List.HasOrderedDisjointSublists word parts

/-- A Greendlinger configuration for a quarter-group is either two ordered disjoint parts each
longer than `3 / 4` of a symmetrized relator from `R*`, or four ordered disjoint parts each
longer than `1 / 2` of a symmetrized relator from `R*`. The owner is the cyclic word itself,
not a chosen reduced-word representative. -/
def HasGreendlingerQuarterConfiguration (q : CyclicWord X) (R : Set (FreeGroup X)) : Prop :=
  (∃ part₁ part₂ : List (SignedLetter X),
      q.HasOrderedDisjointParts [part₁, part₂] ∧
        HasLongSymmetrizedRelatorFractionPart R 3 4 part₁ ∧
          HasLongSymmetrizedRelatorFractionPart R 3 4 part₂) ∨
    ∃ part₁ part₂ part₃ part₄ : List (SignedLetter X),
      q.HasOrderedDisjointParts [part₁, part₂, part₃, part₄] ∧
        HasLongSymmetrizedRelatorPart R part₁ ∧
          HasLongSymmetrizedRelatorPart R part₂ ∧
            HasLongSymmetrizedRelatorPart R part₃ ∧
              HasLongSymmetrizedRelatorPart R part₄

-- Proof sketch: unfold `HasGreendlingerQuarterConfiguration`; the two disjuncts are exactly the
-- two source alternatives in the definition.
/-- A quarter-group Greendlinger configuration is exactly one of the two source long-subword
alternatives. -/
theorem hasGreendlingerQuarterConfiguration_iff (q : CyclicWord X) (R : Set (FreeGroup X)) :
    q.HasGreendlingerQuarterConfiguration R ↔
      (∃ part₁ part₂ : List (SignedLetter X),
          q.HasOrderedDisjointParts [part₁, part₂] ∧
            HasLongSymmetrizedRelatorFractionPart R 3 4 part₁ ∧
              HasLongSymmetrizedRelatorFractionPart R 3 4 part₂) ∨
        ∃ part₁ part₂ part₃ part₄ : List (SignedLetter X),
          q.HasOrderedDisjointParts [part₁, part₂, part₃, part₄] ∧
            HasLongSymmetrizedRelatorPart R part₁ ∧
              HasLongSymmetrizedRelatorPart R part₂ ∧
                HasLongSymmetrizedRelatorPart R part₃ ∧
                  HasLongSymmetrizedRelatorPart R part₄ :=
  Iff.rfl

-- Proof sketch: under `C'(1 / 4)`, every `j`-remnant from Definition `5-4-6` is longer than
-- `(4 - j) / 4` of the corresponding symmetrized relator from `R*`. Rewriting the `(4, 4)`
-- remnant data from Theorem `5-4-7` with these long-subword bounds converts the remnant-index
-- multisets `[1, 1]` and `[2, 2, 2, 2]` into the source alternatives of two `>(3 / 4) R`
-- subwords and four subwords longer than half a symmetrized relator, using the existing Chapter
-- `3` half-relator bridge
-- `hasLongSymmetrizedRelatorPart_iff_hasLongSymmetrizedRelatorFractionPart` in the half-relator
-- case.
/-- Under `C'(1 / 4)`, the generic `(4, 4)` remnant configuration from Theorem `5-4-7` is
equivalent to Greendlinger's two quarter-group long-subword alternatives on the induced cyclic
word. -/
theorem hasGreendlingerRemnantConfiguration_quarter_iff
    (R : Set (FreeGroup X)) (hR_cprime : C'((1 / 4 : ℝ))[basis, R]) {w : FreeGroup X}
    (hw_cyclic : FreeGroup.IsCyclicallyReduced w.toWord) :
    w.HasGreendlingerRemnantConfiguration R 4 4 ↔
      CyclicWord.HasGreendlingerQuarterConfiguration
        (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) R := sorry

end CyclicWord

-- Proof sketch: choose a minimal van Kampen diagram over `R` for the cyclically reduced word `w`.
-- The hypotheses `C'(1 / 4)` and `T(4)` convert the boundary analysis of that diagram into the
-- quarter-group curvature bounds. Greendlinger's lemma for `(4, 4)` maps then yields either that
-- the cyclic word of `w` lies in the symmetrized relator family `R*`, or that the same cyclic
-- word has the owner configuration obtained by rewriting the `(4, 4)` remnant alternative through
-- the preceding cyclic-word bridge. The representative/conjugacy bookkeeping is absorbed by the
-- owner `CyclicWord X`.
/-- Theorem 5-4-9: if `R` satisfies `C'(1 / 4)` and `T(4)`, and `w` is a nontrivial cyclically
reduced word in the normal closure of `R`, then either the cyclic word of `w` lies in the
symmetrized relator family `R*`, or that same cyclic word satisfies one of Greendlinger's two
quarter-group configurations. The public conclusion stays on the intrinsic cyclic-word owner
rather than introducing a second representative-level conjugacy witness. -/
theorem greendlinger_alternatives_for_quarter_groups
    (R : Set (FreeGroup X)) {w : FreeGroup X}
    (hR_cprime : C'((1 / 4 : ℝ))[basis, R]) (hR_t : T(4)[basis, R]) (hw_ne : w ≠ 1)
    (hw_cyclic : FreeGroup.IsCyclicallyReduced w.toWord)
    (hw_mem : w ∈ Subgroup.normalClosure R) :
    (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) ∈ symmetrizedRelatorFamily R ∨
      CyclicWord.HasGreendlingerQuarterConfiguration
        (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) R := sorry

end

/-! ### Definition_5_4_10 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

noncomputable section

open GroupPresentation

section

variable {X : Type u} {F : Type v} [Group F]

/-!
Primary domain: Dehn-type reduction for classical small-cancellation presentations.

Layer triage:
- `source-facing`: a basis `basis : FreeGroupBasis X F`, a relator set `R : Set F`, a word
  `w : List (X × Bool)`, and the prohibition on subwords of `w` that are longer than half of a
  relator from the symmetrized family generated by `R`.
- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for reading relators on the
  chosen generators, `GroupPresentation.symmetrizedRelatorFamily` is the owner of the symmetrized
  relator family, `CyclicWord.HasPart` is the owner predicate for a cyclic part of a relator, and
  `FreeGroup.IsReduced` / `FreeGroup.IsCyclicallyReduced` are the owner reducedness predicates on
  words.
- `bridge/view`: `basis.repr '' R` transports the relators from `F` to the canonical free-group
  model on `X`, while `List.IsInfix` and `List.IsRotated` read the textbook subword and cyclic
  permutation language directly on source words.

Domain sampling:
1. `FreeGroupBasis X F` is the chapter owner for a free group with a chosen basis.
2. `symmetrizedRelatorFamily` from Proposition `3-11-2` is the owner abstraction for `R*`.
3. `CyclicWord.HasPart` from Proposition `1-7-9` is the owner predicate for a cyclic subword of a
   symmetrized relator.
4. `FreeGroup.IsReduced` and `FreeGroup.IsCyclicallyReduced` are the owner predicates for freely
   reduced and cyclically reduced words.
5. `List.IsInfix` and `List.IsRotated` are the canonical list-level owners for subwords and cyclic
   permutations of the source word `w`.

Primitive vs. derived:
- primitive source data: the source word `w`, the relator family `R`, and the existence of a
  subword of `w` longer than half of a symmetrized relator;
- derived API: `R`-reducedness and cyclic `R`-reducedness.
-/

namespace FreeGroupBasis

/-- Definition 5-4-10: a word `w` on the generators `X` is `R`-reduced with respect to `basis` if
it is freely reduced and has no subword that is longer than half of a relator from the
symmetrized family generated by `R`. -/
def is_r_reduced (basis : FreeGroupBasis X F) (R : Set F) (w : List (X × Bool)) : Prop :=
  FreeGroup.IsReduced w ∧
    ∀ ⦃part : List (X × Bool)⦄, List.IsInfix part w →
      ¬ HasLongSymmetrizedRelatorPart (basis.repr '' R) part

/-- A word is cyclically `R`-reduced when every cyclic permutation of it is `R`-reduced. -/
def is_cyclically_r_reduced (basis : FreeGroupBasis X F) (R : Set F) (w : List (X × Bool)) :
    Prop :=
  ∀ ⦃v : List (X × Bool)⦄, List.IsRotated v w → basis.is_r_reduced R v

-- Proof sketch: project the first conjunct in the definition of `is_r_reduced`.
/-- An `R`-reduced word is freely reduced. -/
theorem isReduced_of_is_r_reduced
    (basis : FreeGroupBasis X F) {R : Set F} {w : List (X × Bool)}
    (hw : basis.is_r_reduced R w) :
    FreeGroup.IsReduced w :=
  hw.1

-- Proof sketch: apply the defining rotation-invariance of `is_cyclically_r_reduced` to the
-- trivial cyclic permutation of `w`.
/-- Every cyclically `R`-reduced word is `R`-reduced. -/
theorem is_r_reduced_of_is_cyclically_r_reduced
    (basis : FreeGroupBasis X F) {R : Set F} {w : List (X × Bool)}
    (hw : basis.is_cyclically_r_reduced R w) :
    basis.is_r_reduced R w :=
  hw (List.IsRotated.refl w)

-- Proof sketch: first obtain that `w` is freely reduced from
-- `is_r_reduced_of_is_cyclically_r_reduced`. Then split `w` into the empty word, a singleton, or
-- `x :: xs ++ [y]`, invoke the canonical owner lemma
-- `FreeGroup.isCyclicallyReduced_cons_append_iff`, and prove the endpoint compatibility by
-- applying `isReduced_cons_cons` to the rotation `y :: x :: xs`.
/-- Every cyclically `R`-reduced word is cyclically reduced in the free-group sense. -/
theorem isCyclicallyReduced_of_is_cyclically_r_reduced
    (basis : FreeGroupBasis X F) {R : Set F} {w : List (X × Bool)}
    (hw : basis.is_cyclically_r_reduced R w) :
    FreeGroup.IsCyclicallyReduced w := by
  have hwReduced : FreeGroup.IsReduced w :=
    basis.isReduced_of_is_r_reduced (basis.is_r_reduced_of_is_cyclically_r_reduced hw)
  cases w using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton ws y =>
      cases ws with
      | nil =>
          simp
      | cons x xs =>
          rw [FreeGroup.isCyclicallyReduced_cons_append_iff]
          refine ⟨by simpa using hwReduced, ?_⟩
          have hrot : List.IsRotated (y :: x :: xs) (x :: xs ++ [y]) := by
            simpa using (List.IsRotated.symm (List.isRotated_concat y (x :: xs)))
          have hred : FreeGroup.IsReduced (y :: x :: xs) :=
            basis.isReduced_of_is_r_reduced (hw hrot)
          exact (FreeGroup.isReduced_cons_cons.mp hred).1

end FreeGroupBasis

end
