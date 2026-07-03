import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_9_1 (from Items/Chap03) -/
universe w

set_option autoImplicit false

noncomputable section

open Quiver.Path

/-
Primary domain: finite singular subcomplex decompositions inside an ambient `TwoComplex`.

Layer triage:
- `source-facing`: a finite singular subcomplex with no loose `1`-skeleton data, together with
  the conclusion that its connected components are singular discs equipped with explicit reduced
  boundary cycles or singular spheres whose edges are all closed up by carried faces.
- `core/canonical`: `OneComplex.GeometricEdge`,
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`,
  `TwoComplex.IsSimplyConnected`, `TwoComplex.EmbedsInPlane`, `TwoComplex.EmbedsInSphere`, and
  `TwoComplex.GeometricFace` are the owner predicates and carriers for the geometric ingredients.
- `bridge/view`: `Quiver.Path.CyclicPath`, `IsSimpleCycle`, and
  `IsCyclicallyReducedCycle` are the owner API for the chosen boundary cycle carried by a
  singular disc, while oriented-edge representatives of a geometric edge remain only a companion
  view for boundary traversal.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner abstraction for carried
   subcomplexes and their induced `2`-complexes.
2. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for simple
   connectedness of the carried `2`-complex.
3. `TwoComplex.EmbedsInPlane` and `TwoComplex.EmbedsInSphere` from Proposition `3-5-6` are the
   owner predicates for planar and spherical embeddability.
4. `OneComplex.GeometricEdge` from Definition `3-2-1` is the owner carrier for carried edges, so
   boundary-vs-interior edge data should be phrased on geometric edges rather than on oriented
   representatives.
5. `TwoComplex.GeometricFace` from Definition `3-2-4` is the owner carrier for orientation-free
   face incidence, so the incident-face API should pair naturally with geometric edges.
6. `Quiver.Path.CyclicPath`, `IsSimpleCycle`, and `IsCyclicallyReducedCycle` are the owner API
   for the explicit disc boundary cycle.

Primitive vs. derived:
- primitive data: the ambient subcomplex `S` with finite carried vertices, geometric edges, and
  faces, no loose carried vertices or edges, and for a disc component its chosen boundary cycle;
- derived API: connected-component decompositions of `S`, connectedness, simple connectedness,
  simplicity and cyclic reduction of the chosen boundary cycle, and the geometric-face incidence
  conditions distinguishing disc boundary geometric edges from interior or spherical ones.
-/

namespace Quiver.Path

private def CyclicPath.SupportsEdge {K : OneComplex} (c : CyclicPath K) (e : K.Edge) : Prop :=
  ∃ t ∈ c.1, t.hom.1 = e ∨ t.hom.1 = e⁻¹

private theorem CyclicPath.supportsEdge_inv_iff {K : OneComplex} (c : CyclicPath K) (e : K.Edge) :
    c.SupportsEdge e⁻¹ ↔ c.SupportsEdge e := by
  constructor
  · rintro ⟨t, ht, hte | hte⟩
    · exact ⟨t, ht, Or.inr hte⟩
    · exact ⟨t, ht, Or.inl (hte.trans (K.edgeInv_involutive e))⟩
  · rintro ⟨t, ht, hte | hte⟩
    · exact ⟨t, ht, Or.inr (hte.trans (K.edgeInv_involutive e).symm)⟩
    · exact ⟨t, ht, Or.inl hte⟩

/-- A geometric edge lies on a cyclic path when some, equivalently every, oriented representative
of that geometric edge is traversed by the path. -/
def CyclicPath.SupportsGeometricEdge {K : OneComplex} (c : CyclicPath K)
    (e : OneComplex.GeometricEdge K) : Prop :=
  Quotient.liftOn e (fun f ↦ c.SupportsEdge f) fun e f h ↦
    propext <| by
      rcases h with rfl | h
      · rfl
      · simpa [h] using c.supportsEdge_inv_iff f

/-- The owner-level geometric-edge condition is equivalent to traversing any chosen oriented
representative or its reverse. -/
theorem supportsGeometricEdge_iff {K : OneComplex} (c : CyclicPath K) (e : K.Edge) :
    c.SupportsGeometricEdge ⟦e⟧ ↔ ∃ t ∈ c.1, t.hom.1 = e ∨ t.hom.1 = e⁻¹ := by
  rfl

end Quiver.Path

namespace TwoComplex.Subcomplex

variable {C : TwoComplex.{w}}

/-- A family of subcomplexes is a connected-component decomposition of `S` when it partitions the
carried vertices, edges, and faces of `S`, and each piece is connected. -/
structure IsComponentDecomposition (S : Subcomplex C) {ι : Type*}
    (components : ι → Subcomplex C) : Prop where
  /-- A carried vertex of `S` lies in exactly one listed component. -/
  vertex_mem_iff (v : C.skeleton) :
    v ∈ S.skeleton.vertexSet ↔ ∃ i, v ∈ (components i).skeleton.vertexSet
  /-- A carried edge of `S` lies in exactly one listed component. -/
  edge_mem_iff (e : C.skeleton.Edge) :
    e ∈ S.skeleton.edgeSet ↔ ∃ i, e ∈ (components i).skeleton.edgeSet
  /-- A carried face of `S` lies in exactly one listed component. -/
  face_mem_iff (D : C.Face) :
    D ∈ S.faceSet ↔ ∃ i, D ∈ (components i).faceSet
  /-- Distinct listed components have disjoint vertex carriers, so they are genuinely different
  connected components of the carried `1`-skeleton. -/
  vertex_pairwiseDisjoint :
    Pairwise
      (fun i j ↦
        Disjoint (components i).skeleton.vertexSet (components j).skeleton.vertexSet)
  /-- Each listed piece is connected in its own carried `1`-skeleton. -/
  connected (i : ι) :
    Quiver.IsStronglyConnected (Quiver.Symmetrify (components i).skeleton.toOneComplex)

namespace IsComponentDecomposition

section

variable {S : Subcomplex C} {ι : Type*} {components : ι → Subcomplex C}

/-- Each listed component of a component decomposition is carried by the parent subcomplex at the
vertex level. -/
theorem vertexSet_subset (hcomponents : IsComponentDecomposition S components) (i : ι) :
    (components i).skeleton.vertexSet ⊆ S.skeleton.vertexSet := fun _ hv ↦
  (hcomponents.vertex_mem_iff _).2 ⟨i, hv⟩

/-- Each listed component of a component decomposition is carried by the parent subcomplex at the
edge level. -/
theorem edgeSet_subset (hcomponents : IsComponentDecomposition S components) (i : ι) :
    (components i).skeleton.edgeSet ⊆ S.skeleton.edgeSet := fun _ he ↦
  (hcomponents.edge_mem_iff _).2 ⟨i, he⟩

/-- Each listed component of a component decomposition is carried by the parent subcomplex at the
face level. -/
theorem faceSet_subset (hcomponents : IsComponentDecomposition S components) (i : ι) :
    (components i).faceSet ⊆ S.faceSet := fun _ hD ↦
  (hcomponents.face_mem_iff _).2 ⟨i, hD⟩

end

end IsComponentDecomposition

section SingularSurfacePieces

variable (S : Subcomplex C)

local notation "K1" => S.skeleton.toOneComplex
local notation "GeometricEdge" => OneComplex.GeometricEdge K1
local notation "verts" => S.skeleton.vertexSet
local notation "edges" => S.skeleton.edgeSet

/-- The geometric faces of `S.complex` incident to a geometric edge of the carried
`1`-skeleton. -/
def incidentGeometricFaces (e : GeometricEdge) : Set (TwoComplex.GeometricFace S.complex) :=
  { F | ∃ D : S.complex.Face,
      (⟦D⟧ : TwoComplex.GeometricFace S.complex) = F ∧
        (S.complex.boundary D).SupportsGeometricEdge e }

/-- A carried geometric edge is on the outer boundary exactly when it is incident to a unique
carried geometric face. -/
def EdgeHasUniqueIncidentGeometricFace (e : GeometricEdge) : Prop :=
  ∃ F : TwoComplex.GeometricFace S.complex,
    F ∈ S.incidentGeometricFaces e ∧
      ∀ F' : TwoComplex.GeometricFace S.complex,
        F' ∈ S.incidentGeometricFaces e → F' = F

/-- A carried geometric edge is an interior surface edge exactly when it is incident to two
distinct carried geometric faces and to no others. -/
def EdgeHasExactlyTwoIncidentGeometricFaces (e : GeometricEdge) : Prop :=
  ∃ F₁ F₂ : TwoComplex.GeometricFace S.complex,
    F₁ ≠ F₂ ∧
      F₁ ∈ S.incidentGeometricFaces e ∧
      F₂ ∈ S.incidentGeometricFaces e ∧
      ∀ F : TwoComplex.GeometricFace S.complex,
        F ∈ S.incidentGeometricFaces e → F = F₁ ∨ F = F₂

/-- A singular subcomplex is finite and has no loose carried `1`-skeleton data: every carried
vertex lies on a carried oriented edge, and every carried geometric edge occurs on the boundary of
some carried geometric face. -/
structure IsSingularSubcomplex : Prop where
  finite_vertexSet : Set.Finite verts
  finite_edgeSet : Set.Finite edges
  finite_faceSet : Set.Finite S.faceSet
  edge_exists_at_vertex (v : K1) :
    ∃ e : (K1).Edge, (K1).initial e = v ∨ (K1).terminal e = v
  incidentGeometricFace_nonempty (e : GeometricEdge) :
    ∃ F : TwoComplex.GeometricFace S.complex, F ∈ S.incidentGeometricFaces e

/-- A singular disc is a finite connected simply connected planar subcomplex whose chosen cyclic
boundary is simple, cyclically reduced, and carries exactly the geometric edges incident to one
carried geometric face; the remaining carried geometric edges are interior and incident to exactly
two carried geometric faces. -/
structure IsSingularDisc (boundary : CyclicPath K1) : Prop extends IsSingularSubcomplex S where
  faceSet_nonempty : S.faceSet.Nonempty
  connected : Quiver.IsStronglyConnected (Quiver.Symmetrify K1)
  simplyConnected : S.complex.IsSimplyConnected
  embedsInPlane : S.complex.EmbedsInPlane
  simpleCycle : IsSimpleCycle boundary
  cyclicallyReducedCycle : IsCyclicallyReducedCycle boundary
  boundary_geometricEdge_iff (e : GeometricEdge) :
    boundary.SupportsGeometricEdge e ↔ S.EdgeHasUniqueIncidentGeometricFace e
  interior_geometricEdge (e : GeometricEdge) :
    ¬ boundary.SupportsGeometricEdge e → S.EdgeHasExactlyTwoIncidentGeometricFaces e

/-- A singular disc in particular carries a simple cyclic boundary witness. -/
theorem IsSingularDisc.hasSimpleBoundary {S : Subcomplex C}
    {boundary : CyclicPath S.skeleton.toOneComplex} (hS : IsSingularDisc S boundary) :
    S.HasSimpleBoundary := by
  exact ⟨boundary, hS.simpleCycle⟩

/-- A singular sphere is a finite connected simply connected spherical subcomplex all of whose
carried geometric edges are interior edges incident to exactly two carried geometric faces. -/
structure IsSingularSphere : Prop extends IsSingularSubcomplex S where
  faceSet_nonempty : S.faceSet.Nonempty
  connected : Quiver.IsStronglyConnected (Quiver.Symmetrify K1)
  simplyConnected : S.complex.IsSimplyConnected
  embedsInSphere : S.complex.EmbedsInSphere
  interior_geometricEdge (e : GeometricEdge) :
    S.EdgeHasExactlyTwoIncidentGeometricFaces e

end SingularSurfacePieces

/-- Proposition 3-9-1: every singular subcomplex admits a finite component normal form in which
each component is either a singular disc with an explicit reduced boundary cycle or a singular
sphere. -/
-- Proof sketch: argue by induction on the total boundary length of the singular subcomplex.
-- Detachment decreases this complexity by splitting off repeated boundary segments, while sewing
-- up removes immediately cancellable boundary pairs. Repeating these moves until no further
-- reduction is possible yields components that are exactly reduced singular discs or singular
-- spheres.
theorem exists_disc_or_sphere_component_normalForm_of_singularSubcomplex
    (S : Subcomplex C) (hS : IsSingularSubcomplex S) :
    ∃ (ι : Type*) (_ : Fintype ι) (components : ι → Subcomplex C),
      IsComponentDecomposition S components ∧
        ∀ i : ι,
          (∃ boundary : CyclicPath (components i).skeleton.toOneComplex,
            IsSingularDisc (components i) boundary) ∨
            IsSingularSphere (components i) := sorry

end TwoComplex.Subcomplex

/-! ### Proposition_3_9_2 (from Items/Chap03) -/
universe u

open Quiver.Path
open CayleyComplex.Coordinates
open TwoComplex.Subcomplex

set_option autoImplicit false

/-
Layer triage:
- `source-facing`: a reduced boundary word in the normal closure of the relators of a
  presentation, and a genuine singular disc carried by a relator-filled Cayley `2`-complex whose
  boundary label is that word.
- `core/canonical`: `FreeGroup.IsReduced` and `Subgroup.normalClosure` are the owner predicates
  for the reduced-word and normal-closure hypotheses, `CayleyComplex.Coordinates` is the chapter
  owner for an actual Cayley `2`-complex with relator faces, `TwoComplex.Subcomplex` is the owner
  for a carried van Kampen diagram inside that ambient complex,
  `TwoComplex.Subcomplex.IsSingularDisc` is the chapter owner for the source-side disc geometry
  together with its explicit boundary cycle, and `PresentationCoordinates.boundaryLabel` is the
  owner map reading the signed boundary word of an actual Cayley loop.
- `bridge/view`: `PresentationCoordinates.fromIntrinsicCayley` is the canonical sign-sensitive
  map from the intrinsic Cayley graph to the chosen actual Cayley `1`-skeleton, while
  `PresentationCoordinates.boundaryLabel_fromIntrinsicCayley_mapLoop` is the comparison lemma
  relating intrinsic and actual boundary-word readings.

Domain sampling:
1. `FreeGroup.IsReduced` is mathlib's owner predicate for reduced signed words.
2. `Subgroup.normalClosure` is the canonical owner for the normal closure of the relator set.
3. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the chapter owner for an actual
   Cayley `2`-complex whose oriented faces are indexed by relators.
4. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner for a carried singular diagram
   inside that ambient `2`-complex.
5. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for
   disc-like singular diagrams with an explicit boundary cycle.
6. `PresentationCoordinates.boundaryLabel` from Proposition `3-5-9` is the owner map for reading
   signed words on the actual Cayley skeleton, while
   `PresentationCoordinates.fromIntrinsicCayley` and
   `PresentationCoordinates.boundaryLabel_fromIntrinsicCayley_mapLoop` are the comparison
   bridge/view API relating that direct reading to the intrinsic Cayley graph.
7. `GroupPresentation.cayleyOneComplex R` and `GroupPresentation.cayleyPathLabel R` from Lemma
   `3-5-7` remain the intrinsic owner API for signed boundary words.

Primitive vs. derived:
- primitive data: the relator set `R`, the reduced signed word `w`, an ambient `2`-complex `C`
  equipped with actual Cayley coordinates, a singular disc `S : TwoComplex.Subcomplex C`, and a
  boundary loop `p` whose cyclic path is the explicit boundary cycle in the owner predicate
  `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`;
- derived API: the canonical bridge from intrinsic Cayley loops to actual Cayley loops and the
  direct equality `boundaryLabel coords ... = w` expressing that the ambient boundary loop reads
  the word `w`.
-/

namespace GroupPresentation

variable {X : Type u}

/-- Proposition 3-9-2: if a reduced word `w` represents an element of the normal closure of the
relators `R`, then there is a simple singular disc carried by an actual Cayley `2`-complex for
`(X; R)` whose boundary label, read in the chosen Cayley coordinates, is exactly `w`. -/
-- Proof sketch: write the normal-closure element as a product of conjugates of relators and
-- inverse relators, build the corresponding bouquet of singular relator discs in the Cayley
-- diagram, and then apply sewing-up and detachment until the remaining boundary word is the
-- given reduced word `w`.
theorem exists_cayleySingularDisc_of_reduced_mem_normalClosure
    (R : Set (FreeGroup X)) (w : List (SignedLetter X))
    (hw_reduced : FreeGroup.IsReduced w)
    (hw_normal : FreeGroup.mk w ∈ Subgroup.normalClosure R) :
    ∃ (C : TwoComplex) (coords : PresentationCoordinates C R)
      (S : TwoComplex.Subcomplex C) (p : Loop S.skeleton.toOneComplex),
      S.IsSingularDisc (cyclicPath p) ∧
        boundaryLabel coords (S.skeleton.inclusion.mapLoop p) = w := sorry

end GroupPresentation

/-! ### Proposition_3_9_3 (from Items/Chap03) -/
universe u v

open Subgroup (closure normalClosure)

section

variable {X : Type u} {F : Type v} [Group F]

namespace FreeGroupBasis

variable (basis : FreeGroupBasis X F)

local notation "Gp[" Y "]" => closure (basis '' Y)

-- Layer triage:
-- `source-facing`: a free group `F` equipped with a chosen basis `basis : FreeGroupBasis X F`,
-- basis subsets `Y, Z : Set X`, relator sets `P, Q : Set F` lying in the generated subgroups
-- `Gp(Y)` and `Gp(Z)`, and the existence of an intermediate relator set `M` supported on
-- `Y ∩ Z`.
-- `core/canonical`: the owner namespace `FreeGroupBasis`, together with `Subgroup.closure` and
-- `Subgroup.normalClosure`.
-- `bridge/view`: the source subgroup notation `Gp(Y)` is rendered by the local notation `Gp[Y]`
-- backed by the canonical owner `closure (basis '' Y)`, while the normal closure remains the
-- owner expression `normalClosure P`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the canonical owner for a free group together with a specified
--    basis, and nearby basis-dependent Magnus theorems already live in `namespace FreeGroupBasis`.
-- 2. `Subgroup.closure` is the canonical owner for the subgroup generated by a subset.
-- 3. `Subgroup.normalClosure` is the canonical owner for the normal closure of a subset.
-- Primitive vs. derived:
-- the primitive data are the chosen basis, the two basis subsets, and the relator sets `P` and
-- `Q`; the generated subgroups and normal closures are derived canonically from those data, so no
-- extra wrapper around the three subset conditions is needed.

-- Proof sketch: reduce to the case where `Y ∪ Z` is the whole basis and `Q` is a singleton
-- cyclically reduced word. Fill that word by a simple van Kampen diagram over the relators `P`,
-- delete interior edges, and let `M` be the set of boundary labels of the resulting faces. Those
-- boundary labels lie in the subgroup generated by `Y ∩ Z`, remain in the normal closure of `P`,
-- and their normal closure contains the original set `Q`.
/-- Proposition 3-9-3: if `P` lies in the subgroup generated by the basis subset `Y`, `Q` lies in
the subgroup generated by `Z`, and `Q` is contained in the normal closure of `P`, then there is a
set `M` in the subgroup generated by `Y ∩ Z` which still lies in the normal closure of `P` and
whose normal closure contains `Q`. -/
theorem exists_intersection_relator_set_of_subset_normalClosure
    (Y Z : Set X) (P Q : Set F)
    (hP : P ⊆ Gp[Y])
    (hQ : Q ⊆ Gp[Z])
    (hQncl : Q ⊆ normalClosure P) :
    ∃ M : Set F,
      M ⊆ Gp[Y ∩ Z] ∧
        M ⊆ normalClosure P ∧
        Q ⊆ normalClosure M := sorry

end FreeGroupBasis

end

/-! ### Proposition_3_9_4 (from Items/Chap03) -/
universe u

noncomputable section

section

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X
local notation "basis" => FreeGroupBasis.ofFreeGroup X

-- Layer triage:
-- `source-facing`: Proposition 3-9-4 is the free-group specialization of Magnus's normal-closure
-- occurrence theorem for a cyclically reduced relator.
-- `core/canonical`: `FreeGroupBasis.ofFreeGroup X`, `basisLetterOccurs`,
-- `FreeGroup.IsCyclicallyReduced`, and `Subgroup.normalClosure`.
-- `bridge/view`: specializing the basis-level theorem to the canonical basis of `FreeGroup X`
-- recovers the textbook wording that a generator occurring in `r` must also occur in any
-- nontrivial consequence `w` of `r`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofFreeGroup X` is the canonical basis owner for `FreeGroup X`.
-- 2. `basisLetterOccurs` from Proposition `1-7-4` is the chapter owner predicate for the source
--    phrase “the generator `x` occurs in a word”.
-- 3. `FreeGroupBasis.basisLetterOccurs_of_mem_normalClosure_singleton_of_isCyclicallyReduced`
--    from
--    Proposition `2-5-1` is the already-canonical Magnus statement at the correct owner level.
-- 4. `FreeGroup.IsCyclicallyReduced` and `Subgroup.normalClosure` are the canonical reduced-word
--    and normal-closure constructions on which that theorem is built.
--
-- Primitive vs. derived:
-- the primitive data remain the relator `r`, the normal-closure element `w`, and the generator
-- `x`; the occurrence relation is derived owner-side API through the canonical basis, so this
-- file does not keep a second public theorem phrased by raw membership in `toWord.map Prod.fst`.

/- Proposition 3-9-4: for the canonical basis of `FreeGroup X`, this is exactly Proposition
`2-5-1`. The source phrase “`x` occurs in a word” is already captured by
`basisLetterOccurs basis x`, so this item is a direct recall of the upstream owner theorem rather
than a duplicate free-group-only wrapper. -/
#check
  (FreeGroupBasis.basisLetterOccurs_of_mem_normalClosure_singleton_of_isCyclicallyReduced basis :
    ∀ {r w : FreeGroup X} {x : X},
      FreeGroup.IsCyclicallyReduced r.toWord →
        basisLetterOccurs basis x r →
          w ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
            w ≠ 1 →
              basisLetterOccurs basis x w)

end

/-! ### Proposition_3_9_5 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory for staggered presentations and interval restrictions on
normal closures.

Layer triage:
- `source-facing`: a staggered presentation on generators `X` with a distinguished ordered subset
  `X₀`, together with the least and greatest generators of `X₀` occurring in a word.
- `core/canonical`: `FreeGroup X`, `FreeGroupBasis.ofFreeGroup X`, `basisLetterOccurs`, `IsLeast`,
  `IsGreatest`, `Set.Icc`, and `Subgroup.normalClosure`.
- `bridge/view`: distinguished support is the subset of `X₀` cut out by the owner predicate
  `basisLetterOccurs (FreeGroupBasis.ofFreeGroup X)`, and interval support is expressed as
  inclusion in the canonical interval `Set.Icc xₐ x_b`.

Domain sampling:
1. `FreeGroup X` is the owner object for words in the presentation.
2. `FreeGroupBasis.ofFreeGroup X` together with `basisLetterOccurs` from Proposition `1-7-4` is
   the chapter owner abstraction for the source phrase “the generator `x` occurs in `w`”.
3. `IsLeast`, `IsGreatest`, and `Set.Icc` are the canonical order-theoretic owners for extremal
   distinguished generators and the interval they determine.
4. Proposition `2-5-2` shows the same chapter-level interval/normal-closure pattern for indexed
   generators; this file keeps the extra distinguished-subset data source-facing, but it should
   still reuse the same owner-level occurrence and interval abstractions.

Primitive vs. derived:
- primitive public data: the ordered distinguished subset `X₀` and the indexed relator family
  `r`;
- derived API: the distinguished support set, distinguished interval support, the staggered
  predicate, and the interval-restricted relator set.
-/

namespace GroupPresentation

section

variable {X : Type u} [LinearOrder X]

open Subgroup

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-- The distinguished generators from `X₀` occurring in `w`. -/
def distinguishedSupport (X₀ : Set X) (w : FreeGroup X) : Set X :=
  X₀ ∩ {x | basisLetterOccurs basis x w}

/-- Every distinguished generator of `X₀` occurring in `w` lies in the interval `xₐ ≤ x ≤ x_b`. -/
def SupportedOnDistinguishedInterval (X₀ : Set X) (xₐ x_b : X) (w : FreeGroup X) : Prop :=
  distinguishedSupport X₀ w ⊆ Set.Icc xₐ x_b

/-- The generators `xₐ` and `x_b` are the least and greatest distinguished generators from `X₀`
occurring in `w`. -/
def HasExtremeDistinguishedSupport (X₀ : Set X) (w : FreeGroup X) (xₐ x_b : X) : Prop :=
  IsLeast (distinguishedSupport X₀ w) xₐ ∧
    IsGreatest (distinguishedSupport X₀ w) x_b

/-- Extreme distinguished support bounds the full distinguished support inside the interval
`[xₐ, x_b]`. -/
theorem supportedOnDistinguishedInterval_of_hasExtremeDistinguishedSupport
    {X₀ : Set X} {w : FreeGroup X} {xₐ x_b : X}
    (h : HasExtremeDistinguishedSupport X₀ w xₐ x_b) :
    SupportedOnDistinguishedInterval X₀ xₐ x_b w := by
  intro x hx
  exact ⟨h.1.2 hx, h.2.2 hx⟩

-- Proof sketch: the least distinguished support element already lies in `distinguishedSupport X₀ w`.
/-- Extreme distinguished support implies that some generator from `X₀` occurs in `w`. -/
theorem exists_distinguished_generator_of_hasExtremeDistinguishedSupport
    {X₀ : Set X} {w : FreeGroup X} {xₐ x_b : X}
    (h : HasExtremeDistinguishedSupport X₀ w xₐ x_b) :
    ∃ x : X, x ∈ X₀ ∧ basisLetterOccurs basis x w := by
  refine ⟨xₐ, ?_⟩
  simpa [distinguishedSupport] using h.1.1

end

section

variable {X : Type u} [LinearOrder X]
variable {J : Type v} [Preorder J]

open Subgroup

/-- A relator family is staggered relative to the distinguished generator set `X₀` when each
relator has least and greatest distinguished generators in its support, and those endpoints
increase with the relator order. -/
def IsStaggeredPresentation (X₀ : Set X) (r : J → FreeGroup X) : Prop :=
  ∃ initial terminal : J → X,
    (∀ j, HasExtremeDistinguishedSupport X₀ (r j) (initial j) (terminal j)) ∧
      StrictMono initial ∧
      StrictMono terminal

/-- The interval-restricted relator set consists of those relators whose distinguished generators
from `X₀` all lie between `xₐ` and `x_b`. -/
def relatorsSupportedOnDistinguishedInterval
    (X₀ : Set X) (r : J → FreeGroup X) (xₐ x_b : X) : Set (FreeGroup X) :=
  Set.range r ∩ SupportedOnDistinguishedInterval X₀ xₐ x_b

-- Proof sketch: choose a van Kampen diagram for `w` over the relators `r`. The staggered ordering
-- forces the least and greatest distinguished generators on the boundary word to control the
-- distinguished supports of every relator that appears in the diagram. Removing extremal faces
-- inductively leaves a diagram using only relators whose distinguished generators lie between
-- those two extremes, so `w` already lies in the normal closure of the interval-restricted
-- relators.
/-- Proposition 3-9-5: if `r` is a staggered presentation relative to `X₀` and a nontrivial word
`w` lies in the normal closure of `r`, then `w` contains generators of `X₀`; choosing the least
and greatest such generators `xₐ` and `x_b`, the word already lies in the normal closure of the
relators whose distinguished generators from `X₀` all lie between `xₐ` and `x_b`. -/
theorem exists_extreme_distinguished_support_and_interval_normalClosure
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    {w : FreeGroup X} (hw : w ∈ normalClosure (Set.range r)) (hwne : w ≠ 1) :
    ∃ xₐ x_b : X,
      HasExtremeDistinguishedSupport X₀ w xₐ x_b ∧
        w ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) := sorry

end

end GroupPresentation

/-! ### Proposition_3_9_6 (from Items/Chap03) -/
universe u v w z

set_option autoImplicit false

noncomputable section

open Quiver.Path
open GroupPresentation

/-!
Primary domain: combinatorial group theory of staggered presentations and disc diagrams over a
presentation complex.

Layer triage:
- `source-facing`: a staggered presentation relative to a distinguished ordered subset `X₀ ⊆ X`,
  an actual presentation complex `K(X; R)` realized by
  `PresentationComplex.Coordinates K X R`, a singular disc `S : TwoComplex.Subcomplex C`, a
  diagram `φ : S.complex → K`, and a boundary loop `p` whose cyclic path is the boundary data in
  `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`.
- `core/canonical`: `GroupPresentation.IsStaggeredPresentation` is the chapter owner for the
  staggered-presentation hypothesis, `PresentationComplex.Coordinates` is the owner for the actual
  presentation complex, `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the
  chapter owner for disc diagrams together with explicit boundary cycle data, `TwoComplex.Hom` is
  the owner for the diagram map, and `basisLetterOccurs` is the chapter owner for the source
  phrase “the generator `x` occurs in the boundary word”.
- `bridge/view`: the source-facing loop `p` is tied to the diagram boundary through the owner
  predicate `TwoComplex.Subcomplex.IsSingularDisc`.

Domain sampling:
1. `GroupPresentation.IsStaggeredPresentation` from Proposition `3-9-5` is the existing chapter
   owner for staggeredness.
2. `PresentationComplex.Coordinates` from Proposition `3-4-3` is the owner abstraction for the
   presentation complex attached to a relator set, so this file should speak directly about
   `K(X; R)` rather than an unrelated `TwoComplex`.
3. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for the
   singular-disc source together with its explicit boundary cycle.
4. `TwoComplex.Hom` from Proposition `3-3-4` is the owner abstraction for a combinatorial diagram
   map into that presentation complex.
5. `basisLetterOccurs` from Proposition `1-7-4` is the chapter owner for the source phrase
   “the generator `x` occurs”.
6. `CayleyComplex.Coordinates.pathLabel` and `boundaryLabel` from Proposition `3-5-9` give the
   established owner pattern for reading a signed word from a loop.

Primitive vs. derived:
- primitive data: the distinguished subset `X₀`, the relator family `r`, the presentation-complex
  coordinates `coords : PresentationComplex.Coordinates K X (Set.range r)`, the singular disc
  `S : TwoComplex.Subcomplex C`, the morphism `φ : S.complex → K`, and the boundary loop `p`
  recorded in `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`;
- derived API: which generators of `X` occur on presentation-complex edges, and the boundary word
  read from a chosen loop after applying the diagram map.
-/

namespace PresentationComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {K : TwoComplex.{v}}

variable {D : TwoComplex.{v}}

/-- The generators occurring in a diagram over the presentation complex are the generators
appearing on the images of its oriented edges. -/
def occurringGenerators (coords : Coordinates K X R)
    (φ : TwoComplex.Hom D K) : Set X :=
  { x | ∃ e : D.skeleton.Edge, (coords.edgeEquiv (φ.toEdge e)).1 = x }

/-- The signed-generator word read along a path in the source `1`-skeleton after applying the
diagram map to the presentation complex. -/
def pathLabel (coords : Coordinates K X R) (φ : TwoComplex.Hom D K) {a b : D.skeleton} :
    Quiver.Path a b → List (SignedLetter X)
  | .nil => []
  | .cons p e => pathLabel coords φ p ++ [coords.edgeEquiv (φ.toEdge e.1)]

/-- The signed-generator boundary word read from a loop in the source `1`-skeleton after applying
the diagram map. -/
def boundaryLabel (coords : Coordinates K X R)
    (φ : TwoComplex.Hom D K) (p : Loop D.skeleton) : List (SignedLetter X) :=
  pathLabel coords φ p.2

section Proposition396

variable [LinearOrder X]
variable {J : Type z} [Preorder J]
local notation "basis" => FreeGroupBasis.ofFreeGroup X

-- Proof sketch: the staggered ordering and the disc-diagram topology force an extremal
-- distinguished face to survive on the outer boundary. The chapter owner
-- `TwoComplex.Subcomplex.IsSingularDisc` packages the source disc together with the fact that the
-- chosen loop `p` carries its boundary cycle. Reading the resulting boundary word through
-- `coords.boundaryLabel φ p`, the extremal generator therefore occurs in that canonical word.
/-- Proposition 3-9-6: let `coords : PresentationComplex.Coordinates K X (Set.range r)` realize
the presentation complex of a staggered relator family `r`, let `S` be a singular disc, let
`φ : S.complex → K` be a diagram over that complex, and let `p` be a loop carrying the boundary
cycle of `S`. If `x` is either the greatest or the least distinguished generator from `X₀`
occurring on the edges of `S.complex`, then `x` already occurs in the boundary word read from
`p`. -/
theorem basisLetterOccurs_boundaryLabel_of_isGreatest_or_isLeast
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    {C : TwoComplex.{v}} (S : TwoComplex.Subcomplex C)
    {K : TwoComplex.{v}} (coords : Coordinates K X (Set.range r))
    (φ : TwoComplex.Hom S.complex K) (p : Loop S.skeleton.toOneComplex)
    (hS : TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)) {x : X}
    (hx : IsGreatest (X₀ ∩ coords.occurringGenerators φ) x ∨
      IsLeast (X₀ ∩ coords.occurringGenerators φ) x) :
    basisLetterOccurs basis x (FreeGroup.mk (coords.boundaryLabel φ p)) := sorry

end Proposition396

end PresentationComplex.Coordinates

/-! ### Proposition_3_9_7 (from Items/Chap03) -/
universe u v w

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory of staggered presentations and spherical diagrams over
presentation complexes.

Layer triage:
- `source-facing`: a staggered relator family on the indexed generators `Σ i, Y i`, a spherical
  diagram over an actual presentation complex `K(Σ i, Y i; range r)`, and the reducedness
  condition on that diagram.
- `core/canonical`: `GroupPresentation.IsStaggeredRelatorFamily` from Proposition `2-5-2` is the
  chapter owner for staggered relator families, `PresentationComplex.Coordinates` from
  Proposition `3-4-3` is the owner for the presentation complex of `(Σ i, Y i; range r)`, and
  `TwoComplex.IsSphericalDiagram`, `TwoComplex.Hom`, and `TwoComplex.Hom.mapBoundaryStar` are the
  owners for the spherical source, the diagram map, and its induced corner map.
- `bridge/view`: the source-facing reducedness condition is expressed by injectivity of
  `mapBoundaryStar` at each source vertex.

Domain sampling:
1. `GroupPresentation.IsStaggeredRelatorFamily` from Proposition `2-5-2` is the existing chapter
   owner for staggeredness, so this file should reuse it rather than restate the same support API.
2. `PresentationComplex.Coordinates` from Proposition `3-4-3` is the owner abstraction for a
   chosen presentation complex of `(Σ i, Y i; range r)`, so the main theorem should refer to that
   object rather than an unrelated `TwoComplex`.
3. `TwoComplex.Hom` and `TwoComplex.Hom.mapBoundaryStar` from Proposition `3-3-4` are the owner
   abstractions for combinatorial diagram maps and their induced boundary-star maps.
4. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for simple
   connectedness of the source complex.
5. `TwoComplex.EmbedsInSphere` from Proposition `3-5-6` is the owner predicate for spherical
   embeddability.

Primitive vs. derived:
- primitive data: a chosen presentation complex
  `coords : PresentationComplex.Coordinates K Generators (Set.range r)`, the source complex
  `D : TwoComplex`, and a morphism `φ : TwoComplex.Hom D K`;
- derived API: the owner predicate `D.IsSphericalDiagram` packaging connectedness of `D.skeleton`,
  simple connectedness of `D`, and embeddability of `D` in the sphere, together with injectivity
  of `φ.mapBoundaryStar` at every source vertex.
-/

open GroupPresentation

namespace TwoComplex

/-- A spherical diagram is a connected simply connected `2`-complex that embeds in the sphere. -/
class IsSphericalDiagram (D : TwoComplex) : Prop where
  /-- The underlying `1`-skeleton is connected. -/
  connected : Quiver.IsStronglyConnected (Quiver.Symmetrify D.skeleton)
  /-- The source complex is simply connected. -/
  simplyConnected : IsSimplyConnected D
  /-- The source complex embeds in the `2`-sphere. -/
  embedsInSphere : D.EmbedsInSphere

instance {D : TwoComplex} [hD : IsSphericalDiagram D] : IsSimplyConnected D :=
  hD.simplyConnected

end TwoComplex

section Proposition397

variable {ι : Type u} [LinearOrder ι]
variable {Y : ι → Type v}
variable {J : Type w} [Preorder J]

local notation "Generators" => Σ i, Y i

-- Proof sketch: argue by contradiction from a reduced spherical diagram over the presentation
-- complex. A staggered relator family admits an extremal face in any spherical diagram; the local
-- injectivity of `TwoComplex.Hom.mapBoundaryStar` at each source vertex forbids the cancellation
-- that such an extremal face would force, so no reduced spherical diagram can exist.
/-- Proposition 3-9-7: if `r` is a staggered relator family on the indexed generators
`Σ i, Y i`, then any actual presentation complex `K(Σ i, Y i; range r)` admits no reduced
spherical diagram over it. -/
theorem no_reduced_spherical_diagram_over_staggered_presentation
    (r : J → FreeGroup Generators) (hstaggered : IsStaggeredRelatorFamily r) {K : TwoComplex}
    (coords : PresentationComplex.Coordinates K Generators (Set.range r)) :
    ¬ ∃ (D : TwoComplex) (φ : TwoComplex.Hom D K),
        D.IsSphericalDiagram ∧
        ∀ v : D.skeleton, Function.Injective (φ.mapBoundaryStar v) :=
  sorry

end Proposition397
