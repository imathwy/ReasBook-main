import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_10_1 (from Items/Chap03) -/
universe u

open Quiver.Path
open CayleyComplex.Coordinates

set_option autoImplicit false

noncomputable section

/-!
Primary domain: spherical diagrams over Cayley complexes and the asphericity of a presentation.

Layer triage:
- `source-facing`: a spherical diagram over the actual Cayley complex `C(X; R)`, its reducedness,
  reduction, triviality, and the resulting asphericity notion for the presentation.
- `core/canonical`: `CayleyComplex.Coordinates` is the owner for the actual Cayley complex of
  `(X; R)`, `TwoComplex.IsSphericalDiagram` is the owner predicate for a combinatorial sphere,
  `TwoComplex.Subcomplex.IsSingularDisc` is the owner predicate for singular subdiscs,
  `TwoComplex.Hom` and `OneComplex.Hom.mapLoop` are the owner maps for sending a carried loop in
  a subdisc into the ambient Cayley complex, and
  `CayleyComplex.Coordinates.boundaryLabel` is the owner for boundary labels in the actual
  Cayley complex.
- `bridge/view`: the source phrase “a spherical diagram is a pair `(S, f)`” is packaged by the
  structure `CayleyComplex.Coordinates.SphericalDiagram`, while the reduction operation is
  expressed by a direct one-step relation carrying the chosen reducible subdisc, its deleted-face
  complement, and explicit sewing comparison data into the target spherical diagram; then
  `Relation.ReflTransGen` is the canonical owner for finite reduction sequences.

Domain sampling:
1. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the chapter owner for a chosen actual
   Cayley complex attached to `(X; R)`, so the source-facing API should land directly in `C`.
2. `TwoComplex.IsSphericalDiagram` from Proposition `3-9-7` already packages the connected,
   simply connected, sphere-embedding part of “combinatorial sphere”.
3. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the owner for a singular
   subdisc with explicit boundary loop data.
4. `OneComplex.Hom.mapLoop` applied to the inclusion `S.skeleton.inclusion`,
   `TwoComplex.Hom.mapLoop`, and
   `CayleyComplex.Coordinates.boundaryLabel` are the chapter owners for comparing a carried
   subdisc boundary loop with its image in the actual Cayley complex and reading the resulting
   signed boundary word there.
5. `Relation.ReflTransGen` is the canonical closure operator for “obtainable by finitely many
   reductions”, so triviality should be expressed with that owner rather than a bespoke
   transitive closure.

Primitive vs. derived:
- primitive data: the source `2`-complex, the map into the actual Cayley complex, finiteness of
  the source cells, and for a reduction step the chosen two-face singular subdisc, the complement
  of the deleted faces, and the explicit sewing comparison into the target;
- derived API: reducedness, triviality via repeated reductions, and asphericity of the
  presentation.
-/

namespace TwoComplex.Subcomplex

/-- A singular subdisc has exactly two geometric faces when its carried face set has exactly two
elements modulo orientation reversal. -/
def HasExactlyTwoGeometricFaces {C : TwoComplex} (S : Subcomplex C) : Prop :=
  ∃ F₁ F₂ : TwoComplex.GeometricFace S.complex,
    F₁ ≠ F₂ ∧
      ∀ F : TwoComplex.GeometricFace S.complex, F = F₁ ∨ F = F₂

end TwoComplex.Subcomplex

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- Definition 3-10-1 (1): a spherical diagram over `(X; R)` is a finite combinatorial sphere
together with a dimension-preserving map into the actual Cayley complex `C(X; R)`. -/
structure SphericalDiagram
    (coords : PresentationCoordinates C R) where
  /-- The finite combinatorial sphere underlying the spherical diagram. -/
  source : TwoComplex
  /-- The dimension-preserving map into the Cayley complex `C(X; R)`. -/
  map : TwoComplex.Hom source C
  /-- The source has finitely many vertices. -/
  finite_vertex : Finite source.skeleton
  /-- The source has finitely many oriented edges. -/
  finite_edge : Finite source.skeleton.Edge
  /-- The source has finitely many oriented faces. -/
  finite_face : Finite source.Face
  /-- The source is a combinatorial sphere. -/
  spherical : source.IsSphericalDiagram

namespace SphericalDiagram

variable {coords : PresentationCoordinates C R}

/-- A spherical diagram is used via its underlying source `2`-complex. -/
instance : CoeOut (SphericalDiagram coords) TwoComplex where
  coe := SphericalDiagram.source

/-- The source `1`-skeleton of a spherical diagram is finite. -/
instance (Δ : SphericalDiagram coords) : Finite Δ.source.skeleton := Δ.finite_vertex

/-- The oriented edge set of the source of a spherical diagram is finite. -/
instance (Δ : SphericalDiagram coords) : Finite Δ.source.skeleton.Edge := Δ.finite_edge

/-- The oriented face set of the source of a spherical diagram is finite. -/
instance (Δ : SphericalDiagram coords) : Finite Δ.source.Face := Δ.finite_face

/-- A carried singular subdisc has trivial boundary label when one of its boundary loops reads a
word equal to `1` in the free group on the generators. -/
def HasTrivialBoundaryLabel (Δ : SphericalDiagram coords)
    (S : TwoComplex.Subcomplex Δ.source) : Prop :=
  ∃ (p : Loop S.skeleton.toOneComplex)
    (_ : TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p))
    (w : List (SignedLetter X)),
      boundaryLabel coords (Δ.map.mapLoop (S.skeleton.inclusion.mapLoop p)) = w ∧
        FreeGroup.mk w = 1

/-- A spherical diagram has a reducible subdisc when it contains a singular two-face subdisc whose
boundary label is trivial in the free group. -/
def HasReducibleSubdisc (Δ : SphericalDiagram coords) : Prop :=
  ∃ S : TwoComplex.Subcomplex Δ.source,
    S.HasExactlyTwoGeometricFaces ∧
      Δ.HasTrivialBoundaryLabel S

/-- Definition 3-10-1 (2): a spherical diagram is reduced when it contains no singular subdisc
with exactly two geometric faces and trivial boundary label. -/
def IsReduced (Δ : SphericalDiagram coords) : Prop :=
  ¬ Δ.HasReducibleSubdisc

/-- The deleted-face complement of a chosen reducible subdisc is the carried subcomplex whose
oriented faces are exactly the ambient faces not belonging to that subdisc. -/
def IsDeletedFaceComplement (Δ : SphericalDiagram coords)
    (S T : TwoComplex.Subcomplex Δ.source) : Prop :=
  ∀ D : Δ.source.Face, D ∈ T.faceSet ↔ D ∉ S.faceSet

/-- A sewing comparison from the deleted-face complement into a target spherical diagram is a
surjective map on the carried `1`-skeleton, bijective on the remaining oriented faces, and
compatible with the ambient map to the actual Cayley complex. -/
def IsSewingComparison (Δ : SphericalDiagram coords) (T : TwoComplex.Subcomplex Δ.source)
    (Δ' : SphericalDiagram coords) (sew : TwoComplex.Hom T.complex Δ'.source) : Prop :=
  let C' := T.complex
  let K := C'.skeleton
  Function.Surjective sew.toVertex ∧
    Function.Surjective sew.toEdge ∧
    Function.Bijective sew.mapFace ∧
    (∀ v : K, Δ'.map.toVertex (sew.toVertex v) = Δ.map.toVertex v.1) ∧
    (∀ e : K.Edge,
      Δ'.map.toEdge (sew.toEdge e) = Δ.map.toEdge e.1) ∧
    ∀ D : C'.Face, Δ'.map.mapFace (sew.mapFace D) = Δ.map.mapFace D.1

/-- Definition 3-10-1 (3): a one-step reduction deletes a reducible singular two-face subdisc and
sews up the complementary faces. If the chosen subdisc already contains every oriented face of the
source, the result is the empty diagram. -/
inductive ReductionStep : Option (SphericalDiagram coords) → Option (SphericalDiagram coords) → Prop
  | toEmpty
      (Δ : SphericalDiagram coords)
      (reducibleSubdisc : TwoComplex.Subcomplex Δ.source)
      (reducible_twoFace : reducibleSubdisc.HasExactlyTwoGeometricFaces)
      (reducible_trivialBoundary : Δ.HasTrivialBoundaryLabel reducibleSubdisc)
      (covers_faces : ∀ D : Δ.source.Face, D ∈ reducibleSubdisc.faceSet) :
      ReductionStep (some Δ) none
  | toDiagram
      (Δ Δ' : SphericalDiagram coords)
      (reducibleSubdisc : TwoComplex.Subcomplex Δ.source)
      (reducible_twoFace : reducibleSubdisc.HasExactlyTwoGeometricFaces)
      (reducible_trivialBoundary : Δ.HasTrivialBoundaryLabel reducibleSubdisc)
      (deletedFaceComplement : TwoComplex.Subcomplex Δ.source)
      (deletedFaceComplement_spec :
        IsDeletedFaceComplement Δ reducibleSubdisc deletedFaceComplement)
      (sew : TwoComplex.Hom deletedFaceComplement.complex Δ'.source)
      (sew_spec :
        IsSewingComparison Δ deletedFaceComplement Δ' sew) :
      ReductionStep (some Δ) (some Δ')

/-- Definition 3-10-1 (4): a spherical diagram is trivial when a finite sequence of reductions
carries it to the empty diagram. -/
def IsTrivial (Δ : SphericalDiagram coords) : Prop :=
  Relation.ReflTransGen ReductionStep (some Δ) none

end SphericalDiagram

/-- Definition 3-10-1 (5): the presentation `(X; R)` and its associated Cayley complex are
aspherical when every spherical diagram over `C(X; R)` is trivial. -/
def IsAspherical
    (coords : PresentationCoordinates C R) : Prop :=
  ∀ Δ : SphericalDiagram coords, Δ.IsTrivial

end CayleyComplex.Coordinates

/-! ### Definition_3_10_2 (from Items/Chap03) -/
universe u

set_option autoImplicit false

section

namespace List

variable {G : Type u} [Group G]

/-!
Primary domain: finite list-valued Peiffer rewrites in a group.

Layer triage:
- `source-facing`: the first-kind Peiffer formula replacing an adjacent pair `(a, b)` by
  `(b, b⁻¹ * a * b)`.
- `core/canonical`: `List G` is the owner abstraction for a finite ordered sequence, and
  `List.IsAdjacentConjugatingSwap` is the chapter owner relation for the adjacent conjugating
  rewrite `(a, b) ↦ (a * b * a⁻¹, a)`.
- `bridge/view`: the first-kind source formula is exactly the converse relation
  `Function.swap IsAdjacentConjugatingSwap`, used downstream in the short form
  `IsAdjacentConjugatingSwap π' π`, so no parallel first-kind predicate is needed.

Domain sampling:
1. `List G` is the canonical owner for a finite sequence `(p₁, ..., pₙ)`.
2. `List.append` and list literals `[a, b]` give the cleanest source-faithful way to isolate an
   adjacent pair without separate index bookkeeping.
3. `List.prod` together with `List.prod_append` is the canonical aggregate API on a group-valued
   list.
4. `Function.swap` is the canonical owner-side operation for reversing a binary relation, so it
   captures the first-kind orientation without introducing a second predicate.
5. Group conjugation is represented directly by the standard term `a * b * a⁻¹`.

Primitive vs. derived:
- primitive data: the owner relation `IsAdjacentConjugatingSwap` on the two lists;
- derived API: the converse-owner recall `Function.swap IsAdjacentConjugatingSwap`, the
  source-facing bridge theorem below, and the owner invariants of length and total product.
-/

/-- The chapter owner relation for the adjacent conjugating rewrite used in Peiffer
transformations. -/
def IsAdjacentConjugatingSwap (π π' : List G) : Prop :=
  ∃ left right : List G, ∃ a b : G,
    π = left ++ [a, b] ++ right ∧
      π' = left ++ [a * b * a⁻¹, a] ++ right

/-- An adjacent conjugating swap preserves the length of the sequence. -/
theorem length_eq_of_isAdjacentConjugatingSwap {π π' : List G}
    (h : IsAdjacentConjugatingSwap π π') :
    π.length = π'.length := by
  rcases h with ⟨left, right, a, b, rfl, rfl⟩
  simp

/-- An adjacent conjugating swap preserves the total product of the sequence. -/
theorem prod_eq_of_isAdjacentConjugatingSwap {π π' : List G}
    (h : IsAdjacentConjugatingSwap π π') :
    π.prod = π'.prod := by
  rcases h with ⟨left, right, a, b, rfl, rfl⟩
  simp [List.prod_append, mul_assoc]

/- Definition 3-10-2: the textbook first-kind Peiffer transformation is the converse relation
`Function.swap List.IsAdjacentConjugatingSwap` of the chapter owner relation. -/
#check Function.swap IsAdjacentConjugatingSwap

/-- Definition 3-10-2 is canonically the converse orientation of the adjacent conjugating
swap. -/
theorem isPeifferTransformationFirstKind_iff (π π' : List G) :
    (∃ left right : List G, ∃ a b : G,
      π = left ++ [a, b] ++ right ∧
        π' = left ++ [b, b⁻¹ * a * b] ++ right) ↔
      IsAdjacentConjugatingSwap π' π := by
  constructor
  · rintro ⟨left, right, a, b, hπ, hπ'⟩
    refine ⟨left, right, b, b⁻¹ * a * b, hπ', ?_⟩
    simpa [mul_assoc] using hπ
  · rintro ⟨left, right, a, b, hπ', hπ⟩
    refine ⟨left, right, a * b * a⁻¹, a, hπ, ?_⟩
    simpa [mul_assoc] using hπ'

end List

end

/-! ### Definition_3_10_3 (from Items/Chap03) -/
universe u

set_option autoImplicit false

section

namespace List

variable {G : Type u} [Group G]

/-!
Primary domain: finite list-valued Peiffer rewrites in a group.

Layer triage:
- `source-facing`: the second Peiffer transformation replacing an adjacent pair `(a, b)` by
  `(a * b * a⁻¹, a)`.
- `core/canonical`: `List.IsAdjacentConjugatingSwap` from Definition `3-10-2` is the chapter
  owner relation for this adjacent conjugating rewrite.
- `bridge/view`: the displayed textbook second-kind formula is exactly that owner relation, so the
  file recalls the canonical declaration directly instead of introducing a parallel local
  predicate.

Domain sampling:
1. `List G` is mathlib's owner abstraction for finite ordered sequences.
2. `List.IsAdjacentConjugatingSwap` is the project owner for the adjacent conjugating rewrite.
3. `List.length` is the first owner-side invariant of such a rewrite.
4. `List.prod` is the natural group-valued aggregate invariant of a Peiffer move.

Primitive vs. derived:
- primitive data: the owner relation `IsAdjacentConjugatingSwap` on the two lists;
- derived API: the owner-side invariants `length_eq_of_isAdjacentConjugatingSwap` and
  `prod_eq_of_isAdjacentConjugatingSwap`.
-/

/- Definition 3-10-3: the displayed second-kind Peiffer transformation is the chapter owner
relation `List.IsAdjacentConjugatingSwap`. Its basic invariants are part of that owner API, so
this file recalls the canonical declaration directly. -/
#check IsAdjacentConjugatingSwap
#check length_eq_of_isAdjacentConjugatingSwap
#check prod_eq_of_isAdjacentConjugatingSwap

end List

end

/-! ### Proposition_3_10_4 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: aspherical presentations and identities among relations.

Layer triage:
- `source-facing`: a finite sequence of conjugates of relators and inverse relators whose total
  product is trivial, the elementary Peiffer moves on such sequences, and the equivalence between
  triviality of all such identities and asphericity of the presentation.
- `core/canonical`: `CayleyComplex.Coordinates` and `CayleyComplex.Coordinates.IsAspherical`
  from Definition `3-10-1` are the owner notions for spherical-diagram asphericity,
  `List (FreeGroup X)` is the owner for finite identities among relations, `IsConj` is the
  canonical owner for conjugacy in the free group, and `Relation.ReflTransGen` is the canonical
  owner for finite chains of elementary moves.
- `bridge/view`: Definitions `3-10-2` and `3-10-3` provide the two oriented adjacent conjugating
  rewrites used in a Peiffer move, while a separate local deletion step records cancellation of an
  adjacent inverse pair.

Domain sampling:
1. `CayleyComplex.Coordinates.IsAspherical` is already the chapter owner for the asphericity side
   of the equivalence, so the main theorem should reuse it directly.
2. `List (FreeGroup X)` is the canonical owner for a finite sequence `(p₁, ..., pₙ)` of
   conjugates.
3. `IsConj` from mathlib is the canonical owner for “is a conjugate of”.
4. `Relation.ReflTransGen` is the canonical closure operator for “obtainable by finitely many
   elementary moves”.
5. `List.IsAdjacentConjugatingSwap` is the chapter owner relation for the adjacent conjugating
   rewrite, and Definitions `3-10-2` and `3-10-3` contribute its two orientations
   `List.IsAdjacentConjugatingSwap π' π` and `List.IsAdjacentConjugatingSwap π π'`.

Primitive vs. derived:
- primitive data: a relator set `R`, a list `π : List (FreeGroup X)`, the termwise conjugacy
  condition, and the elementary local rewrite steps on `π`;
- derived API: triviality of an identity via finitely many Peiffer reductions and the main
  equivalence with asphericity.
-/

namespace GroupPresentation

variable {X : Type u}

/-- A term in an identity among relations for `(X; R)` is a conjugate of a relator or of the
inverse of a relator. -/
def IsRelatorConjugate (R : Set (FreeGroup X)) (p : FreeGroup X) : Prop :=
  ∃ r : FreeGroup X, r ∈ R ∧ (IsConj p r ∨ IsConj p r⁻¹)

/-- An identity among relations for `(X; R)` is a finite sequence of conjugates of relators or
inverse relators whose product in the free group is `1`. -/
def IsIdentityAmongRelations (R : Set (FreeGroup X)) (π : List (FreeGroup X)) : Prop :=
  (∀ p ∈ π, IsRelatorConjugate R p) ∧ π.prod = 1

/-- The defining conditions for an identity among relations are termwise relator conjugacy and
trivial total product. -/
-- Proof sketch: unfold `IsIdentityAmongRelations`.
theorem isIdentityAmongRelations_iff (R : Set (FreeGroup X)) (π : List (FreeGroup X)) :
    IsIdentityAmongRelations R π ↔ (∀ p ∈ π, IsRelatorConjugate R p) ∧ π.prod = 1 := sorry

/-- A deletion step cancels one adjacent inverse pair in a sequence. -/
def IsDeletionOfInversePair (π π' : List (FreeGroup X)) : Prop :=
  ∃ left right : List (FreeGroup X), ∃ a : FreeGroup X,
    π = left ++ [a, a⁻¹] ++ right ∧ π' = left ++ right

/-- An elementary Peiffer step is either one of the two oriented adjacent conjugating rewrites
from Definitions `3-10-2` and `3-10-3`, or deletion/insertion of an adjacent inverse pair. -/
def PeifferStep (π π' : List (FreeGroup X)) : Prop :=
  List.IsAdjacentConjugatingSwap π' π ∨
    List.IsAdjacentConjugatingSwap π π' ∨
      IsDeletionOfInversePair π π' ∨ IsDeletionOfInversePair π' π

/-- An identity among relations is trivial when finitely many elementary Peiffer steps transform
it into the empty identity. -/
def IsTrivialIdentityAmongRelations (π : List (FreeGroup X)) : Prop :=
  Relation.ReflTransGen PeifferStep π []

/-- A presentation admits a nontrivial identity among relations when some identity among
relations is not reducible to the empty identity by elementary Peiffer steps. -/
def HasNontrivialIdentityAmongRelations (R : Set (FreeGroup X)) : Prop :=
  ∃ π : List (FreeGroup X),
    IsIdentityAmongRelations R π ∧ ¬ IsTrivialIdentityAmongRelations π

/-- A nontrivial identity among relations is exactly an identity not connected to the empty one by
the Peiffer-step closure. -/
-- Proof sketch: unfold `HasNontrivialIdentityAmongRelations` and
-- `IsTrivialIdentityAmongRelations`.
theorem hasNontrivialIdentityAmongRelations_iff (R : Set (FreeGroup X)) :
    HasNontrivialIdentityAmongRelations R ↔
      ∃ π : List (FreeGroup X),
        IsIdentityAmongRelations R π ∧ ¬ Relation.ReflTransGen PeifferStep π [] := sorry

/-- Proposition 3-10-4: the actual Cayley complex `C(X; R)` is aspherical exactly when the
relator family `R` admits no nontrivial identity among relations. -/
-- Proof sketch: build from any identity among relations the spherical diagram obtained by sewing
-- together the corresponding bouquet of relator discs, and conversely decompose any spherical
-- diagram into such a bouquet. The elementary Peiffer moves are precisely the local modifications
-- that preserve the resulting spherical diagram, and trivial identities are exactly those that
-- reduce to the empty diagram.
theorem isAspherical_iff_no_nontrivial_identities_among_relations
    {R : Set (FreeGroup X)} {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R) :
    CayleyComplex.Coordinates.IsAspherical coords ↔
      ¬ HasNontrivialIdentityAmongRelations R := sorry

end GroupPresentation

/-! ### Corollary_3_10_5 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: aspherical presentations, relation modules, and low-degree group resolutions.

Layer triage:
- `source-facing`: an aspherical presentation `(X; R)` with no relator a proper power, and the
  resulting freeness of the relation module `N / [N, N]`.
- `core/canonical`: `CayleyComplex.Coordinates.IsAspherical` is the chapter owner for
  asphericity, `Subgroup.normalClosure R` is the owner for the relator subgroup `N`,
  `quotientGroupRingRight N` is the owner ring for right `ℤG`-modules, and
  `relationIdealQuotient N` from Proposition `2-3-2` is the owner realization of the relation
  module.
- `bridge/view`: the textbook phrase “the relation module `N / [N, N]` is a free `G`-module” is
  expressed directly by `Module.Free (quotientGroupRingRight N) (relationIdealQuotient N)`.

Domain sampling:
1. `CayleyComplex.Coordinates.IsAspherical` from Definition `3-10-1` is the owner asphericity
   predicate for the chosen actual Cayley complex.
2. `Subgroup.normalClosure R` is the canonical owner for the normal closure `N` of the relators.
3. `relationIdealQuotient N` from Proposition `2-3-2` is the chapter owner for the relation
   module attached to the presentation.
4. `Module.Free` is mathlib's owner predicate for “is a free module”.

Primitive vs. derived:
- primitive data: the relator set `R`, the chosen standard Cayley presentation `P`, and the
  relator-side hypothesis that no element of `R` is a proper power;
- derived API: freeness of the canonical relation-module owner `relationIdealQuotient
  (Subgroup.normalClosure R)`.
-/

namespace GroupPresentation

variable {X : Type u} {R : Set (FreeGroup X)}

local notation "N" => Subgroup.normalClosure R
local notation "S" => quotientGroupRingRight N

/-- Corollary 3-10-5: if `G = (X; R)` is aspherical and no relator is a proper power, then the
relation module is a free `G`-module. -/
-- Proof sketch: in the current chapter API, Proposition `2-3-2` already packages the relation
-- module `relationIdealQuotient N` as one of the free terms in the canonical low-degree Fox
-- resolution over `quotientGroupRingRight N`. This corollary is therefore a direct source-facing
-- specialization of that owner theorem.
theorem relationIdealQuotient_free_of_isAspherical_of_relators_not_properPower
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (_ : CayleyComplex.Coordinates.IsAspherical coords)
    (_ : ∀ r ∈ R, ¬ IsProperPower r) :
    Module.Free S (relationIdealQuotient N) := by
  let hres := relation_ideal_free_resolution N
  rcases hres with ⟨_, _, hfree, _, _⟩
  exact hfree

end GroupPresentation

/-! ### Corollary_3_10_6 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

/-!
Primary domain: aspherical presentations, relation modules, and projective resolutions of the
trivial module.

Layer triage:
- `source-facing`: an aspherical presentation `(X; R)` with no relator a proper power, and the
  conclusion that the presented group has cohomological dimension at most `2`.
- `core/canonical`: `CayleyComplex.Coordinates.IsAspherical` is the owner asphericity predicate,
  `quotientGroupRingTrivialModule (Subgroup.normalClosure R)` is the owner trivial right
  `ℤG`-module, and `CategoryTheory.HasProjectiveDimensionLE` is the owner abstraction for the
  cohomological-dimension bound.
- `bridge/view`: the same textbook phrase can be witnessed by a projective resolution of the
  canonical trivial module whose terms vanish from degree `3` onward.

Domain sampling:
1. `quotientGroupRingTrivialModule N` from Proposition `2-3-2` is the chapter owner for the
   trivial right `ℤG`-module attached to the presentation.
2. `CategoryTheory.HasProjectiveDimensionLE` from mathlib is the owner predicate for “projective
   dimension at most `n`”.
3. `CategoryTheory.projectiveDimension_le_iff` from mathlib is the canonical comparison between
   the owner predicate and the numerical projective dimension.
4. `relation_ideal_free_resolution` from Proposition `2-3-2` and
   `relationIdealQuotient_free_of_isAspherical_of_relators_not_properPower` from Corollary
   `3-10-5` are the low-degree resolution inputs that produce the degree-`≤ 2` bound.

Primitive vs. derived:
- primitive data: the relator set `R`, the chosen standard Cayley presentation `P`, and the
  relator-side hypothesis that no element of `R` is a proper power;
- derived API: the canonical conclusion `HasProjectiveDimensionLE T 2`, with any explicit
  truncated projective resolution demoted to a bridge theorem.
-/

namespace GroupPresentation

variable {X : Type u} {R : Set (FreeGroup X)}

local notation "N" => Subgroup.normalClosure R
local notation "T" => quotientGroupRingTrivialModule N

/-- Corollary 3-10-6: if `G = (X; R)` is aspherical and no relator is a proper power, then the
canonical trivial `ℤG`-module has projective dimension at most `2`. -/
-- Proof sketch: Proposition `2-3-2` gives the standard low-degree free resolution of the trivial
-- module. Corollary `3-10-5` makes the relation module itself free, so the resolution can be
-- truncated after degree `2`, yielding cohomological dimension at most `2`.
theorem hasProjectiveDimensionLE_two_trivialModule_of_isAspherical_of_relators_not_properPower
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (hAspherical : CayleyComplex.Coordinates.IsAspherical coords)
    (hproper : ∀ r ∈ R, ¬ IsProperPower r) :
    HasProjectiveDimensionLE T 2 := by
  sorry

/-- Companion bridge theorem: the projective-dimension bound in Corollary `3-10-6` may be
realized by a projective resolution of the canonical trivial `ℤG`-module with no terms in degrees
`≥ 3`. -/
theorem exists_projectiveResolution_trivialModule_isZero_from_degree_three_of_isAspherical_of_relators_not_properPower
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (hAspherical : CayleyComplex.Coordinates.IsAspherical coords)
    (hproper : ∀ r ∈ R, ¬ IsProperPower r) :
    ∃ Q : ProjectiveResolution T, ∀ n : ℕ, IsZero (Q.complex.X (n + 3)) := by
  sorry

end GroupPresentation

/-! ### Proposition_3_10_7 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

section

variable {X : Type u}

/-!
Primary domain: combinatorial group theory of identities among relations and aspherical
presentations.

Layer triage:
- `source-facing`: the normal closure `N` of the relators of a presentation `(X; R)`, the
  condition `(I.2)` describing a free basis of `N` by conjugates `u * r * u⁻¹`, and the
  asphericity conclusion for the presentation.
- `core/canonical`: `Subgroup.normalClosure` is the owner for the relator subgroup `N`,
  `Subgroup.centralizer {r}` is the owner for the centralizer `C(r)`, `H.LeftTransversal` is the
  mathlib owner for a full left transversal of a subgroup `H`, `FreeGroupBasis` is the canonical
  owner for a chosen free basis, and `CayleyComplex.Coordinates.IsAspherical` is the chapter owner
  for asphericity of a chosen actual Cayley complex.
- `bridge/view`: the source product subgroup `N C(r)` is expressed canonically as the subgroup
  generated by `N` and `C(r)`, namely `N ⊔ Subgroup.centralizer {r}`; the source basis `B` is
  the corresponding subset of the normal closure `N`.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the subgroup generated by the relators.
2. `Subgroup.centralizer {r}` is mathlib's subgroup-valued owner for the centralizer of a relator.
3. `H.LeftTransversal` from `Mathlib/GroupTheory/Complement` is the owner abstraction for a full
   left transversal of `H`.
4. `FreeGroupBasis` is the canonical owner for a chosen free basis of a free group.
5. `CayleyComplex.Coordinates.IsAspherical` from Definition `3-10-1` is the owner conclusion for
   the asphericity of `(X; R)` once an actual Cayley-complex realization has been chosen.

Primitive vs. derived:
- primitive data: the relator set `R` and the family of left transversals attached to the
  subgroups `N ⊔ C(r)`;
- derived API: the corresponding basis subset of `N` and the asphericity conclusion.
-/

/-- The textbook condition `(I.2)` says that the normal closure `N` of the relators has a free
basis consisting of the conjugates `u * r * u⁻¹`, where for each relator `r` the conjugating
elements `u` range over a full left transversal of `N ⊔ C(r)` in the ambient free group. -/
def HasConjugacyTransversalBasis (R : Set (FreeGroup X)) : Prop :=
  let N : Subgroup (FreeGroup X) := Subgroup.normalClosure R
    ∃ U : ∀ r : R,
      (N ⊔ Subgroup.centralizer ({(r : FreeGroup X)} : Set (FreeGroup X))).LeftTransversal,
    ∃ ι : Type v, ∃ basis : FreeGroupBasis ι N,
      Set.range basis = {g : N |
        ∃ r : R, ∃ u : FreeGroup X, u ∈ (U r : Set (FreeGroup X)) ∧
          (g : FreeGroup X) = u * (r : FreeGroup X) * u⁻¹}

/-- Proposition 3-10-7: if condition `(I.2)` holds, so that the normal closure of the relators has
the conjugacy-transversal basis described above, then every actual Cayley complex `C(X; R)` is
aspherical. -/
-- Proof sketch: by Proposition `10.1` it is enough to show that `(I.2)` rules out nontrivial
-- identities among relations. Rewrite each term of a reduced identity among relations in the basis
-- given by `(I.2)`, apply the odd-length cancellation argument to find an adjacent pair with more
-- than half-overlap, and then use a first-kind Peiffer transformation to reduce the total length.
-- Induction on the sum of the lengths of the terms completes the contradiction.
theorem isAspherical_of_hasConjugacyTransversalBasis
    (R : Set (FreeGroup X)) (hI2 : HasConjugacyTransversalBasis R) {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R) :
    CayleyComplex.Coordinates.IsAspherical coords := sorry

end
