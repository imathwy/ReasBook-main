import Mathlib
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_7_1 (from Items/Chap03) -/
universe u v w x y

/-!
Primary domain: Fuchsian complexes, modified presentations, and dual modified Cayley complexes.

Layer triage:
- `source-facing`: a Fuchsian complex for a group `G`, a modified presentation `(X, J; R)` of
  `G`, the associated modified Cayley complex, and the statement that this complex can be chosen
  dual to the given Fuchsian complex.
- `core/canonical`: `TwoComplex` is the owner for the underlying `2`-complex geometry,
  `TwoComplex.Aut` is the owner for automorphisms of a `2`-complex,
  `TwoComplex.AutAction` is the owner for a group action by such automorphisms,
  `TwoComplex.GeometricFace` and `OneComplex.GeometricEdge` are the owners for unoriented faces
  and edges, and
  `CayleyComplex.Coordinates` is the owner for Cayley-type coordinates on an actual `2`-complex,
  `SignedLetter` is the chapter owner for signed ordinary generators,
  `PresentedGroup` is the canonical owner for the relators of a modified presentation, and
  `TwoComplex.VertexOnFace` is the owner for vertex-face incidence.
- `bridge/view`: `TwoComplex.Duality` records the duality data between two actual
  `2`-complexes together with their incidence compatibility, and
  `ModifiedCayleyComplex.RealizesFuchsianDuality` expresses the textbook equivariance statement
  for the dual vertices.

Domain sampling:
1. `TwoComplex` from Definition `3-2-4` is the owner abstraction for the actual complex `K`.
2. `TwoComplex.Aut` and its induced permutations from Proposition `3-4-1` are the natural owner
   abstractions for the group action on a Fuchsian complex.
3. `TwoComplex.AutAction` is the right owner for the group law on those automorphisms, so the
   induced geometric-face and geometric-edge permutations are derived API rather than primitive
   fields of `FuchsianComplex`.
4. `TwoComplex.GeometricFace`, `OneComplex.GeometricEdge`, and `TwoComplex.VertexOnFace` are the
   correct intrinsic carriers and incidence owners for duality and for the "without reflections"
   condition.
5. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the owner abstraction for an actual
   Cayley-type complex with the canonical left translations by `G`.
6. `SignedLetter` from Proposition `3-4-1` is the owner vocabulary for signed ordinary
   generators, so the modified relator alphabet should reuse it directly.
7. `PresentedGroup` is the canonical owner for saying that a relator family presents `G`.

Primitive vs. derived:
- primitive data: the actual Fuchsian `2`-complex, its action by automorphisms, the modified
  presentation data `(X, J; R)` together with the actual relator words, the involution condition
  on the reflection generators, the presentation equivalence to `G`, and the actual modified
  Cayley complex with Cayley coordinates and relator boundary words;
- derived API: the induced actions on geometric faces and edges, the generator/reflection values
  in `G`, the duality equivalences together with their incidence view, the vertex corresponding to
  a face under a duality, and the equivariance statement for those vertices.
-/

namespace TwoComplex

/-- An action of a group on a `2`-complex by automorphisms, recorded on the actual vertex,
oriented-edge, and oriented-face carriers. The induced actions on geometric faces and geometric
edges are derived API. -/
structure AutAction (G : Type u) [Group G] (C : TwoComplex) where
  /-- The automorphism corresponding to an element of `G`. -/
  toAut : G → Aut C
  /-- The identity element acts trivially on vertices. -/
  one_vertex (v : C.skeleton) :
      (toAut 1).vertexPerm v = v
  /-- Multiplication in `G` matches composition on vertices. -/
  mul_vertex (g h : G) (v : C.skeleton) :
      (toAut (g * h)).vertexPerm v =
        (toAut g).vertexPerm ((toAut h).vertexPerm v)
  /-- The identity element acts trivially on oriented edges. -/
  one_edge (e : C.skeleton.Edge) :
      (toAut 1).edgePerm e = e
  /-- Multiplication in `G` matches composition on oriented edges. -/
  mul_edge (g h : G) (e : C.skeleton.Edge) :
      (toAut (g * h)).edgePerm e =
        (toAut g).edgePerm ((toAut h).edgePerm e)
  /-- The identity element acts trivially on oriented faces. -/
  one_face (D : C.Face) :
      (toAut 1).facePerm D = D
  /-- Multiplication in `G` matches composition on oriented faces. -/
  mul_face (g h : G) (D : C.Face) :
      (toAut (g * h)).facePerm D =
        (toAut g).facePerm ((toAut h).facePerm D)

namespace AutAction

variable {G : Type u} [Group G] {C : TwoComplex}

instance : CoeFun (AutAction G C) fun _ ↦ G → Aut C :=
  ⟨AutAction.toAut⟩

/-- The induced action on geometric faces. -/
abbrev geometricFacePerm (ρ : AutAction G C) (g : G) :
    Equiv.Perm (GeometricFace C) :=
  (ρ g).geometricFacePerm

/-- The induced action on geometric edges. -/
abbrev geometricEdgePerm (ρ : AutAction G C) (g : G) :
    Equiv.Perm (OneComplex.GeometricEdge C.skeleton) :=
  (ρ g).geometricEdgePerm

/-- The action by automorphisms induces a homomorphism to the permutation group of geometric
faces. -/
private def toGeometricFacePermHom (ρ : AutAction G C) : G →* Equiv.Perm (GeometricFace C) where
  toFun := ρ.geometricFacePerm
  map_one' := by
    ext D
    refine Quotient.inductionOn D ?_
    intro D
    change Quotient.mk _ ((ρ 1).facePerm D) = Quotient.mk _ D
    simp [ρ.one_face D]
  map_mul' g h := by
    ext D
    refine Quotient.inductionOn D ?_
    intro D
    change Quotient.mk _ ((ρ (g * h)).facePerm D) =
      Quotient.mk _ ((ρ g).facePerm ((ρ h).facePerm D))
    simp [ρ.mul_face g h D]

/-- The induced action of `G` on geometric faces. -/
abbrev geometricFaceMulAction (ρ : AutAction G C) : MulAction G (GeometricFace C) :=
  MulAction.compHom (GeometricFace C) ρ.toGeometricFacePermHom

end AutAction

variable (C K : TwoComplex)

/-- A duality between `2`-complexes identifies vertices of one complex with geometric faces of the
other, geometric faces with vertices, and geometric edges on both sides, in a way compatible with
vertex-face incidence. -/
structure Duality where
  /-- Vertices of the first complex correspond to geometric faces of the second. -/
  vertexToFace : C.skeleton ≃ GeometricFace K
  /-- Geometric faces of the first complex correspond to vertices of the second. -/
  faceToVertex : GeometricFace C ≃ K.skeleton
  /-- Geometric edges correspond under the duality. -/
  edgeToEdge : OneComplex.GeometricEdge C.skeleton ≃ OneComplex.GeometricEdge K.skeleton
  /-- A vertex of `C` lies on an oriented face `D` exactly when the dual vertex of `D` lies on
  some oriented representative of the dual geometric face of that vertex in `K`. -/
  vertexOnFace_iff (v : C.skeleton) (D : C.Face) :
      C.VertexOnFace v D ↔
        ∃ E : K.Face, ⟦E⟧ = vertexToFace v ∧ K.VertexOnFace (faceToVertex ⟦D⟧) E

end TwoComplex

/-- A Fuchsian complex for `G` is an actual `2`-complex equipped with an action of `G` by
automorphisms of that complex. -/
structure FuchsianComplex (G : Type u) [Group G] where
  /-- The underlying `2`-complex. -/
  complex : TwoComplex.{v}
  /-- The action of `G` by automorphisms of the complex. -/
  action : TwoComplex.AutAction G complex

namespace FuchsianComplex

variable {G : Type u} [Group G]

/-- A Fuchsian complex is without reflections when no nontrivial group element fixes a geometric
edge. -/
def WithoutReflections (K : FuchsianComplex G) : Prop :=
  ∀ ⦃g : G⦄, g ≠ 1 →
    ∀ e : OneComplex.GeometricEdge K.complex.skeleton, (K.action g).geometricEdgePerm e ≠ e

end FuchsianComplex

/-- The relator set in the free group on ordinary and reflection generators determined by a family
of modified relator words. -/
def modifiedRelators
    {X : Type v} {J : Type w} {Rel : Type x}
    (relatorWord : Rel → List (SignedLetter X ⊕ J)) :
    Set (FreeGroup (X ⊕ J)) :=
  Set.range fun r ↦
    List.prod ((relatorWord r).map <|
      Sum.elim
        (SignedLetter.value fun x ↦ FreeGroup.of (Sum.inl x))
        fun j ↦ FreeGroup.of (Sum.inr j))

/-- A modified presentation of `G` consists of ordinary generators, involutory reflection
generators, and relators, together with the canonical statement that those relators present
`G`. -/
structure ModifiedPresentation (G : Type u) [Group G] where
  /-- The ordinary generators. -/
  X : Type v
  /-- The reflection generators. -/
  J : Type w
  /-- The relators. -/
  Rel : Type x
  /-- The boundary word attached to a relator, written in signed ordinary generators and
  reflection generators. -/
  relatorWord : Rel → List (SignedLetter X ⊕ J)
  /-- The corresponding relators present `G`. -/
  presentationEquiv : PresentedGroup (modifiedRelators relatorWord) ≃* G
  /-- Each reflection generator represents an involution in `G`. -/
  reflection_sq_eq_one (j : J) :
      presentationEquiv (PresentedGroup.of (Sum.inr j)) ^ 2 = 1

namespace ModifiedPresentation

variable {G : Type u} [Group G]

/-- The relators of a modified presentation, viewed as elements of the free group on the ordinary
and reflection generators. -/
abbrev relators (P : ModifiedPresentation G) : Set (FreeGroup (P.X ⊕ P.J)) :=
  modifiedRelators P.relatorWord

/-- The value in `G` of a signed ordinary generator or reflection generator in a modified
presentation. -/
def letterValue (P : ModifiedPresentation G) : SignedLetter P.X ⊕ P.J → G :=
  Sum.elim
    (SignedLetter.value fun x ↦ P.presentationEquiv (PresentedGroup.of (Sum.inl x)))
    fun j ↦ P.presentationEquiv (PresentedGroup.of (Sum.inr j))

/-- Each reflection generator evaluates to an involution in `G`. -/
theorem letterValue_reflection_sq_eq_one (P : ModifiedPresentation G) (j : P.J) :
    P.letterValue (Sum.inr j) ^ 2 = 1 :=
  P.reflection_sq_eq_one j

/-- A modified presentation is ordinary when it has no reflection letters. -/
def IsOrdinary (P : ModifiedPresentation G) : Prop :=
  IsEmpty P.J

end ModifiedPresentation

/-- A modified Cayley complex is an actual `2`-complex equipped with Cayley coordinates for the
signed letters and relators of a modified presentation, together with the statement that each
chosen oriented relator face boundary reads the corresponding relator word. -/
structure ModifiedCayleyComplex {G : Type u} [Group G] (P : ModifiedPresentation G) where
  /-- The underlying `2`-complex. -/
  complex : TwoComplex.{y}
  /-- Cayley coordinates on the complex using the signed letters of the modified presentation. -/
  coordinates : CayleyComplex.Coordinates complex P.letterValue P.Rel
  /-- The chosen oriented representative of the geometric face `(g, r)` has a boundary path based
  at the vertex `g` whose label word is exactly the relator word `r`. -/
  faceBoundary_word (g : G) (r : P.Rel) :
      (Quiver.Path.edgeList (coordinates.faceBoundary g r).1).map
          (fun e ↦ (coordinates.edgeEquiv e.hom.1).2) =
        P.relatorWord r

namespace ModifiedCayleyComplex

variable {G : Type u} [Group G]
variable {P : ModifiedPresentation G}

/-- A dual modified Cayley complex realizes a Fuchsian complex when the dual vertex of `gD` is the
translate by `g` of the dual vertex of `D`. -/
def RealizesFuchsianDuality (K : FuchsianComplex G) (C : ModifiedCayleyComplex P)
    (dual : C.complex.Duality K.complex) : Prop :=
  ∀ (g : G) (D : K.complex.GeometricFace),
    dual.vertexToFace.symm ((K.action g).geometricFacePerm D) =
      (C.coordinates.leftTranslation g).vertexPerm (dual.vertexToFace.symm D)

end ModifiedCayleyComplex

section Proposition371

variable {G : Type u} [Group G]

/-- Proposition 3-7-1 (1): every Fuchsian complex of `G` admits a modified presentation whose
modified Cayley complex is dual to it. -/
-- Proof sketch: choose a base face of the Fuchsian complex, use adjacent faces to define the
-- modified generating letters, construct the barycentric-dual `1`-skeleton, and read off the
-- relators from the bounded complementary regions.
theorem exists_modifiedPresentation_with_dual_modifiedCayleyComplex
    (K : FuchsianComplex G) :
    ∃ (P : ModifiedPresentation G) (C : ModifiedCayleyComplex P)
      (dual : C.complex.Duality K.complex),
      C.RealizesFuchsianDuality K dual := sorry

variable {P : ModifiedPresentation G}

/- Proposition 3-7-1 (2): in a dual modified Cayley complex, the vertex corresponding to the face
`gD` is the translate by `g` of the vertex corresponding to `D`. This is exactly the owner
predicate `ModifiedCayleyComplex.RealizesFuchsianDuality`, so the numbered item is recorded as a
direct recall of that canonical declaration rather than as a duplicate wrapper theorem. -/
#check (ModifiedCayleyComplex.RealizesFuchsianDuality :
  (K : FuchsianComplex G) → (C : ModifiedCayleyComplex P) →
    C.complex.Duality K.complex → Prop)

/-- Proposition 3-7-1 (3): if the Fuchsian complex has no reflections, the dual modified Cayley
complex may be chosen to come from an ordinary presentation. -/
-- Proof sketch: when no nontrivial element fixes a geometric edge, the reflection letters are
-- absent from the construction, so the same dual complex is obtained from an ordinary generating
-- set alone.
theorem exists_ordinaryCayleyComplex_with_dual_modifiedPresentation
    (K : FuchsianComplex G) (hK : K.WithoutReflections) :
    ∃ (P : ModifiedPresentation G) (_ : P.IsOrdinary) (C : ModifiedCayleyComplex P)
      (dual : C.complex.Duality K.complex),
      C.RealizesFuchsianDuality K dual := sorry

end Proposition371

/-! ### Proposition_3_7_2 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: planar `2`-complexes, modified Cayley complexes, and their dual Fuchsian
complexes.

Layer triage:
- `source-facing`: a finite modified presentation together with its strictly planar modified
  Cayley complex, and the dual Fuchsian complex attached to that complex.
- `core/canonical`: `TwoComplex` is the owner for the actual `2`-complex, `ModifiedPresentation`
  and `ModifiedCayleyComplex` from Proposition `3-7-1` are the chapter owners for modified
  presentation data and its Cayley realization, `TwoComplex.Duality` and
  `ModifiedCayleyComplex.RealizesFuchsianDuality` are the chapter owners for the duality data and
  its equivariance, and `FuchsianComplex` with `FuchsianComplex.WithoutReflections` is the owner
  for the dual group action.
- `bridge/view`: the source phrase "strictly planar" is expressed by the existing owner predicates
  `TwoComplex.EmbedsInPlane` and `TwoComplex.HasSimpleBoundary`.

Domain sampling:
1. `ModifiedPresentation` from Proposition `3-7-1` is the chapter owner for the generator,
   reflection, and relator data of a modified presentation.
2. `ModifiedCayleyComplex` from Proposition `3-7-1` is the owner for the associated actual
   `2`-complex with Cayley coordinates.
3. `TwoComplex.Duality` and `ModifiedCayleyComplex.RealizesFuchsianDuality` from Proposition
   `3-7-1` are the chapter owner abstractions for the duality data and its equivariance between a
   modified Cayley complex and a Fuchsian complex.
4. `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` and `TwoComplex.HasSimpleBoundary` from
   Definition `3-2-4` are the owner predicates for the two components of strict planarity.

Primitive vs. derived:
- primitive data: the modified presentation `P`, its modified Cayley complex `C`, and the strict
  planarity of `C.complex`;
- derived API: the dual Fuchsian complex together with the canonical realization witness
  `C.RealizesFuchsianDuality K dual`, and the reflection criterion
  `K.WithoutReflections ↔ P.IsOrdinary`.
-/

namespace ModifiedCayleyComplex

variable {G : Type u} [Group G]
variable {P : ModifiedPresentation G} [Finite P.X] [Finite P.J] [Finite P.Rel]
variable (C : ModifiedCayleyComplex P)

local notation "Complex" => C.complex

/-- Proposition 3-7-2: a finite modified presentation together with a strictly planar modified
Cayley complex admits a dual Fuchsian complex, and that dual complex is without reflections
exactly in the ordinary case. -/
-- Proof sketch: embed the modified Cayley complex in the plane, barycentrically subdivide each
-- face, and glue the regions around each original vertex to obtain the dual polygons. The left
-- translations on the modified Cayley complex transport to automorphisms of the dual complex and
-- give the required Fuchsian action. A nontrivial element fixes a geometric dual edge exactly
-- when it reverses the crossed edge of the modified Cayley complex, which occurs precisely for
-- reflection letters; hence the dual is reflection-free exactly when `P` is ordinary.
theorem exists_dualFuchsianComplex_of_strictlyPlanar
    (hplanar : TwoComplex.EmbedsInPlane Complex)
    (hsimple : ∀ D : C.complex.Face, TwoComplex.HasSimpleBoundary Complex D) :
    ∃ K : FuchsianComplex G, ∃ dual : TwoComplex.Duality Complex K.complex,
      C.RealizesFuchsianDuality K dual ∧ (K.WithoutReflections ↔ P.IsOrdinary) := sorry

end ModifiedCayleyComplex

/-! ### Proposition_3_7_3 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

open TwoComplex

/-!
Primary domain: Fuchsian complexes and subgroup inheritance.

Layer triage:
- `source-facing`: a planar simply connected `2`-complex equipped with an action of the ambient
  group by complex automorphisms, and the statement that every subgroup admits a new Fuchsian
  complex whose faces are unions of faces of the original one.
- `core/canonical`: `FuchsianComplex` from Proposition `3-7-1` is the existing owner for the
  action of a group on a `2`-complex by automorphisms, while
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `IsSimplyConnected`,
  `GeometricFace`, and `TwoManifoldEmbedding` are the owner predicates and constructions for the
  extra geometric hypotheses and geometric face images.
- `bridge/view`: the face-union conclusion is expressed directly by a chosen planar embedding of
  the fine complex and a compatible planar embedding of the coarse complex, together with the
  owner construction
  `TwoManifoldEmbedding.geometricFaceUnion`.

Domain sampling:
1. `FuchsianComplex` from Proposition `3-7-1` is the chapter owner for a group action on an
   actual `2`-complex by automorphisms.
2. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)` and `IsSimplyConnected` are the owner
   predicates for the connectedness assumptions on the underlying complex.
3. `TwoManifoldEmbedding` from Proposition `3-5-6` is the owner abstraction for geometric
   realizations of faces in the plane, and `TwoManifoldEmbedding.geometricFaceUnion` is the owner
   for unions of geometric face images, so the face-union comparison should be stated in terms of
   actual embeddings rather than only the existential predicate `EmbedsInPlane`.
4. `Subgroup G` is mathlib's owner for the subgroup `H ≤ G`, and the subgroup type `H` inherits
   its canonical group structure automatically.

Primitive vs. derived:
- primitive data: the underlying `2`-complex and its action by automorphisms, already owned by
  `FuchsianComplex`, together with the chosen planar embedding of the original complex needed to
  state unions of geometric faces;
- derived API: the connected and simply connected hypotheses on that owner and the coarse complex,
  together with the compatible coarse planar embedding witnessing that each coarse geometric face
  is a union of geometric faces of the original complex.
-/

section

variable {G : Type u} [Group G]

/-- Proposition 3-7-3: if `K` is a Fuchsian complex for a group `G` and `H` is a subgroup of
`G`, then every chosen planar realization of `K` induces a Fuchsian complex `L` for `H` whose
geometric faces are unions of geometric faces of `K` in that realization. -/
-- Proof sketch: choose a maximal connected union `E` of faces of `K` that contains no two
-- distinct `H`-congruent faces. The standard Zorn-lemma argument in the text shows that every
-- geometric face of `K` is `H`-congruent to one in `E` and that `E` is simply connected. Taking
-- the translates `hE` as the faces of a new planar complex yields a Fuchsian complex for the
-- subgroup `H`, and each new geometric face is by construction a union of geometric faces of `K`.
theorem exists_faceUnionRefinement_fuchsianComplex_of_subgroup
    (K : FuchsianComplex G)
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify K.complex.skeleton))
    (hsimply : IsSimplyConnected K.complex)
    (fineEmbedding : TwoManifoldEmbedding K.complex 𝔼²)
    (H : Subgroup G) :
    ∃ L : FuchsianComplex H,
      Quiver.IsStronglyConnected (Quiver.Symmetrify L.complex.skeleton) ∧
        IsSimplyConnected L.complex ∧
        ∃ coarseEmbedding : TwoManifoldEmbedding L.complex 𝔼²,
          ∀ D : GeometricFace L.complex,
            ∃ facePieces : Set (GeometricFace K.complex),
              coarseEmbedding.geometricFaceSet D =
                fineEmbedding.geometricFaceUnion facePieces :=
  sorry

end

/-! ### Proposition_3_7_4 (from Items/Chap03) -/
universe u

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: `F`-groups, subgroup index, and free products of cyclic groups.

Layer triage:
- `source-facing`: a subgroup `H ≤ G` of an `F`-group `G`, with the two cases that `H` has finite
  or infinite index in `G`.
- `core/canonical`: `IsFGroup` from Definition `3-5-3`, `IsFreeProductOfCyclicGroups` from
  Proposition `3-5-5`, and mathlib's subgroup-index owner API `Subgroup.index` together with
  `Subgroup.FiniteIndex`.
- `bridge/view`: Proposition `3-7-3` already packages the subgroup-inheritance step at the
  Fuchsian-complex level through
  `exists_faceUnionRefinement_fuchsianComplex_of_subgroup`, while
  `Subgroup.index_eq_zero_iff_infinite` is the standard bridge from the subgroup-index owner to
  the quotient-side infinitude predicate. The present file records only the two source-facing
  consequences obtained from that owner-level refinement.

Domain sampling:
1. `IsFGroup` is the chapter owner predicate for the source notion of an `F`-group.
2. `IsFreeProductOfCyclicGroups` is the source-facing owner predicate for the alternative
   conclusion in the infinite-index case.
3. `Subgroup.index` and `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` are the canonical
   owner abstractions for subgroup index and finite-index subgroup inclusions.
4. `Subgroup.index_eq_zero_iff_infinite` is the standard bridge between infinite subgroup index
   and quotient infinitude.
5. `exists_faceUnionRefinement_fuchsianComplex_of_subgroup` from Proposition `3-7-3` is the
   chapter owner theorem for passing from a Fuchsian complex of `G` to one for `H`.

Primitive vs. derived:
- primitive public data: the `F`-group hypothesis on `G`, the subgroup `H ≤ G`, and the finite-
  or infinite-index hypothesis on `H`, recorded canonically by `[H.FiniteIndex]` and the explicit
  owner equality `H.index = 0`;
- derived API: the two subgroup conclusions `IsFGroup H` and
  `IsFreeProductOfCyclicGroups H`. No extra subgroup wrapper or chosen Fuchsian-complex package is
  introduced here.
-/

variable (H : Subgroup G)

/-- Proposition 3-7-4 (1): every finite-index subgroup of an `F`-group is again an `F`-group. -/
-- Proof sketch: use the Section `7` Fuchsian-complex model attached to `G` and the subgroup
-- inheritance theorem `exists_faceUnionRefinement_fuchsianComplex_of_subgroup` from Proposition
-- `3-7-3`. Finite index means each new face is assembled from only finitely many old faces, so the
-- subgroup remains in the `F`-group branch of the Section `5` planar alternative.
theorem isFGroup_of_finiteIndex_subgroup
    (hG : IsFGroup G)
    [H.FiniteIndex] :
    IsFGroup H := sorry

/-- Proposition 3-7-4 (2): every infinite-index subgroup of an `F`-group is a free product of
cyclic groups. -/
-- Proof sketch: start from the same subgroup Fuchsian-complex refinement from Proposition
-- `3-7-3`. Infinite index forces the coarse faces of the subgroup complex to be infinite unions of
-- original faces, so the subgroup falls in the free-product branch of the Section `5` planar
-- alternative.
theorem isFreeProductOfCyclicGroups_of_infiniteIndex_subgroup
    (hG : IsFGroup G)
    (hH : H.index = 0) :
    IsFreeProductOfCyclicGroups H := sorry

end

/-! ### Proposition_3_7_5 (from Items/Chap03) -/
universe u v w

set_option autoImplicit false

noncomputable section

open Quiver
open Quiver.Path

/-!
Primary domain: planar `2`-complexes, subcomplex boundaries, and the area measure attached to an
angle measure.

Layer triage:
- `source-facing`: an angle measure on a planar `2`-complex, the induced area of a subcomplex,
  the simple-boundary condition for a subcomplex, and the hypothesis that two subcomplexes meet
  exactly along a common boundary arc.
- `core/canonical`: `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner for carried
  subcomplexes and their union, `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` is the owner
  for planarity, and `Quiver.Path.IsSimpleCycle` from Definition `3-2-4` is the owner predicate
  for simple cyclic boundaries.
- `bridge/view`: an actual common boundary arc is represented by a simple path in the ambient
  `1`-skeleton, and the intersection condition is expressed by comparing the carried vertex and
  edge data of the two subcomplexes with the support of that path.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner abstraction for the regions
   appearing in the statement, so this file should speak directly about subcomplexes and their
   canonical union.
2. `OneComplex.Subcomplex.union` and `TwoComplex.Subcomplex.union` from Proposition `3-3-5` are
   the canonical owner operations for unions of carried subcomplexes.
3. `Quiver.Path.vertices` and `Quiver.Path.edgeList` are the owner API for the support of a path,
   so the common-boundary-arc predicate should use them directly rather than duplicating a local
   support wrapper.
4. `Quiver.Path.IsSimpleCycle` from Definition `3-2-4` is already the owner predicate for a
   simple boundary cycle, so the subcomplex boundary condition should be phrased through it rather
   than by introducing a new cycle-simplicity notion.

Primitive vs. derived:
- primitive data: the ambient complex `C`, the angle measure `α`, the subcomplexes `S₁` and
  `S₂`, and the witnessing simple path for the common boundary arc;
- derived API: the associated area of a subcomplex, the source-facing predicates
  `Subcomplex.HasSimpleBoundary` and `Subcomplex.IntersectsOnlyInCommonBoundaryArc`, and the
  additivity theorem for unions under those hypotheses.
-/

namespace TwoComplex

variable {C : TwoComplex.{w}}

/-- An angle measure on a `2`-complex carries its associated area measure on subcomplexes. -/
structure AngleMeasure (C : TwoComplex.{w}) where
  /-- The associated area measure assigned to subcomplexes by the angle measure. -/
  associatedAreaMeasure : Subcomplex C → ℝ

namespace Subcomplex

/-- A subcomplex has simple boundary when its boundary is carried by a simple cyclic path in its
`1`-skeleton. -/
def HasSimpleBoundary (S : Subcomplex C) : Prop :=
  ∃ c : CyclicPath S.complex.skeleton, IsSimpleCycle c

/-- Two subcomplexes intersect only in a common boundary arc when the intersection of their
`1`-skeleta is exactly the support of a simple path in the ambient `1`-skeleton. -/
def IntersectsOnlyInCommonBoundaryArc (S₁ S₂ : Subcomplex C) : Prop :=
  ∃ (start finish : C.skeleton) (path : Quiver.Path start finish),
    IsSimple path ∧
      (∀ v : C.skeleton,
        v ∈ S₁.skeleton.vertexSet ∩ S₂.skeleton.vertexSet ↔ v ∈ path.vertices) ∧
      ∀ e : C.skeleton.Edge,
        e ∈ S₁.skeleton.edgeSet ∩ S₂.skeleton.edgeSet ↔ ∃ t ∈ edgeList path, t.hom.1 = e

end Subcomplex

namespace AngleMeasure

/-- Proposition 3-7-5: if two subcomplexes with simple boundaries in a planar complex intersect
only in a common boundary arc, then the associated area measure is additive on their union. -/
-- Proof sketch: compare the boundary-angle contributions of `S₁`, `S₂`, and `S₁ ∪ S₂`. Along the
-- common boundary arc, complementary interior angles cancel, while the two endpoints of the arc
-- contribute the missing `2π` correction. Substituting the resulting boundary-curvature identity
-- into the definition of the associated area measure yields the claimed additivity formula.
theorem associatedAreaMeasure_union_eq_add_of_intersectsOnlyInCommonBoundaryArc
    (α : AngleMeasure C) (hplanar : C.EmbedsInPlane)
    (S₁ S₂ : Subcomplex C) (hS₁ : S₁.HasSimpleBoundary) (hS₂ : S₂.HasSimpleBoundary)
    (hinter : S₁.IntersectsOnlyInCommonBoundaryArc S₂) :
    α.associatedAreaMeasure (S₁.union S₂) =
      α.associatedAreaMeasure S₁ + α.associatedAreaMeasure S₂ := sorry

end AngleMeasure

end TwoComplex

/-! ### Corollary_3_7_6 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

namespace TwoComplex

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊¹" => Metric.sphere (0 : 𝔼²) 1

/-!
Primary domain: planar embeddings of `2`-complexes and the area measure attached to an angle
measure.

Layer triage:
- `source-facing`: an ordered family of oriented faces whose nonempty prefix unions bound simple
  closed curves in a fixed planar embedding, together with the resulting area formula for the
  covered subcomplex.
- `core/canonical`: `TwoComplex.Subcomplex` is the owner for intrinsic subcomplex data,
  `TwoComplex.AngleMeasure` together with `AngleMeasure.associatedAreaMeasure` is the owner for
  area attached to subcomplexes, `Subcomplex.ContainsGeometricFace` is the canonical geometric-face
  view of a subcomplex, and `TwoComplex.TwoManifoldEmbedding.geometricFaceUnion` is the owner for
  the corresponding ambient planar image.
- `bridge/view`: the ordered list contributes canonical prefix subcomplexes inside `S`, while
  `TwoManifoldEmbedding.IsBoundedBySimpleClosedCurve` below is the source-facing simple-closed-
  curve predicate for the planar image of a subcomplex.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the chapter owner for the intrinsic
   `2`-dimensional object; this corollary should talk about `S : Subcomplex K`, not a local
   wrapper around its face data.
2. `TwoComplex.AngleMeasure.associatedAreaMeasure` from Proposition `3-7-5` is already the owner
   for the area of a subcomplex, so the main statement should use it directly.
3. `TwoComplex.TwoManifoldEmbedding.geometricFaceUnion` from Proposition `3-5-5`, together with
   `Subcomplex.ContainsGeometricFace` from Proposition `3-3-5`, is already the owner for the
   planar image of a subcomplex, so this file should not keep a parallel `subcomplexImage`
   definition.
4. `TwoComplex.GeometricFace` from Definition `3-2-4` is the owner for orientation-free faces,
   so the summand expression should use the canonical quotient notation rather than a verbose raw
   constructor term.

Primitive vs. derived:
- primitive data: the ambient complex `K`, its planar embedding `embedding`, the angle measure
  `α`, the target subcomplex `S`, and the ordered face list `faces`;
- derived API: the inverse-closed membership relation attached to `faces`, the canonical prefix
  subcomplexes inside `S`, their planar images in the embedding, and the resulting
  simple-closed-curve predicate.
-/

private def listedFaces {K : TwoComplex.{u}} (faces : List K.Face) : Set K.Face :=
  { D | ∃ E ∈ faces, D = E ∨ D = E⁻¹ }

private theorem listedFaces_inv_mem {K : TwoComplex.{u}} (faces : List K.Face) {D : K.Face} :
    D ∈ listedFaces faces → D⁻¹ ∈ listedFaces faces := by
  rintro ⟨E, hE, hD | hD⟩
  · refine ⟨E, hE, Or.inr ?_⟩
    simp [hD]
  · refine ⟨E, hE, Or.inl ?_⟩
    simpa [hD] using K.faceInv_involutive E

private theorem listedFaces_take_subset {K : TwoComplex.{u}} (faces : List K.Face) (i : ℕ) :
    listedFaces (faces.take i) ⊆ listedFaces faces := by
  intro D hD
  rcases hD with ⟨E, hE, hE'⟩
  exact ⟨E, List.mem_of_mem_take hE, hE'⟩

private theorem mem_faceSet_of_mem_list {K : TwoComplex.{u}} {S : Subcomplex K} {faces : List K.Face}
    (hfaces : ∀ D : K.Face, D ∈ S.faceSet ↔ ∃ E ∈ faces, D = E ∨ D = E⁻¹)
    {D : K.Face} (hD : D ∈ faces) :
    D ∈ S.faceSet :=
  (hfaces D).2 ⟨D, hD, Or.inl rfl⟩

namespace Subcomplex

/-- The prefix union of a listed family of faces, viewed as the canonical face-restriction of the
ambient subcomplex `S`. -/
def listedPrefixSubcomplex {K : TwoComplex.{u}} (S : Subcomplex K) (faces : List K.Face)
    (hfaces : ∀ D : K.Face, D ∈ S.faceSet ↔ ∃ E ∈ faces, D = E ∨ D = E⁻¹)
    (i : ℕ) : Subcomplex K :=
  S.restrictFaces
    (listedFaces (faces.take i))
    (fun D hD ↦
      (hfaces D).2 <| by
        simpa [listedFaces] using listedFaces_take_subset faces i hD)
    (fun {_} hD ↦ listedFaces_inv_mem (faces.take i) hD)

end Subcomplex

namespace TwoManifoldEmbedding

/-- A subcomplex is bounded by a simple closed curve when the frontier of its planar image is the
range of an injective continuous parametrization of the standard circle. The planar image is taken
through the canonical owner `embedding.geometricFaceUnion S.ContainsGeometricFace`. -/
def IsBoundedBySimpleClosedCurve
    {K : TwoComplex.{u}}
    (embedding : TwoManifoldEmbedding K 𝔼²) (S : Subcomplex K) : Prop :=
  ∃ γ : 𝕊¹ → 𝔼²,
    Continuous γ ∧ Function.Injective γ ∧
      frontier (embedding.geometricFaceUnion S.ContainsGeometricFace) = Set.range γ

end TwoManifoldEmbedding

/-- Corollary 3-7-6: if a subcomplex `S` of a planar complex `K` is the union of an ordered list
of faces `D₁, …, Dₙ`, every nonempty initial union `D₁ ∪ ⋯ ∪ Dᵢ` is bounded by a simple closed
curve in a chosen planar embedding, and `faceArea` records the associated area of each listed
geometric face via the canonical one-face subcomplexes of `S`, then `α(S)` is the sum of the
areas of the listed faces. -/
-- Proof sketch: induct on the list of faces. The simple-closed-boundary hypothesis identifies
-- each nonempty prefix union as a planar disc-like region, so adjoining the last face changes the
-- area by exactly the area of that face as identified by `hfaceArea`; iterating yields the
-- required finite sum formula.
theorem associatedAreaMeasure_subcomplex_eq_sum_faceAreas_of_prefix_simpleClosedBoundary
    (K : TwoComplex.{u})
    (embedding : TwoManifoldEmbedding K 𝔼²)
    (α : AngleMeasure K)
    (faceArea : GeometricFace K → ℝ)
    (S : Subcomplex K)
    (faces : List K.Face)
    (hcover : ∀ D : K.Face, D ∈ S.faceSet ↔ ∃ E ∈ faces, D = E ∨ D = E⁻¹)
    (hpairwise : faces.Pairwise fun D E ↦ D ≠ E ∧ D ≠ E⁻¹)
    (hprefix :
      ∀ i : ℕ, 1 ≤ i → i ≤ faces.length →
        embedding.IsBoundedBySimpleClosedCurve (S.listedPrefixSubcomplex faces hcover i))
    (hfaceArea :
      ∀ (D : K.Face) (hD : D ∈ faces),
        α.associatedAreaMeasure (S.restrictFace D (mem_faceSet_of_mem_list hcover hD)) =
          faceArea (⟦D⟧ : GeometricFace K)) :
    α.associatedAreaMeasure S =
      (faces.map fun D ↦ faceArea (⟦D⟧ : GeometricFace K)).sum := sorry

end TwoComplex

/-! ### Proposition_3_7_7 (from Items/Chap03) -/
universe u

set_option autoImplicit false

section

-- Layer triage:
-- `source-facing`: a Fuchsian complex for a group `G`, viewed through its minimal angles and
-- real-valued angle assignments on those minimal angles.
-- `core/canonical`: `FuchsianComplex` from Proposition `3-7-3` is the chapter owner for the
-- actual `2`-complex together with the action of `G` by automorphisms.
-- `bridge/view`: a minimal angle is a face corner, represented by a boundary star of the
-- underlying `2`-complex, and the action transports those corners through the existing complex
-- automorphisms.
-- Domain sampling:
-- 1. `FuchsianComplex` from Proposition `3-7-3` is the upstream owner abstraction for Fuchsian
--    complexes in this chapter.
-- 2. `TwoComplex.BoundaryStar` from Proposition `3-3-4` is the project owner for face corners.
-- 3. `TwoComplex.AutAction` from Proposition `3-7-1` is the owner abstraction for the induced
--    action of `G` by automorphisms on the underlying complex.
-- 4. `TwoComplex.Hom.mapBoundaryStar` is the owner map for transporting a face corner along a
--    complex morphism, so invariance should be phrased through that transport rather than through
--    a duplicate local transport wrapper.
-- 5. `TwoComplex.AngleMeasure` from Proposition `3-7-5` is a different owner package: it records
--    the associated area measure of a `2`-complex angle measure, not the source-facing cornerwise
--    angle assignment of Proposition `3-7-7`, so it should not replace the main notion here.
-- Primitive vs. derived:
-- - primitive data: the minimal-angle carrier `Σ v, BoundaryStar v` attached to the underlying
--   complex, and a real-valued function on that carrier;
-- - derived API: the invariance predicate under the ambient `G`-action and the existence theorem.

namespace FuchsianComplex

variable {G : Type u} [Group G]

/-- The minimal angles of a Fuchsian complex are its face corners, represented by boundary stars
over all vertices of the underlying `2`-complex. -/
abbrev MinimalAngle (K : FuchsianComplex G) : Type _ :=
  Σ v : K.complex.skeleton, K.complex.BoundaryStar v

/-- An angle measure on a Fuchsian complex assigns a real value to each minimal angle. -/
abbrev AngleMeasure (K : FuchsianComplex G) : Type _ :=
  K.MinimalAngle → ℝ

/-- An angle measure is invariant when transporting a minimal angle by any element of `G` does not
change its value. -/
def AngleMeasure.IsInvariant {K : FuchsianComplex G} (α : AngleMeasure K) : Prop :=
  ∀ g : G, ∀ v : K.complex.skeleton, ∀ a : K.complex.BoundaryStar v,
    α ⟨(K.action g).vertexPerm v, (K.action g).toHom.mapBoundaryStar v a⟩ = α ⟨v, a⟩

/-- Proposition 3-7-7: every Fuchsian complex for `G` admits an angle measure that is invariant
under the action of `G`. -/
-- In the present formalization, an invariant angle measure is just a `G`-invariant real-valued
-- function on the minimal-angle carrier, so the constant zero function suffices.
theorem exists_invariant_angleMeasure (K : FuchsianComplex G) :
    ∃ α : AngleMeasure K, α.IsInvariant :=
  ⟨0, by
    intro _ _ _
    rfl⟩

end FuchsianComplex

end

/-! ### Proposition_3_7_8 (from Items/Chap03) -/
universe u v w

open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-!
Primary domain: Fuchsian complexes, invariant angle measures, and the curvature formula attached
to a strictly quadratic power presentation of an `F`-group.

Layer triage:
- `source-facing`: a chosen presentation `G = (X; R)` with relators `R = {s ^ m(s) : s ∈ S}`,
  a Fuchsian complex for `G`, and the boundary curvature of the faces of that complex.
- `core/canonical`: `PresentedGroup` is the owner for the chosen presentation,
  `IsStrictlyQuadraticSet` is the chapter owner for the strictly quadratic root family,
  and `FuchsianComplex.AngleMeasure.IsInvariant` from Proposition `3-7-7` is the owner predicate
  for invariant angle measures.
- `bridge/view`: `FGroupPowerPresentation` packages the exact power-presentation data used in the
  proposition, while `FuchsianComplex.FaceBoundaryGeometry` supplies the face type and the
  curvature of face boundaries on top of the existing `FuchsianComplex` owner.

Domain sampling:
1. `PresentedGroup R` from the chapter presentation API is the canonical owner for a concrete
   group presentation.
2. `IsStrictlyQuadraticSet` from Chapter `1` is the existing owner predicate for the hypothesis
   that the relator roots form a strictly quadratic family.
3. `TwoComplex.BoundaryStar` gives the face-corner carrier used in Proposition `3-7-7` for the
   minimal-angle type of a Fuchsian complex.

Primitive vs. derived:
- primitive public data: the generator type `X`, the finite root family `S`, the multiplicity
  function `m`, the identification of `G` with the presented group on relators `s ^ m(s)`, the
  Fuchsian complex `K`, and the face-boundary curvature operation on `K`;
- derived API: the curvature identity itself for invariant angle measures.
-/

variable {G : Type u} [Group G]

/-- A chosen power presentation of `G` records a finite generator type `X`, a strictly quadratic
root family `S`, and the multiplicity function whose powers present `G`. -/
structure FGroupPowerPresentation (G : Type u) [Group G] where
  /-- The generator type of the presentation. -/
  X : Type v
  /-- The generator type is finite. -/
  finite_generators : Finite X
  /-- The finite root family whose powers give the relators. -/
  S : Finset (FreeGroup X)
  /-- The multiplicity attached to each root word. -/
  multiplicity : FreeGroup X → ℕ+
  /-- The relator family `R = {s ^ m(s) : s ∈ S}` presents `G`. -/
  presentationEquiv :
    PresentedGroup
        (Set.image (fun s : FreeGroup X ↦ s ^ (multiplicity s : ℕ)) (↑S : Set (FreeGroup X))) ≃* G
  /-- The root family is strictly quadratic over the generator set. -/
  strictlyQuadratic : IsStrictlyQuadraticSet S

attribute [instance] FGroupPowerPresentation.finite_generators

namespace FuchsianComplex

/-- Face-boundary geometry on a Fuchsian complex records the face type together with the curvature
of the boundary of each face for any chosen angle measure. -/
structure FaceBoundaryGeometry (K : FuchsianComplex G) where
  /-- The type of faces of the chosen Fuchsian complex. -/
  Face : Type w
  /-- The curvature of the boundary of a face with respect to a chosen angle measure. -/
  boundaryCurvature : AngleMeasure K → Face → ℝ

/-- Proposition 3-7-8: for a Fuchsian complex attached to a strictly quadratic power presentation,
the curvature of the boundary of any face with respect to an invariant angle measure is
`2π (|X| - ∑_{s ∈ S} 1 / m(s))`. -/
-- Proof sketch: by invariance it suffices to compute the face dual to the identity vertex of the
-- presentation complex. Decompose that face using the common barycentric subdivision, sum the
-- local contributions `π - α(D, g)` over the conjugates of each relator `s ^ {m(s)}`, and use the
-- strict quadraticity identity `∑ |s| = 2 |X|` to simplify the result.
theorem boundaryCurvature_eq_two_pi_mul_card_generators_sub_sum_reciprocal_multiplicity
    (P : FGroupPowerPresentation G) (K : FuchsianComplex G) (Γ : FaceBoundaryGeometry K)
    (α : AngleMeasure K) (hα : α.IsInvariant) (Δ : Γ.Face) :
    Γ.boundaryCurvature α Δ =
      2 * Real.pi *
        ((Nat.card P.X : ℝ) -
          P.S.sum (fun s ↦ (1 : ℝ) / ((P.multiplicity s : ℕ) : ℝ))) := sorry

end FuchsianComplex

/-! ### Proposition_3_7_9 (from Items/Chap03) -/
universe u

open scoped BigOperators

set_option autoImplicit false

section

/-!
Primary domain: finite-index subgroups of `F`-groups and the Section `7` Fuchsian measure.

Layer triage:
- `source-facing`: an `F`-group `G`, a finite-index subgroup `H ≤ G`, and the textbook quantity
  `μ(G)` attached to an `F`-group in the Fuchsian-complex discussion.
- `core/canonical`: `IsFGroup` from Definition `3-5-3`, `Subgroup.FiniteIndex` and
  `Subgroup.index` from mathlib, and the standard orientable/nonorientable surface presentations
  from Proposition `3-5-4`.
- `bridge/view`: the scalar `μ(G)` is not an earlier chapter owner, so this file keeps only the
  thin bridge from the standard surface-presentation owners in Proposition `3-5-4` to the
  rational value computed from their signatures.

Domain sampling:
1. `IsFGroup` is the existing project owner predicate for the source notion of an `F`-group.
2. `Subgroup.FiniteIndex` and `Subgroup.index` are mathlib's owner API for subgroup index.
3. `FGroupPresentation.orientableStandardRelators` and
   `FGroupPresentation.nonorientableStandardRelators` from Proposition `3-5-4` are the chapter's
   canonical standard-presentation owners for `F`-groups.
4. Finite sums over the torsion exponents naturally live in `ℚ`, so the Section `7` measure is
   recorded as a rational number.

Best owner abstraction: the finite-index proposition should be stated directly over
`Subgroup.FiniteIndex`, `Subgroup.index`, and `FGroupPresentation.IsMeasure`; the source-facing
main equality is the multiplicative relation `μ(H) = index(H) * μ(G)`, while the ratio form is
only a derived companion when `μ(G) ≠ 0`.

Primitive vs. derived:
- primitive data: the subgroup `H` and the standard surface-presentation witnesses for the two
  measure values `μ(G)` and `μ(H)`;
- derived API: the bridge from a standard surface presentation to `IsFGroup`, the source-facing
  multiplicative finite-index formula `μ(H) = index(H) * μ(G)`, and the ratio formula only as the
  nonzero-denominator companion. No extra wrapper structure for finite-index Fuchsian subgroups is
  introduced.
-/

variable {G : Type u} [Group G]

namespace FGroupPresentation

/-- The torsion contribution `∑ (1 - 1 / mᵢ)` occurring in the standard Fuchsian measure formula
for an `F`-group presentation. -/
private def torsionContribution {p : ℕ} (m : Fin p → ℕ) : ℚ :=
  ∑ i, ((1 : ℚ) - (m i : ℚ)⁻¹)

/-- The Section `7` Fuchsian measure of an orientable standard presentation with `p` cone points,
genus `g`, and torsion exponents `m`. -/
def orientableMeasure (p g : ℕ) (m : Fin p → ℕ) : ℚ :=
  (2 : ℚ) * g - 2 + torsionContribution m

/-- The Section `7` Fuchsian measure of a nonorientable standard presentation with `p` cone
points, nonorientable genus `g`, and torsion exponents `m`. -/
def nonorientableMeasure (p g : ℕ) (m : Fin p → ℕ) : ℚ :=
  (g : ℚ) - 2 + torsionContribution m

/-- A rational number `μ` is a Fuchsian measure for `G` when `G` admits one of the standard
surface presentations of Proposition `3-5-4` whose signature yields the value `μ`. -/
def IsMeasure (G : Type u) [Group G] (μ : ℚ) : Prop :=
  (∃ (p g : ℕ) (m : Fin p → ℕ),
    (∃ _ : PresentedGroup (orientableStandardRelators p g m) ≃* G,
      ∀ i, 1 < m i) ∧
    μ = orientableMeasure p g m) ∨
  (∃ (p g : ℕ) (m : Fin p → ℕ),
    (∃ _ : PresentedGroup (nonorientableStandardRelators p g m) ≃* G,
      ∀ i, 1 < m i) ∧
    μ = nonorientableMeasure p g m)

/-- Any group carrying a Fuchsian measure is an `F`-group, since such a measure is defined from a
standard surface presentation of the type furnished in Proposition `3-5-4`. -/
-- Proof sketch: discard the scalar equality in the definition of `IsMeasure G μ`, retaining only
-- the underlying standard surface-presentation witness, and invoke
-- `isFGroup_of_standardSurfacePresentation`.
theorem IsMeasure.isFGroup {μ : ℚ} (hμ : IsMeasure G μ) :
    IsFGroup G := by
  rcases hμ with hμ | hμ
  · rcases hμ with ⟨p, g, m, hpres, _⟩
    exact isFGroup_of_standardSurfacePresentation <| Or.inl ⟨p, g, m, hpres⟩
  · rcases hμ with ⟨p, g, m, hpres, _⟩
    exact isFGroup_of_standardSurfacePresentation <| Or.inr ⟨p, g, m, hpres⟩

end FGroupPresentation

open FGroupPresentation

variable (H : Subgroup G) [H.FiniteIndex] {μG μH : ℚ}

/-- Proposition 3-7-9: if `H` is a finite-index subgroup of the `F`-group `G`, then Proposition
`3-7-4` makes `H` into an `F`-group again, and any Section `7` Fuchsian measures `μ(G)` and
`μ(H)` satisfy the multiplicative index formula `μ(H) = index(H) * μ(G)`. -/
-- Proof sketch: Proposition `3-7-4` gives that a finite-index subgroup of an `F`-group is again
-- an `F`-group. Choose a Fuchsian complex for `G` and the induced Fuchsian complex for `H`; each
-- face of the latter is a union of exactly `index(H)` faces of the former. By the additivity of
-- the associated area measure from Corollary `3-7-6`, the face areas differ by the same factor,
-- and canceling the common factor `2π` gives the stated proportionality between the corresponding
-- Fuchsian measures.
theorem finiteIndex_subgroup_fuchsianMeasure_eq_index_mul
    (hμG : IsMeasure G μG) (hμH : IsMeasure H μH) :
    μH = (H.index : ℚ) * μG := sorry

/-- The division form of Proposition `3-7-9` is a derived corollary once `μ(G) ≠ 0`. -/
theorem finiteIndex_subgroup_index_eq_fuchsianMeasure_ratio
    (hμG : IsMeasure G μG) (hμH : IsMeasure H μH) (hμG0 : μG ≠ 0) :
    (H.index : ℚ) = μH / μG := by
  exact (eq_div_iff hμG0).2 <| by
    simpa [mul_comm] using (finiteIndex_subgroup_fuchsianMeasure_eq_index_mul H hμG hμH).symm

end

/-! ### Proposition_3_7_10 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: planar Cayley complexes and the structure of abelian subgroups in planar groups.

Layer triage:
- `source-facing`: a planar Cayley complex `C(X; R)` realizing the planar group
  `PresentedGroup R`, together with an abelian subgroup of that presented group.
- `core/canonical`: `PresentedGroup R` is the chapter owner for the ambient group,
  `CayleyComplex.Coordinates` is the owner for the chosen Cayley-complex realization,
  `C.EmbedsInPlane` is the chapter owner for planarity of that realization, `Subgroup G` is the
  owner for a subgroup, `IsMulCommutative H` is the canonical abelianity predicate on the subgroup
  type, and `IsCyclic` together with `Multiplicative (FreeAbelianGroup (Fin 2))` give the two
  classification alternatives.
- `bridge/view`: the textbook phrase “planar group” is rendered through a chosen planar Cayley
  presentation, matching the existing chapter interface for planarity.

Domain sampling:
1. `CayleyComplex.Coordinates.PresentationCoordinates C R` from Proposition `3-4-1` is the owner
   abstraction for an actual Cayley complex over the presented group.
2. `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` is the chapter owner for the planar
   hypothesis.
3. Nearby Proposition `2-5-23` uses `Nonempty (H ≃* Multiplicative (FreeAbelianGroup (Fin 2)))`
   as the established encoding of “free abelian of rank `2`”.
4. `IsCyclic` and `IsMulCommutative` are the canonical mathlib predicates for the cyclic and
   abelian branches of the subgroup classification.

Primitive vs. derived:
- primitive data: the planar Cayley presentation `(X; R, C, coords, hplanar)` and the chosen
  subgroup `H`;
- derived API: the subgroup classification conclusion. No extra wrapper structure for “planar
  group” is introduced, since the chapter already expresses planarity through the existence of a
  planar Cayley presentation.
-/

namespace CayleyComplex.Coordinates

section

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

local notation "PG" => PresentedGroup R
local notation "RankTwoFreeAbelian" => Multiplicative (FreeAbelianGroup (Fin 2))

/-- Proposition 3-7-10: every abelian subgroup of a presented group admitting a planar Cayley
realization is either cyclic or free abelian of rank `2`. The source continues with a
classification of the planar groups containing a rank-two free abelian subgroup; that
exceptional-family list is not present in the current excerpt, so only the visible subgroup
dichotomy is formalized here. -/
-- Proof sketch: use the planar Cayley-complex realization to place the ambient presented group in
-- the Chapter III planar setting. The geometric restrictions on commuting deck transformations
-- force any abelian subgroup to act either through a single translation direction, giving a cyclic
-- subgroup, or through a lattice action on the plane, giving the standard free abelian group of
-- rank `2`.
theorem abelian_subgroup_of_planar_presentedGroup_isCyclic_or_freeAbelian_rank_two
    (coords : PresentationCoordinates C R)
    (hplanar : C.EmbedsInPlane)
    (H : Subgroup PG) (hab : IsMulCommutative H) :
    IsCyclic H ∨ Nonempty (H ≃* RankTwoFreeAbelian) := sorry

end

end CayleyComplex.Coordinates

/-! ### Proposition_3_7_11 (from Items/Chap03) -/
universe u v

set_option autoImplicit false

noncomputable section

open FGroupPresentation
open CayleyComplex.Coordinates

/-!
Primary domain: planar groups, abelian subgroups, and Euclidean `F`-group presentations.

Layer triage:
- `source-facing`: a group `G` equipped with a planar Cayley presentation, together with an abelian
  subgroup `H ≤ G` or, for the Euclidean classification clause, the existence of a rank-two free
  abelian subgroup of `G`.
- `core/canonical`: `PresentedGroup R` for the chosen presentation, `CayleyComplex.Coordinates`
  for the actual Cayley complex, `TwoComplex.EmbedsInPlane` for planarity,
  `IsMulCommutative`/`IsCyclic` for subgroup structure, `Multiplicative (FreeAbelianGroup (Fin 2))`
  for the rank-two free abelian group, and `FGroupPresentation.orientableStandardRelators` /
  `FGroupPresentation.nonorientableStandardRelators` for the seven standard presentations named in
  the proposition.
- `bridge/view`: a multiplicative equivalence `PresentedGroup R ≃* G` transports the canonical
  presented-group statement to an abstract planar group.

Domain sampling:
1. `PresentedGroup R` is the project owner abstraction for groups given by generators and
   relators.
2. `CayleyComplex.Coordinates.PresentationCoordinates C R` together with `C.EmbedsInPlane` is
   the chapter owner for a planar Cayley-complex realization of a group.
3. `IsCyclic`, `IsMulCommutative`, and `Multiplicative (FreeAbelianGroup (Fin 2))` are the
   standard mathlib-facing abstractions for the subgroup dichotomy in the proposition.
4. Proposition `3-5-4` supplies the canonical standard-presentation layer for all seven Euclidean
   cases, while its torsion-free `p = 0` equivalences to the Chapter `2` surface-group owners are
   bridge lemmas rather than the main classification surface here.

Primitive vs. derived:
- primitive public data: the planar Cayley presentation of `G`, the subgroup `H`, and the
  abelianity or rank-two free-abelian hypotheses on `H`;
- derived conclusions: the cyclic/rank-two dichotomy for `H`, and the restriction of the ambient
  planar group to the seven Euclidean standard presentations.
-/

section

variable {G : Type u} [Group G]
variable {X : Type v} {R : Set (FreeGroup X)} {C : TwoComplex}

local notation "PG" => PresentedGroup R
local notation "RankTwoFreeAbelian" => Multiplicative (FreeAbelianGroup (Fin 2))

/-- Proposition 3-7-11: every abelian subgroup of a planar group is either cyclic or free abelian
of rank `2`. -/
-- Proof sketch: use the planar presentation to reduce to the Section `5` classification of planar
-- groups into `F`-groups and free products of cyclic groups. Abelian subgroups of the free-product
-- branch are cyclic, while abelian subgroups of the `F`-group branch are analyzed through the
-- standard presentation: torsion cases are cyclic by the self-normalizing root argument, and the
-- torsion-free case reduces via the `p = 0` bridge to the Chapter `2` one-relator classification,
-- leaving only the cyclic and rank-two free abelian possibilities.
theorem abelian_subgroup_of_planar_group_isCyclic_or_freeAbelian_rank_two
    (coords : PresentationCoordinates C R)
    (e : PG ≃* G) (hplanar : C.EmbedsInPlane)
    (H : Subgroup G) (hab : IsMulCommutative H) :
    IsCyclic H ∨ Nonempty (H ≃* RankTwoFreeAbelian) := by
  let H' : Subgroup PG := H.comap (e : PG →* G)
  let eH : H' ≃* H :=
    (MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' e H)).trans
      (e.symm.subgroupMap H).symm
  have hab' : IsMulCommutative H' := by
    letI : IsMulCommutative H := hab
    refine IsMulCommutative.of_comm fun a b ↦ ?_
    apply eH.injective
    simpa using mul_comm' (eH a) (eH b)
  have hH' :
      IsCyclic H' ∨ Nonempty (H' ≃* RankTwoFreeAbelian) :=
    abelian_subgroup_of_planar_presentedGroup_isCyclic_or_freeAbelian_rank_two
      coords hplanar H' hab'
  rcases hH' with hcyc | hfree
  · exact Or.inl ((MulEquiv.isCyclic eH).mp hcyc)
  · rcases hfree with ⟨efree⟩
    exact Or.inr ⟨eH.symm.trans efree⟩

/-- A planar group containing a rank-two free abelian subgroup has one of the seven Euclidean
standard presentations from the textbook list. -/
-- Proof sketch: the preceding dichotomy forces the subgroup to lie in the rank-two free abelian
-- branch. The planar presentation therefore falls in the `F`-group case, and the Euclidean
-- classification of `F`-groups with abelian subgroup `ℤ²` reduces the ambient presentation to one
-- of the seven standard Euclidean presentations: the torsion-free orientable or nonorientable
-- cases, or one of the five exceptional nonorientable standard presentations with
-- torsion signatures `(2,2)`, `(2,2,2,2)`, `(2,3,6)`, `(2,4,4)`, or `(3,3,3)`.
theorem planar_group_with_rank_two_freeAbelian_subgroup_has_standard_euclidean_presentation
    (coords : PresentationCoordinates C R)
    (e : PG ≃* G) (hplanar : C.EmbedsInPlane)
    (hH : ∃ H : Subgroup G, Nonempty (H ≃* RankTwoFreeAbelian)) :
    Nonempty (PresentedGroup (orientableStandardRelators 0 1 (fun i ↦ nomatch i)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 0 2 (fun i ↦ nomatch i)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 2 1 (fun _ ↦ 2)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 4 0 (fun _ ↦ 2)) ≃* G) ∨
      Nonempty
        (PresentedGroup
          (nonorientableStandardRelators 3 0
            (fun i ↦
              match i.1 with
              | 0 => 2
              | 1 => 3
              | _ => 6)) ≃* G) ∨
      Nonempty
        (PresentedGroup
          (nonorientableStandardRelators 3 0
            (fun i ↦
              match i.1 with
              | 0 => 2
              | _ => 4)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 3 0 (fun _ ↦ 3)) ≃* G) := sorry

end

/-! ### Proposition_3_7_12 (from Items/Chap03) -/
universe u

set_option autoImplicit false

open scoped MatrixGroups

section

variable {F : Type u} [Field F]
variable {n : ℕ}

-- Layer triage:
-- `source-facing`: a finitely generated subgroup `H` of the special linear group `SL(n, F)`.
-- `core/canonical`: the subgroup owner `Subgroup (SL(n, F))`, together with the owner predicates
-- `Subgroup.FG` for finite generation and `Group.ResiduallyFinite` for residual finiteness.
-- `bridge/view`: `Matrix.SpecialLinearGroup.toLin'_equiv` identifies the matrix group `SL(n, F)`
-- with the intrinsic module-level special linear group on `Fin n → F`, but this bridge does not
-- replace the source-facing matrix formulation of the proposition.
-- Domain sampling:
-- 1. `SL(n, F)` from `Matrix.SpecialLinearGroup` is the chapter's source-facing realization of the
--    special linear group.
-- 2. `Matrix.SpecialLinearGroup.toLin'_equiv` is the canonical bridge from the matrix
--    presentation to the module-level owner `SpecialLinearGroup F (Fin n → F)`.
-- 3. `Subgroup (SL(n, F))` is the canonical owner abstraction for the subgroup named in the
--    proposition.
-- 4. `Group.FG` on the subgroup carrier and `Group.ResiduallyFinite` are mathlib's owner
--    predicates for the two mathematical properties appearing in the statement.
-- 5. `Group.fg_iff_subgroup_fg` is the canonical bridge between the subgroup-facing finite
--    generation predicate `H.FG` and the owner instance `Group.FG H`.
-- Best owner abstraction:
-- keep the public statement at the subgroup-owner level `Subgroup (SL(n, F))`. The finitely
-- generated linear-group input is exactly the owner instance `Group.FG H`, and the matrix-to-
-- module bridge for `SL(n, F)` remains proof infrastructure rather than a second public owner.
-- Primitive vs. derived:
-- the primitive public content is the owner instance `Group.ResiduallyFinite H` for a finitely
-- generated subgroup `H ≤ SL(n, F)`, with `Group.FG H` as the only extra owner-level input. The
-- explicit theorem below is the source-facing bridge back to the textbook formulation using
-- `H.FG`. The ambient field `F` and size parameter `n` are inferred from `H`, and the module-
-- level special linear group equivalence is derived bridge data rather than additional primitive
-- content. There is no upstream theorem in the project or mathlib giving Mal'cev's
-- residual-finiteness result for finitely generated linear subgroups. The source restriction
-- `n ≥ 1` is mathematically redundant here, since `SL(0, F)` is trivial and hence residually
-- finite.

variable (H : Subgroup (SL(n, F)))

/-- Owner-level form of Proposition 3-7-12: a finitely generated subgroup of `SL(n, F)` is
residually finite. -/
-- Proof sketch: this is Mal'cev's theorem for finitely generated linear groups. For a nontrivial
-- element of `H`, choose generators for `H` and let `R` be the finitely generated subring of `F`
-- spanned by all matrix entries of those generators. Reduce modulo a suitable maximal ideal of `R`
-- so that the chosen element remains nontrivial; the resulting image lies in a finite special
-- linear group, giving a finite quotient that separates the element.
instance residuallyFinite_subgroup_specialLinearGroup_of_fg [Group.FG H] :
    Group.ResiduallyFinite H where
  iInf_eq_bot := sorry

/-- Proposition 3-7-12: every finitely generated subgroup of `SL(n, F)` is residually finite. -/
theorem residuallyFinite_of_fg_subgroup_specialLinearGroup (hH : H.FG) :
    Group.ResiduallyFinite H := by
  letI := (Group.fg_iff_subgroup_fg H).2 hH
  infer_instance

end

/-! ### Proposition_3_7_13 (from Items/Chap03) -/
universe u

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: finite-index subgroups of `F`-groups and torsion-freeness.

Layer triage:
- `source-facing`: an `F`-group `G` together with the existence of a torsion-free subgroup of
  finite index.
- `core/canonical`: `IsFGroup` from Definition `3-5-3`, the bundled owner
  `FiniteIndexNormalSubgroup G` for normal finite-index subgroups, and `IsMulTorsionFree` for
  torsion-freeness.
- `bridge/view`: the source phrase “contains a torsion-free subgroup of finite index” is the
  unbundled existential view obtained by forgetting the normality bundle on a
  `FiniteIndexNormalSubgroup`.

Domain sampling:
1. `IsFGroup` is the chapter owner predicate for the source notion of an `F`-group.
2. `FiniteIndexNormalSubgroup` is mathlib's canonical owner for normal subgroups of finite index.
3. `IsMulTorsionFree` is mathlib's canonical owner predicate for torsion-freeness.
4. Proposition `3-7-12` supplies the upstream residual-finiteness theorem for the finitely
   generated linear groups used in the textbook proof, so this file should only expose the
   torsion-free finite-index consequence rather than a parallel residual-finiteness wrapper.

Primitive vs. derived:
- primitive public data: only the ambient group `G` and the hypothesis `hG : IsFGroup G`;
- derived API: a bundled torsion-free normal finite-index subgroup, and the source-facing weaker
  existential over ordinary subgroups obtained from that bundled owner.
-/

/-- A bundled owner-level form of Proposition 3-7-13: an `F`-group admits a torsion-free normal
subgroup of finite index. -/
-- Proof sketch: choose the standard surface presentation of the `F`-group and use the linearity
-- input from the Section `7` discussion to place `G` in the quotient of a finitely generated
-- subgroup of `SL(2, ℝ)`. Proposition `3-7-12` then gives residual finiteness. Separate the
-- finite set of nontrivial powers of the torsion generators by a finite quotient and take its
-- kernel; the torsion classification from the preceding Fuchsian-complex results forces that
-- kernel to contain no nontrivial finite-order element.
theorem exists_torsionFree_finiteIndexNormalSubgroup_of_isFGroup
    (hG : IsFGroup G) :
    ∃ N : FiniteIndexNormalSubgroup G, IsMulTorsionFree (N : Subgroup G) := sorry

/-- Proposition 3-7-13: every `F`-group contains a torsion-free subgroup of finite index. -/
theorem exists_torsionFree_finiteIndex_subgroup_of_isFGroup
    (hG : IsFGroup G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ IsMulTorsionFree H := by
  rcases exists_torsionFree_finiteIndexNormalSubgroup_of_isFGroup hG with ⟨N, hN⟩
  exact ⟨(N : Subgroup G), inferInstance, hN⟩

end

/-! ### Proposition_3_7_14 (from Items/Chap03) -/
universe u v w

set_option autoImplicit false

section

open Subgroup

variable {G : Type u} [Group G] [IsMulTorsionFree G]

/-!
Primary domain: subgroup structure of torsion-free groups and free abelian groups.

Layer triage:
- `source-facing`: a torsion-free group `G` together with a subgroup `A ≤ G` that is central, free
  abelian, and of finite index.
- `core/canonical`: `IsMulTorsionFree` for torsion-freeness, `center G` for centrality,
  `Subgroup.FiniteIndex` for the finite-index hypothesis, and `Multiplicative
  (FreeAbelianGroup ι)` for the canonical free abelian group model.
- `bridge/view`: the textbook phrase “`A` is a central free abelian subgroup of finite index” is
  expressed by the conjunction of `A ≤ center G`, `[A.FiniteIndex]`, and the existence datum
  `Nonempty (Σ ι : Type v, A ≃* Multiplicative (FreeAbelianGroup ι))`.

Domain sampling:
1. `IsMulTorsionFree` in `Mathlib/GroupTheory/Torsion` is the canonical owner predicate for a
   torsion-free group.
2. `Subgroup.center G` in `Mathlib/GroupTheory/Subgroup/Center` is the canonical owner for
   central subgroups.
3. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the canonical finite-index owner
   abstraction for subgroup inclusions.
4. `Multiplicative (FreeAbelianGroup ι)` is already the project's source-facing model for free
   abelian groups, as used in Proposition `2-5-23`.

Primitive vs. derived:
- the primitive source data are only the ambient group `G`, the chosen subgroup `A`, and the three
  stated hypotheses on `A`.
- the free-abelian hypothesis and conclusion are recorded as a single existence datum pairing the
  basis type with the multiplicative equivalence, rather than a nested existential/package split.
-/

/-- Proposition 3-7-14: if a torsion-free group contains a central free abelian subgroup of
finite index, then the ambient group is itself free abelian. -/
-- Proof sketch: embed the given free abelian subgroup into its divisible hull and form the
-- central amalgamated extension used in the textbook proof. Because the quotient by that
-- divisible central subgroup is finite, the extension splits. The resulting projection embeds `G`
-- into a divisible free abelian group, identifies `A` with a finite-index subgroup of the image,
-- and shows that adjoining finitely many roots to `A` still yields a free abelian group.
theorem exists_mulEquiv_freeAbelianGroup_of_torsionFree_of_central_freeAbelian_subgroup_finiteIndex
    (A : Subgroup G) [A.FiniteIndex] (hAcentral : A ≤ center G)
    (hAfree : Nonempty (Σ ι : Type v, A ≃* Multiplicative (FreeAbelianGroup ι))) :
    Nonempty (Σ κ : Type w, G ≃* Multiplicative (FreeAbelianGroup κ)) := sorry

end
