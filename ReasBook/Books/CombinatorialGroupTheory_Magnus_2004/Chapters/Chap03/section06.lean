

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_6_1 (from Items/Chap03) -/
universe u v w

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: planar Cayley complexes and their left-translation automorphisms.

Layer triage:
- `source-facing`: a planar Cayley complex `C(X; R)` realized as an actual `TwoComplex`, together
  with the nontrivial automorphism induced by left multiplication by `g ≠ 1`; for the fixed-point
  part, also a chosen planar embedding together with an ambient homeomorphism of `ℝ²`
  realizing that automorphism on geometric face images.
- `core/canonical`: `CayleyComplex.Coordinates` is the chapter owner for the Cayley-complex
  realization, `OneComplex.GeometricEdge` and `TwoComplex.GeometricFace` are the owners for
  unoriented cells, `TwoComplex.Aut` is the owner for automorphisms together with their induced
  geometric-edge and geometric-face permutations, while `TwoComplex.TwoManifoldEmbedding` is the
  owner for a chosen planar realization.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.geometricFaceSet`,
  `TwoComplex.TwoManifoldEmbedding.geometricFaceUnion`, and
  `TwoComplex.TwoManifoldEmbedding.RealizesAutomorphism` express the passage from the
  combinatorial automorphism to the ambient plane homeomorphism acting on the geometric images of
  faces.

Domain sampling:
1. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the owner abstraction for actual
   Cayley complexes with their canonical left translations.
2. `OneComplex.GeometricEdge` from Definition `3-2-1` is the owner abstraction for actual edges
   modulo reversal.
3. `TwoComplex.GeometricFace` from Definition `3-2-4` is the owner abstraction for geometric
   faces modulo reversal.
4. `TwoComplex.Aut` from Proposition `3-4-1` is the owner abstraction for genuine automorphisms
   of a `2`-complex and their induced geometric-edge and geometric-face permutations.
5. `TwoComplex.TwoManifoldEmbedding` from Proposition `3-5-5`, specialized to `𝔼²` through
   Proposition `3-5-6`, is the owner abstraction for a chosen planar geometric realization.
6. `Homeomorph 𝔼² 𝔼²` is mathlib's canonical owner for the ambient planar self-map needed by the
   fixed-point clause.

Primitive vs. derived:
- primitive data: the actual Cayley complex `C`, its Cayley coordinates, the chosen nontrivial
  left translation, the chosen planar embedding, and the ambient plane homeomorphism realizing the
  automorphism on geometric face images;
- derived API: the induced action on oriented edges, the induced action on geometric faces, the
  geometric images of geometric faces in the plane, and the fixed-point conclusion for an
  invariant finite geometric-face union.
-/

namespace CayleyComplex.Coordinates

variable {G : Type u} [Group G]
variable {Y : Type v} {Rel : Type w}
variable {C : TwoComplex} {edgeLabel : Y → G}

local notation "GeometricEdge" => OneComplex.GeometricEdge C.skeleton

/-- Proposition 3-6-1 (1): a nontrivial left-translation automorphism of a Cayley complex fixes
no vertex. -/
-- Proof sketch: in Cayley coordinates, left translation by `g` sends the vertex `h` to `g * h`.
-- If this were equal to `h`, left cancellation would force `g = 1`, contradicting the
-- hypothesis.
theorem leftTranslation_fixes_no_vertex
    (coords : Coordinates C edgeLabel Rel) {g : G} (hg : g ≠ 1)
    (v : C.skeleton) :
    (coords.leftTranslation g).vertexPerm v ≠ v := by
  intro hfix
  have hcoord : g * coords.vertexEquiv v = coords.vertexEquiv v := by
    simpa [coords.vertexPerm_apply, hfix] using
      (coords.leftTranslation_vertexPerm_apply g (coords.vertexEquiv v)).symm
  have hg' : g = 1 := by
    have hcoord' : g * coords.vertexEquiv v = 1 * coords.vertexEquiv v := by
      simpa using hcoord
    exact mul_right_cancel hcoord'
  exact hg hg'

/-- A nontrivial left-translation automorphism of a Cayley complex fixes no oriented edge. -/
-- Proof sketch: in Cayley coordinates, left translation sends the oriented edge `(h, y)` to
-- `(g * h, y)`. Equality with the original oriented edge therefore forces `g * h = h`, and left
-- cancellation gives `g = 1`, contradicting the hypothesis.
theorem leftTranslation_fixes_no_orientedEdge
    (coords : Coordinates C edgeLabel Rel) {g : G} (hg : g ≠ 1)
    (e : C.skeleton.Edge) :
    (coords.leftTranslation g).edgePerm e ≠ e := by
  intro hfix
  have hcoord : (g * (coords.edgeEquiv e).1, (coords.edgeEquiv e).2) = coords.edgeEquiv e := by
    simpa [coords.edgePerm_apply, hfix] using
      (coords.leftTranslation_edgePerm_apply g (coords.edgeEquiv e)).symm
  have hfst : g * (coords.edgeEquiv e).1 = (coords.edgeEquiv e).1 :=
    congrArg Prod.fst hcoord
  have hg' : g = 1 := by
    have hfst' : g * (coords.edgeEquiv e).1 = 1 * (coords.edgeEquiv e).1 := by
      simpa using hfst
    exact mul_right_cancel hfst'
  exact hg hg'

/-- Proposition 3-6-1 (2): if the edge-label involution has no fixed points, then a nontrivial
left-translation automorphism of a Cayley complex fixes no geometric edge. -/
-- Proof sketch: if a geometric edge were fixed, some oriented representative would be sent either
-- to itself or to its reverse. The first case is impossible by the oriented-edge argument above.
-- In the second case, the coordinate formula for edge reversal forces the label coordinate `y` to
-- satisfy `labelInv y = y`, contradicting the fixed-point-free label-involution hypothesis.
theorem leftTranslation_fixes_no_edge
    (coords : Coordinates C edgeLabel Rel)
    (hlabelInv : ∀ y : Y, coords.labelInv y ≠ y)
    {g : G} (hg : g ≠ 1)
    (e : GeometricEdge) :
    (coords.leftTranslation g).geometricEdgePerm e ≠ e := by
  refine Quotient.inductionOn e ?_
  intro e hfix
  rcases Quotient.exact hfix with hfix | hfix
  · exact (coords.leftTranslation_fixes_no_orientedEdge hg e) hfix
  · have hcoord : (g * (coords.edgeEquiv e).1, (coords.edgeEquiv e).2) = coords.edgeEquiv e⁻¹ := by
      simpa [coords.edgePerm_apply, hfix] using
        (coords.leftTranslation_edgePerm_apply g (coords.edgeEquiv e)).symm
    have hy : (coords.edgeEquiv e).2 = coords.labelInv (coords.edgeEquiv e).2 := by
      simpa [coords.edgeInv_apply] using congrArg Prod.snd hcoord
    exact hlabelInv _ hy.symm

/-- Proposition 3-6-1 (3): if a nontrivial left-translation automorphism of a planar Cayley
complex fixes no geometric edge, is realized by an ambient homeomorphism of `ℝ²`, and leaves
invariant a nonempty finite union of geometric-face images, then that ambient homeomorphism has a
unique fixed point in that union. -/
-- Proof sketch: pass to an invariant finite planar disc containing the given union of face
-- images and argue by induction on the number of faces. The boundary analysis in the textbook
-- either removes a full orbit of boundary faces or cuts out a smaller invariant disc, eventually
-- forcing a unique fixed point of the ambient planar homeomorphism; the no-fixed-geometric-edge
-- hypothesis rules out boundary fixed segments during the induction.
theorem existsUnique_fixedPoint_of_invariant_finite_geometricFaceUnion
    (coords : Coordinates C edgeLabel Rel)
    (embedding : TwoComplex.TwoManifoldEmbedding C 𝔼²)
    {g : G} (hg : g ≠ 1)
    (hedge : ∀ e : GeometricEdge, (coords.leftTranslation g).geometricEdgePerm e ≠ e)
    (φ : Homeomorph 𝔼² 𝔼²)
    (hφ : embedding.RealizesAutomorphism (coords.leftTranslation g) φ)
    (faceUnion : Set (TwoComplex.GeometricFace C))
    (hnonempty : faceUnion.Nonempty) (hfinite : faceUnion.Finite)
    (hinv : φ '' embedding.geometricFaceUnion faceUnion = embedding.geometricFaceUnion faceUnion) :
    ∃! x : 𝔼², x ∈ embedding.geometricFaceUnion faceUnion ∧ φ x = x := sorry

end CayleyComplex.Coordinates

/-! ### Proposition_3_6_2 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

open GroupPresentation
open scoped Pointwise
/-!
Primary domain: planar Cayley complexes and the torsion structure of the presented group
`G = (X; R)` when the relators are prescribed powers of a chosen primitive root family.

Layer triage:
- `source-facing`: a planar Cayley complex `C(X; R)` realized as an actual `TwoComplex`,
  together with a specified root family `S` and multiplicity function `m(s)` whose powers are
  exactly the relators.
- `core/canonical`: `PresentedGroup R` for the group `(X; R)`,
  `CayleyComplex.Coordinates.PresentationCoordinates C R` for the chosen Cayley-complex
  realization,
  `C.EmbedsInPlane` for the chapter’s planar owner,
  `GroupPresentation.IsPrimitiveRelatorPowerFamily` and
  `GroupPresentation.IsPrimitiveRelatorRoot` for the relator-power data,
  `IsProperPower` for the primitive-root condition,
  `IsOfFinOrder` and `orderOf` for torsion, `Subgroup.zpowers` for cyclic subgroups, and
  `Subgroup.normalizer` for self-normalizing subgroups.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding` is the geometric witness behind
  `C.EmbedsInPlane`, while the source clause that the relators are exactly the powers `s ^ m(s)`
  and that the chosen roots are already primitive is recorded by
  `GroupPresentation.IsPrimitiveRelatorPowerFamily R S m`; the pointwise primitive-root view is
  then derived through `GroupPresentation.IsPrimitiveRelatorRoot S s`.

Domain sampling:
1. `PresentedGroup R` is the project owner abstraction for the group given by generators and
   relators.
2. `CayleyComplex.Coordinates.PresentationCoordinates C R` from Proposition `3-4-1` is the owner
   abstraction for an actual planar Cayley complex with its canonical left translations and
   relator boundaries.
3. `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` is the source-facing planar owner used by
   Proposition `3-6-1`.
4. `GroupPresentation.IsPrimitiveRelatorPowerFamily` from Definition `3-5-3` is the source-facing
   owner for a chosen primitive relator-power family, while
   `GroupPresentation.IsPrimitiveRelatorRoot` is its pointwise derived view.
5. `IsProperPower`, together with `IsOfFinOrder`, `orderOf`, `Subgroup.zpowers`, and
   `Subgroup.normalizer`, provides the primitive-root owner predicate and the canonical mathlib
   torsion/subgroup APIs for the conclusions appearing in the proposition.

Primitive vs. derived:
- primitive data: the actual Cayley complex `C`, its presentation coordinates, the planar
  hypothesis, the chosen root family `S`, the multiplicity function `m`, and the source owner
  hypothesis `GroupPresentation.IsPrimitiveRelatorPowerFamily R S m`;
- derived API: the torsion classification of elements of `PresentedGroup R`, the exact order of
  each root image, the torsion-free special case, and self-normalization for the chosen primitive
  relator roots. The pointwise primitive-root layer is derived through
  `GroupPresentation.IsPrimitiveRelatorRoot S`, the conjugacy clause is expressed with mathlib’s
  owner relation `IsConj`, and the full set of conjugators is described by the existing pointwise
  left-coset notation on sets.
-/

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}
variable {S : Set (FreeGroup X)}
variable (coords : PresentationCoordinates C R) (hplanar : C.EmbedsInPlane)
variable (m : FreeGroup X → ℕ+) (hR : IsPrimitiveRelatorPowerFamily R S m)

local notation "G" => PresentedGroup R
local notation "q" => PresentedGroup.mk R

/-- Proposition 3-6-2: every nontrivial finite-order element of a planar group
`PresentedGroup R` is conjugate to a unique proper positive power of the unique primitive relator
root lying under its face stabilizer, and the full set of conjugators is a left coset of the
cyclic subgroup generated by that primitive root image.
-/
-- Proof sketch: let `g` act on the planar Cayley complex by the left translation supplied by the
-- chosen coordinates. Proposition `3-6-1` gives a unique fixed geometric face of this action.
-- Reading the boundary of that face from a suitable vertex shows that the boundary relator is
-- `s ^ m(s)` for a unique primitive root `s ∈ S`, that `g` moves the chosen vertex by the proper
-- power `s ^ b` with `0 < b < m(s)`, and hence that `g = u * (q s)^b * u⁻¹`. Rotating the
-- basepoint around the same face changes `u` exactly by right multiplication by powers of `q s`,
-- so the conjugators form the left coset `u • (Subgroup.zpowers (q s) : Set G)`.
theorem existsUnique_primitiveRelatorRoot_power_conjugatorLeftCoset_of_nontrivial_isOfFinOrder
    {g : G} (hg : g ≠ 1) (hfin : IsOfFinOrder g) :
    ∃! s : FreeGroup X,
      IsPrimitiveRelatorRoot S s ∧
      ∃! b : ℕ,
        0 < b ∧
        b < (m s : ℕ) ∧
        IsConj g ((q s) ^ b) ∧
        ∃ u : G,
          {v : G | g = v * (q s) ^ b * v⁻¹} = u • (Subgroup.zpowers (q s) : Set G) := sorry

/-- The image of a chosen relator root in `PresentedGroup R` has order equal to its
multiplicity; primitivity is derived from `hR`. -/
-- Proof sketch: the relation `q (s ^ m(s)) = 1` shows that the order of `q s` divides `m(s)`.
-- Since `hs` identifies `s` as one of the chosen relator roots and `hR` already records that
-- every chosen root is primitive, the primitive-root case of Proposition `3-6-2` applies
-- directly and forces `orderOf (q s) = m(s)`.
theorem orderOf_relatorRootImage_eq_relatorMultiplicity
    (s : FreeGroup X) (hs : s ∈ S) :
    orderOf (q s) = m s := sorry

/-- If every relator multiplicity is `1`, then the presented group `PresentedGroup R` is
torsion-free. -/
-- Proof sketch: if a nontrivial finite-order element existed, Proposition `3-6-2` would express
-- it as a conjugate of `(q s)^b` for a primitive root `s` with `0 < b < m(s)`. When every
-- `m(s)` equals `1`, no such positive integer `b` can exist, so every finite-order element must
-- be trivial.
theorem isMulTorsionFree_of_all_relatorMultiplicities_eq_one
    (hm : ∀ ⦃s : FreeGroup X⦄, s ∈ S → m s = 1) :
    IsMulTorsionFree G := sorry

/-- For a chosen relator root of multiplicity greater than `1`, the cyclic subgroup generated by
its image is self-normalizing; primitivity is derived from `hR`. -/
-- Proof sketch: an element of the normalizer conjugates `q s` to another element of the same
-- finite cyclic subgroup. The primitive-root uniqueness clause in Proposition `3-6-2` forces
-- that conjugating element itself to differ from a fixed conjugator by a power of `q s`; since
-- `hR` already makes every chosen relator root primitive, the whole normalizer is already the
-- cyclic subgroup `Subgroup.zpowers (q s)`.
theorem normalizer_zpowers_relatorRootImage_eq_zpowers
    (s : FreeGroup X) (hs : s ∈ S) (hmult : 1 < m s) :
    Subgroup.normalizer (Subgroup.zpowers (q s)) =
      Subgroup.zpowers (q s) := sorry

end CayleyComplex.Coordinates
