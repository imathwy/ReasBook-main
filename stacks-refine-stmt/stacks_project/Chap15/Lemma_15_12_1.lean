import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

noncomputable section

section

/-- The category of pairs `(A, I)`, realized by a commutative ring together with an ideal. -/
structure RingPairCat where
  ring : CommRingCat.{u}
  ideal : Ideal ring

namespace RingPairCat

/-- The quotient arrow `A → A ⧸ I` attached to a ring pair `(A, I)`. -/
def quotientArrow (X : RingPairCat.{u}) : Arrow CommRingCat.{u} :=
  Arrow.mk
    (show X.ring ⟶ CommRingCat.of (X.ring ⧸ X.ideal) from
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal))

/-- The category structure on ring pairs induced from the arrow category of quotient maps. -/
instance : Category RingPairCat.{u} :=
  inferInstanceAs (Category (InducedCategory (Arrow CommRingCat.{u}) quotientArrow))

/-- The underlying ring hom of a morphism of ring pairs. -/
abbrev ringHom {X Y : RingPairCat.{u}} (f : X ⟶ Y) : X.ring →+* Y.ring :=
  f.hom.left.hom

/-- The object property cutting out the full subcategory of henselian pairs. -/
def henselianPairProperty : ObjectProperty RingPairCat.{u} :=
  fun X ↦ HenselianRing X.ring X.ideal

/-- The category of henselian pairs as the full subcategory of `RingPairCat` defined by
`HenselianRing`. -/
abbrev HenselianPairCat :=
  henselianPairProperty.FullSubcategory

/-- The inclusion functor from henselian pairs to all pairs. -/
abbrev henselianPairInclusion : HenselianPairCat.{u} ⥤ RingPairCat.{u} :=
  henselianPairProperty.ι

/-- The chosen henselization object of a ring pair, obtained from the left adjoint of the
inclusion of henselian pairs. -/
abbrev henselization (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    HenselianPairCat.{u} :=
  henselianPairInclusion.leftAdjoint.obj X

/-- The underlying ring pair of the chosen henselization of `X`. -/
abbrev henselizationPair (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    RingPairCat.{u} :=
  henselianPairInclusion.obj (henselization X)

/-- The underlying commutative ring of the chosen henselization of `X`. -/
abbrev henselizationRing (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    CommRingCat.{u} :=
  (henselizationPair X).ring

/-- The distinguished ideal of the chosen henselization of `X`. -/
abbrev henselizationIdeal (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    Ideal (henselizationRing X) :=
  (henselizationPair X).ideal

/-- The canonical ring map from a ring pair to its chosen henselization. -/
abbrev toHenselization (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    X.ring →+* henselizationRing X :=
  ((Adjunction.ofIsRightAdjoint henselianPairInclusion).unit.app X).hom.left.hom

/-- The map of chosen henselizations induced by a morphism of ring pairs. -/
abbrev henselizationMap {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    henselization X ⟶ henselization Y :=
  henselianPairInclusion.leftAdjoint.map f

/-- The underlying ring map on chosen henselization rings induced by a morphism of ring pairs. -/
abbrev henselizationRingMap {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    henselizationRing X →+* henselizationRing Y :=
  ringHom <| henselianPairInclusion.map (henselizationMap f)

/-- Naturality of the canonical map to chosen henselization on underlying rings. -/
lemma toHenselization_naturality {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    (toHenselization Y).comp (ringHom f) =
      (henselizationRingMap f).comp (toHenselization X) := by
  sorry

/-- The chosen henselization ring of a pair carries its canonical `X.ring`-algebra structure. -/
instance henselizationRing_algebra (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    Algebra X.ring (henselizationRing X) :=
  (toHenselization X).toAlgebra

/-- The ring pair attached to an ideal of a commutative ring. -/
abbrev pairOfIdeal {A : Type u} [CommRing A] (I : Ideal A) : RingPairCat.{u} :=
  RingPairCat.mk (CommRingCat.of A) I

/-- The chosen henselization ring of the pair `(A, I)` carries its canonical `A`-algebra
structure via the unit map of the pair-henselization adjunction. -/
instance pairOfIdeal_henselizationRing_algebra {A : Type u} [CommRing A] (I : Ideal A)
    [henselianPairInclusion.IsRightAdjoint] :
    Algebra A (henselizationRing (pairOfIdeal I)) :=
  (toHenselization (pairOfIdeal I)).toAlgebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (J : Ideal B)

-- Proof sketch: the quotient map `A ⧸ I → B ⧸ J` is induced by the universal property of the
-- quotient because `I` maps into `J`; the defining square then commutes by construction.
/-- The quotient maps associated to a morphism of pairs form a commutative square in
`CommRingCat`. -/
lemma pairOfIdeal_hom_square (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    CommRingCat.ofHom (algebraMap A B) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ) := sorry

/-- The map of pairs induced by an `A`-algebra map carrying `I` into `J`. -/
abbrev pairOfIdealMap (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    pairOfIdeal I ⟶ pairOfIdeal J :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ))
      (pairOfIdeal_hom_square I J hIJ)

end

-- Proof sketch: for a pair `(A, I)`, take the filtered colimit of the category of étale
-- neighborhoods of `(A, I)` inducing an isomorphism modulo `I`, as in the source. Lemma
-- `15.11.13` gives henselianity of the resulting pair, and the universal mapping property proved
-- in the text identifies morphisms from this henselian pair to any henselian target pair with
-- morphisms from `(A, I)` to that target.
/-- Lemma 15.12.1: the inclusion functor from the category of henselian pairs to the category of
pairs is a right adjoint; equivalently, henselization of pairs gives a left adjoint to this
inclusion. -/
theorem henselianPairInclusion_isRightAdjoint :
    henselianPairInclusion.IsRightAdjoint := sorry

end RingPairCat

end
