import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCartesianFactorization

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor

namespace LocallyDefinedHomRepresentativeOver

/-- Source stage 2.6, isolated at the point where the proof chooses local factorizations.

For a raw locally-defined morphism `alpha` over `g >> p phi`, the source proof constructs the
factor on the same cover as `alpha`: for every member of `alpha.cover`, factor the local arrow
through the cartesian arrow `phi`, then check that these local factors satisfy the matching
condition.  This structure records exactly that resulting matching family, before passing to the
plus quotient. -/
structure SameCoverCartesianFactorizationData
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y z : X.S} (phi : x ⟶ y) (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)) where
  /-- The local factors through `phi`, indexed by the original cover of `alpha`. -/
  family : Meq (locallyDefinedHomSaturatedPresheaf X g) alpha.cover
  /-- After composing with the ordinary representative of `phi`, this same-cover representative
  gives the original raw representative up to the common-refinement equivalence. -/
  comp_equivalent :
    Equivalent (J := J)
      (composeOver (J := J)
        ({ cover := alpha.cover, family := family } :
          LocallyDefinedHomRepresentativeOver (J := J) X g)
        (ordinaryHomToRepresentativeOver (J := J) X phi))
      alpha

namespace SameCoverCartesianFactorizationData

/-- Package the same-cover local factorization data as a raw fixed-base representative over `g`. -/
noncomputable def toRepresentative
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y z : X.S} {phi : x ⟶ y} {g : X.p.obj z ⟶ X.p.obj x}
    {alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)}
    (D : SameCoverCartesianFactorizationData (J := J) phi g alpha) :
    LocallyDefinedHomRepresentativeOver (J := J) X g where
  cover := alpha.cover
  family := D.family

@[simp]
theorem toRepresentative_cover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y z : X.S} {phi : x ⟶ y} {g : X.p.obj z ⟶ X.p.obj x}
    {alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)}
    (D : SameCoverCartesianFactorizationData (J := J) phi g alpha) :
    D.toRepresentative.cover = alpha.cover :=
  rfl

@[simp]
theorem toRepresentative_family
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y z : X.S} {phi : x ⟶ y} {g : X.p.obj z ⟶ X.p.obj x}
    {alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)}
    (D : SameCoverCartesianFactorizationData (J := J) phi g alpha) :
    D.toRepresentative.family = D.family :=
  rfl

/-- The packaged representative satisfies the composition equivalence recorded in the local
source data. -/
theorem toRepresentative_comp_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {x y z : X.S} {phi : x ⟶ y} {g : X.p.obj z ⟶ X.p.obj x}
    {alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)}
    (D : SameCoverCartesianFactorizationData (J := J) phi g alpha) :
    Equivalent (J := J)
      (composeOver (J := J) D.toRepresentative
        (ordinaryHomToRepresentativeOver (J := J) X phi))
      alpha :=
  D.comp_equivalent

end SameCoverCartesianFactorizationData

end LocallyDefinedHomRepresentativeOver

namespace LocallyDefinedHomTotal

/-- Source stage 2.6 in the exact local form suggested by the Stacks proof.

This is deliberately more concrete than `RawSourceCartesianFactorizationFrontier`: existence must
be proved by constructing the factor on the same cover as `alpha`, and uniqueness is still the raw
representative uniqueness obtained from cartesian uniqueness on common refinements.  No universe or
owner resizing is hidden here. -/
structure RawSourceCartesianSameCoverFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Local existence: factor every local arrow of `alpha` through `phi` and prove the resulting
  local factors match on overlaps. -/
  sameCoverFactorization :
    ∀ ⦃x y z : X.S⦄ (phi : x ⟶ y),
      X.p.IsStronglyCartesian (X.p.map phi) phi →
      ∀ (g : X.p.obj z ⟶ X.p.obj x)
        (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)),
        LocallyDefinedHomRepresentativeOver.SameCoverCartesianFactorizationData
          (J := J) phi g alpha
  /-- Raw uniqueness: any two raw factors whose composites represent `alpha` agree after common
  refinement.  This is the source proof's uniqueness-by-cartesianness argument before passing to
  the plus quotient. -/
  sameCoverUniqueness :
    ∀ ⦃x y z : X.S⦄ (phi : x ⟶ y),
      X.p.IsStronglyCartesian (X.p.map phi) phi →
      ∀ (g : X.p.obj z ⟶ X.p.obj x)
        (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
        (beta beta' : LocallyDefinedHomRepresentativeOver (J := J) X g),
        LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
          (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta
            (ordinaryHomToRepresentativeOver (J := J) X phi))
          alpha →
        LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
          (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta'
            (ordinaryHomToRepresentativeOver (J := J) X phi))
          alpha →
        LocallyDefinedHomRepresentativeOver.Equivalent (J := J) beta' beta

namespace RawSourceCartesianSameCoverFrontier

/-- The same-cover source frontier gives the raw representative factorization frontier used by
the later owner-transport lemmas. -/
theorem toRawSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : RawSourceCartesianSameCoverFrontier (J := J) X) :
    RawSourceCartesianFactorizationFrontier (J := J) X where
  factorization := by
    intro x y z phi hphi g alpha
    let D := H.sameCoverFactorization phi hphi g alpha
    refine ⟨D.toRepresentative, ?_, ?_⟩
    · exact D.toRepresentative_comp_equivalent
    · intro beta hbeta
      exact H.sameCoverUniqueness phi hphi g alpha D.toRepresentative beta
        D.toRepresentative_comp_equivalent hbeta

/-- The same-cover source frontier gives the literal source-form cartesian factorization
frontier for locally-defined morphisms. -/
theorem toStrictSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : RawSourceCartesianSameCoverFrontier (J := J) X) :
    StrictSourceCartesianFactorizationFrontier (J := J) X :=
  H.toRawSourceCartesianFactorizationFrontier.toStrictSourceCartesianFactorizationFrontier

/-- The same-cover source frontier gives the owner-level Hom-lift cartesian factorization
frontier. -/
theorem toSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : RawSourceCartesianSameCoverFrontier (J := J) X) :
    SourceCartesianFactorizationFrontier (J := J) X :=
  H.toStrictSourceCartesianFactorizationFrontier.toSourceCartesianFactorizationFrontier

/-- The same-cover source frontier gives the cartesian frontier used to make the source
projection fibred. -/
theorem toSourceCartesianFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : RawSourceCartesianSameCoverFrontier (J := J) X) :
    SourceCartesianFrontier (J := J) X :=
  H.toStrictSourceCartesianFactorizationFrontier.toSourceCartesianFrontier

end RawSourceCartesianSameCoverFrontier

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
