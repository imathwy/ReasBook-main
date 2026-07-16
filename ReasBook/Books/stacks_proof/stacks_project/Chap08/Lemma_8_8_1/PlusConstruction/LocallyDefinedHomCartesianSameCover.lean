import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCartesianCancellation

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
namespace LocallyDefinedHomTotal

/-- Source stage 2.6, split at the functional boundary used in the Stacks proof.

The existing `RawSourceCartesianSameCoverFrontier` asks for the finished same-cover
factorization data.  This finer frontier records the proof in the source order:

* choose, for each member of the cover of `alpha`, the local factor through the cartesian arrow;
* prove these factors satisfy the matching condition on overlaps;
* prove that composing the resulting same-cover representative with `phi` recovers `alpha`;
* prove uniqueness after passing to a common refinement.

This file deliberately stays on the raw representative surface.  It does not introduce any
same-owner conversion or universe resizing bridge. -/
structure SameCoverLocalFactorizationFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- The local factors `beta_i` in the source proof, indexed by the cover of `alpha`. -/
  localFactor :
    ∀ ⦃x y z : X.S⦄ (phi : x ⟶ y),
      X.p.IsStronglyCartesian (X.p.map phi) phi →
      ∀ (g : X.p.obj z ⟶ X.p.obj x)
        (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)),
        ∀ I : alpha.cover.Arrow,
          (locallyDefinedHomSaturatedPresheaf X g).obj (op I.Y)
  /-- The overlap check for the local factors `beta_i`. -/
  localFactor_compatible :
    ∀ ⦃x y z : X.S⦄ (phi : x ⟶ y)
      (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
      (g : X.p.obj z ⟶ X.p.obj x)
      (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)),
      ∀ R : alpha.cover.Relation,
        (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₁.op
            (localFactor phi hphi g alpha (alpha.cover.shape.fst R)) =
          (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₂.op
            (localFactor phi hphi g alpha (alpha.cover.shape.snd R))
  /-- The local factor family, composed with the ordinary representative of `phi`, represents the
  original raw locally-defined morphism `alpha`. -/
  localFactor_comp_equivalent :
    ∀ ⦃x y z : X.S⦄ (phi : x ⟶ y)
      (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
      (g : X.p.obj z ⟶ X.p.obj x)
      (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)),
      let betaFamily : Meq (locallyDefinedHomSaturatedPresheaf X g) alpha.cover :=
        ⟨fun I => localFactor phi hphi g alpha I,
          localFactor_compatible phi hphi g alpha⟩
      LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
        (LocallyDefinedHomRepresentativeOver.composeOver (J := J)
          ({ cover := alpha.cover
             family := betaFamily } :
            LocallyDefinedHomRepresentativeOver (J := J) X g)
          (ordinaryHomToRepresentativeOver (J := J) X phi))
        alpha
  /-- The source proof's uniqueness statement: any two raw factors with composite `alpha` agree
  after common refinement. -/
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

namespace SameCoverLocalFactorization

/-- The matching-family package built from the explicit pointwise factors, once the overlap
condition has been proved. -/
noncomputable def pointwiseFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (hcompatible :
      ∀ R : alpha.cover.Relation,
        (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₁.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.fst R)) =
          (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₂.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.snd R))) :
    Meq (locallyDefinedHomSaturatedPresheaf X g) alpha.cover :=
  ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I, hcompatible⟩

@[simp]
theorem pointwiseFamily_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (hcompatible :
      ∀ R : alpha.cover.Relation,
        (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₁.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.fst R)) =
          (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₂.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.snd R)))
    (I : alpha.cover.Arrow) :
    pointwiseFamily (J := J) phi hphi g alpha hcompatible I =
      pointwiseLocalFactor (J := J) phi hphi g alpha I :=
  rfl

/-- Source stage 2.6 after the pointwise construction and composite check have been fixed.

The overlap condition and the comparison with `alpha` are now proved directly for the constructed
pointwise factors.  The remaining proof frontier faithful to the source text is the raw
same-cover uniqueness statement on common refinements. -/
structure PointwiseChecks
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- The source proof's uniqueness statement after the explicit local factor construction. -/
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

namespace PointwiseChecks

/-- Package the explicit pointwise construction plus the remaining source checks as the
source-order same-cover frontier. -/
noncomputable def toLocalFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : PointwiseChecks (J := J) X) :
    SameCoverLocalFactorizationFrontier (J := J) X where
  localFactor := by
    intro x y z phi hphi g alpha I
    exact pointwiseLocalFactor (J := J) phi hphi g alpha I
  localFactor_compatible := by
    intro x y z phi hphi g alpha
    exact pointwiseLocalFactor_compatible (J := J) phi hphi g alpha
  localFactor_comp_equivalent := by
    intro x y z phi hphi g alpha
    simpa [pointwiseFamily] using
      pointwiseLocalFactor_comp_equivalent_of_compatible (J := J) phi hphi g alpha
        (pointwiseLocalFactor_compatible (J := J) phi hphi g alpha)
  sameCoverUniqueness := H.sameCoverUniqueness

end PointwiseChecks

/-- The completed source stage-2.6 pointwise checks: overlap compatibility, composite recovery,
and raw uniqueness are all proved on the raw representative surface. -/
noncomputable def pointwiseChecks
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    PointwiseChecks (J := J) X where
  sameCoverUniqueness := by
    intro x y z phi hphi g alpha beta beta' hbeta hbeta'
    exact pointwiseLocalFactor_sameCoverUniqueness (J := J)
      phi hphi g alpha beta beta' hbeta hbeta'

/-- The completed source-order same-cover local factorization frontier. -/
noncomputable def pointwiseLocalFactorizationFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    SameCoverLocalFactorizationFrontier (J := J) X :=
  (pointwiseChecks (J := J) X).toLocalFactorizationFrontier

end SameCoverLocalFactorization

namespace SameCoverLocalFactorizationFrontier

/-- Assemble the local factors into the matching family on the original cover of `alpha`. -/
noncomputable def factorFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X)
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)) :
    Meq (locallyDefinedHomSaturatedPresheaf X g) alpha.cover :=
  ⟨fun I => H.localFactor phi hphi g alpha I,
    H.localFactor_compatible phi hphi g alpha⟩

@[simp]
theorem factorFamily_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X)
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (I : alpha.cover.Arrow) :
    H.factorFamily phi hphi g alpha I = H.localFactor phi hphi g alpha I :=
  rfl

/-- Package the source-order local-factor proof as the same-cover factorization data used by the
raw stage-2.6 frontier. -/
noncomputable def factorizationData
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X)
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)) :
    LocallyDefinedHomRepresentativeOver.SameCoverCartesianFactorizationData
      (J := J) phi g alpha where
  family := H.factorFamily phi hphi g alpha
  comp_equivalent := by
    simpa [factorFamily] using H.localFactor_comp_equivalent phi hphi g alpha

/-- The source-order local frontier is exactly enough to recover the existing same-cover raw
frontier. -/
noncomputable def toRawSourceCartesianSameCoverFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X) :
    RawSourceCartesianSameCoverFrontier (J := J) X where
  sameCoverFactorization := by
    intro x y z phi hphi g alpha
    exact H.factorizationData phi hphi g alpha
  sameCoverUniqueness := H.sameCoverUniqueness

/-- The source-order local frontier gives the raw representative factorization frontier used by
the owner-transport helpers. -/
noncomputable def toRawSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X) :
    RawSourceCartesianFactorizationFrontier (J := J) X :=
  H.toRawSourceCartesianSameCoverFrontier.toRawSourceCartesianFactorizationFrontier

/-- The source-order local frontier gives the literal source-form stage-2.6 frontier. -/
noncomputable def toStrictSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X) :
    StrictSourceCartesianFactorizationFrontier (J := J) X :=
  H.toRawSourceCartesianSameCoverFrontier.toStrictSourceCartesianFactorizationFrontier

/-- The source-order local frontier gives the owner-level Hom-lift stage-2.6 frontier. -/
noncomputable def toSourceCartesianFactorizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X) :
    SourceCartesianFactorizationFrontier (J := J) X :=
  H.toRawSourceCartesianSameCoverFrontier.toSourceCartesianFactorizationFrontier

/-- The source-order local frontier gives the cartesian frontier used for source stage 2.7. -/
noncomputable def toSourceCartesianFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SameCoverLocalFactorizationFrontier (J := J) X) :
    SourceCartesianFrontier (J := J) X :=
  H.toRawSourceCartesianSameCoverFrontier.toSourceCartesianFrontier

end SameCoverLocalFactorizationFrontier

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
