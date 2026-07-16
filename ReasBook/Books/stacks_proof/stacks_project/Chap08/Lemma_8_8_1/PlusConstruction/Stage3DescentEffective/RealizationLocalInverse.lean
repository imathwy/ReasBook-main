import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalIso

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
namespace DescentCompletionObject

/-- Source stage 3.13 inverse-realization helper: specialize the outer transition from the
explicit source-text owner `(a,i)` to a total-cover member `(b,j)`.

This is the canonical-pullback owner form of the inverse component
`rho_(a,i),(b,j) = theta_ab,ij`.  It is deliberately not implemented by rebuilding `(a,i)` as a
choice-based `Cover.bind` arrow. -/
noncomputable def projectionDescentOuterFiberHomFromDatumInnerToTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ((canonicalFiberPseudofunctor P).map (k ≫ K.f).op.toLoc).toFunctor.obj
        (D.obj I) ⟶
      ((canonicalFiberPseudofunctor P).map
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a).op.toLoc).toFunctor.obj
        (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A)) :=
  projectionDescentOuterFiberHom (J := J) hSheaf D
    I
    (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    (k ≫ K.f)
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (by
      calc
        (k ≫ K.f) ≫ I.f = a ≫ A.f := by simpa [Category.assoc] using h
        _ =
          projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f := by
          have hA :
              a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                  (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
                a ≫ A.f :=
            congrArg (fun q => a ≫ q)
              (projectionDescentTotalCover_fac (J := J) hSheaf D A)
          simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using hA.symm)

/-- Explicit-owner form of
`projectionDescentOuterFiberHomFromDatumInnerToTotalCover`. -/
noncomputable def projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I)
        (k ≫ K.f) ⟶
      explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eK :=
    projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I (k ≫ K.f)
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  exact eK.hom ≫
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h ≫
      eA.inv

/-- The explicit-owner inverse-realization transition is vertical over `W`. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    letI := category (J := J) hSheaf
    (projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
      hSheaf D I K k A a h).1.base = 𝟙 W := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
      hSheaf D I K k A a h
  letI : P.IsHomLift (𝟙 W) α.1 := α.2
  have hfac := IsHomLift.fac' P (𝟙 W) α.1
  simpa [P, projectionFunctor, α] using hfac

/-- Component of `rho_(a,i),(b,j)` on the two explicit pullback covers. -/
noncomputable def projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k ≫ K.f)).restrictedLocalObject
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k) (𝟙 W) ⟶
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) (𝟙 W) := by
  letI := category (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
      hSheaf D I K k A a h
  have hbase :
      α.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K k A a h
  exact α.1.components.toHomOver.family
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    (𝟙 W) (𝟙 W)
    (by
      rw [hbase]
      dsimp [projectionDescentDatumExplicitPullbackArrow,
        projectionDescentTotalCoverExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      calc
        𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
        _ = 𝟙 W ≫ 𝟙 W := rfl)

/-- The source-text inverse component
`Lambda_a^{-1}_{i,(b,j)} := rho_(a,i),(b,j)`, with all owner transports explicit. -/
noncomputable def projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject K k ⟶
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D A) a :=
  (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).hom ≫
    (projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D I K k).inv ≫
    projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover (J := J)
      hSheaf D I K k A a h ≫
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D A a).hom ≫
    (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv

/-- The component formula for the inverse local realization map
`X_a -> (glued X)|_{T_a}`, before the compatibility field is supplied. -/
noncomputable def projectionDescentRealizationInverseComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    {W : C} (k : W ⟶ K.Y) (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ 𝟙 I.Y = a ≫ A.f) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject K k ⟶
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).restrictedLocalObject A a := by
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  have htotal : k ≫ K.f ≫ I.f = a ≫ Atot.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      k ≫ K.f ≫ I.f = (k ≫ K.f ≫ 𝟙 I.Y) ≫ I.f := by simp [Category.assoc]
      _ = (a ≫ A.f) ≫ I.f := by rw [h]
      _ = a ≫ A.f ≫ I.f := by simp [Category.assoc]
  simpa [G, Atot, projectionDescentTotalCoverGluedObjectOfTransitionLaws,
    projectionDescentTotalCoverGluedObjectOfLaws,
    projectionDescentTotalCoverGluedObjectOverOfLaws,
    projectionDescentTotalCoverGluedDatumOfLaws,
    projectionDescentTotalCoverGluedLocalObject,
    DescentCompletionObjectOver.pullback,
    DescentCompletionObjectOver.restrictedLocalObject,
    DescentCompletionObjectOver.pullbackCoverBaseArrow] using
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k Atot a htotal

/-- Compatibility obligation for the inverse local realization component. -/
def projectionDescentRealizationInverseComponentCompatibleLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow) : Prop :=
  let Source := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let Target :=
    DescentCompletionObjectOver.pullback (J := J)
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object I.f
  ∀ {W : C} (K₁ K₂ : Source.cover.Arrow) (A₁ A₂ : Target.cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (a₁ : W ⟶ A₁.Y) (a₂ : W ⟶ A₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (hA : a₁ ≫ A₁.f = a₂ ≫ A₂.f)
    (h₁ : k₁ ≫ K₁.f ≫ 𝟙 I.Y = a₁ ≫ A₁.f)
    (h₂ : k₂ ≫ K₂.f ≫ 𝟙 I.Y = a₂ ≫ A₂.f),
      (Source.overlapIso k₁ k₂ hK).hom ≫
          projectionDescentRealizationInverseComponent (J := J)
            hSheaf D hPull hComp I K₂ A₂ (W := W) k₂ a₂ h₂ =
        projectionDescentRealizationInverseComponent (J := J)
            hSheaf D hPull hComp I K₁ A₁ (W := W) k₁ a₁ h₁ ≫
          (Target.overlapIso a₁ a₂ hA).hom

/-- Inverse local realization morphism over `T_a`, conditional on component compatibility. -/
noncomputable def projectionDescentRealizationInverseHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) :
    DescentCompletionObjectOver.HomOver (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f)
      (𝟙 I.Y) where
  family K A k a h :=
    projectionDescentRealizationInverseComponent (J := J)
      hSheaf D hPull hComp I K A k a h
  compatible := by
    intro W K₁ K₂ A₁ A₂ k₁ k₂ a₁ a₂ hK hA h₁ h₂
    exact hcompat K₁ K₂ A₁ A₂ k₁ k₂ a₁ a₂ hK hA h₁ h₂

/-- Naturality obligation for the inverse local realization map. -/
def projectionDescentRealizationInverseComponentNaturalityLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) : Prop :=
  DescentCompletionObjectOver.HomOver.familyNaturality' (J := J)
    (projectionDescentRealizationInverseHomOver
      (J := J) hSheaf D hPull hComp I hcompat)

/-- Inverse local realization morphism over `T_a`, bundled with naturality. -/
noncomputable def projectionDescentRealizationInverseNaturalHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I)
    (hnat :
      projectionDescentRealizationInverseComponentNaturalityLaw
        (J := J) hSheaf D hPull hComp I hcompat) :
    DescentCompletionObjectOver.NaturalHomOver (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f)
      (𝟙 I.Y) where
  toHomOver :=
    projectionDescentRealizationInverseHomOver
      (J := J) hSheaf D hPull hComp I hcompat
  naturality := hnat

namespace ProjectionDescentTotalCoverSourceRealizationFrontier

/-- The explicit-owner inverse of `Lambda_a`, bundled as a fibre morphism. -/
noncomputable def explicitLocalInv
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I)
    (hnat :
      projectionDescentRealizationInverseComponentNaturalityLaw
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I hcompat) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    projectionFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I) ⟶
      explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
        I.f := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let G :=
    projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp
  let m : Hom (J := J)
      (projectionDescentDatumObject (J := J) hSheaf D I)
      (pullback (J := J) G I.f) := {
    base := 𝟙 I.Y
    components :=
      projectionDescentRealizationInverseNaturalHomOver
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I hcompat hnat }
  letI : P.IsHomLift (𝟙 I.Y) m := by
    simpa [P, projectionFunctor, m]
      using (inferInstance : P.IsHomLift (P.map m) m)
  exact Functor.Fiber.homMk P I.Y m

/-- Source-faithful inverse frontier for proving the explicit `Lambda_a` is an isomorphism.

The component formula for the inverse is fixed by `explicitLocalInv`; the remaining fields are
exactly the source-text checks that the two componentwise composites reduce to identity by the
`rho` cocycle/self laws. -/
structure ExplicitLocalInverseFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) where
  inverseCompatible :
    ∀ I : S.Arrow,
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I
  inverseNaturality :
    ∀ I : S.Arrow,
      projectionDescentRealizationInverseComponentNaturalityLaw
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I
        (inverseCompatible I)
  hom_inv_id :
    ∀ I : S.Arrow,
      letI := category (J := J) hSheaf
      let P := projectionFunctor (J := J) hSheaf
      haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
      H.explicitLocalHom I ≫
          explicitLocalInv (J := J) H I (inverseCompatible I) (inverseNaturality I) =
        𝟙 (explicitPullbackFiberObject (J := J) hSheaf
          (projectionDescentTotalCoverGluedObjectOfTransitionLaws
            (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
          I.f)
  inv_hom_id :
    ∀ I : S.Arrow,
      letI := category (J := J) hSheaf
      let P := projectionFunctor (J := J) hSheaf
      haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
      explicitLocalInv (J := J) H I (inverseCompatible I) (inverseNaturality I) ≫
          H.explicitLocalHom I =
        𝟙 (projectionFiberObject (J := J) hSheaf
          (projectionDescentDatumObject (J := J) hSheaf D I))

namespace ExplicitLocalInverseFrontier

/-- Package a source-text inverse of `Lambda_a` as the local explicit isomorphism frontier. -/
noncomputable def toExplicitLocalIsoFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D}
    (R : ExplicitLocalInverseFrontier (J := J) H) :
    ExplicitLocalIsoFrontier (J := J) H where
  localExplicitIso I := by
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    refine
      { hom := H.explicitLocalHom I
        inv := explicitLocalInv (J := J) H I (R.inverseCompatible I) (R.inverseNaturality I)
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · exact R.hom_inv_id I
    · exact R.inv_hom_id I
  localExplicitIso_hom I := rfl

end ExplicitLocalInverseFrontier

end ProjectionDescentTotalCoverSourceRealizationFrontier
end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
