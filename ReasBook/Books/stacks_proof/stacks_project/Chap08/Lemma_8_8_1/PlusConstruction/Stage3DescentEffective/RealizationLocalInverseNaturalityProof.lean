import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseMiddleRestrictedComponents

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

/-- Pointwise restriction/naturality for the actual inverse local realization component, lifted
from the owner-faithful lower-level pull-hom law for
`rho_(a,i),(b,j)`. -/
theorem projectionDescentRealizationInverseComponent_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (hInner :
      projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw
        (J := J) hSheaf D)
    (I : S.Arrow)
    {W W' : C}
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (k : W ⟶ K.Y) (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ 𝟙 I.Y = a ≫ A.f)
    (m : W' ⟶ W) (mk : W' ⟶ K.Y) (ma : W' ⟶ A.Y)
    (hmk : m ≫ k = mk) (hma : m ≫ a = ma) :
    let hsmall : mk ≫ K.f ≫ 𝟙 I.Y = ma ≫ A.f := by
      calc
        mk ≫ K.f ≫ 𝟙 I.Y = m ≫ k ≫ K.f ≫ 𝟙 I.Y := by
          rw [← hmk]
          simp [Category.assoc]
        _ = m ≫ a ≫ A.f := by
          simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
        _ = ma ≫ A.f := by
          simpa [Category.assoc] using congrArg (fun q => q ≫ A.f) hma
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationInverseComponent (J := J)
          hSheaf D hPull hComp I K A k a h)
        m mk ma hmk hma =
      projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A mk ma hsmall := by
  dsimp only
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  let htotal : k ≫ K.f ≫ I.f = a ≫ Atot.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      k ≫ K.f ≫ I.f = (k ≫ K.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (a ≫ A.f) ≫ I.f := by rw [h]
      _ = a ≫ A.f ≫ I.f := by simp [Category.assoc]
  let hsmall : mk ≫ K.f ≫ 𝟙 I.Y = ma ≫ A.f := by
    calc
      mk ≫ K.f ≫ 𝟙 I.Y = m ≫ k ≫ K.f ≫ 𝟙 I.Y := by
        rw [← hmk]
        simp [Category.assoc]
      _ = m ≫ a ≫ A.f := by
        simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
      _ = ma ≫ A.f := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ A.f) hma
  let htotalSmall : mk ≫ K.f ≫ I.f = ma ≫ Atot.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      mk ≫ K.f ≫ I.f = (mk ≫ K.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (ma ≫ A.f) ≫ I.f := by rw [hsmall]
      _ = ma ≫ A.f ≫ I.f := by simp [Category.assoc]
  have hcomp :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K A k a h
  have hcompSmall :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K A mk ma hsmall
  rw [hcomp, hcompSmall]
  simpa [G, Atot, htotal, hsmall, htotalSmall] using
    hInner m I K k (A := Atot) a htotal mk ma hmk hma

/-- Restriction/naturality for the actual inverse local realization component, packaged as the
`HomOver.familyNaturality'` law. -/
theorem projectionDescentRealizationInverseComponent_naturality_of_inner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (hInner :
      projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw
        (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) :
    projectionDescentRealizationInverseComponentNaturalityLaw
      (J := J) hSheaf D hPull hComp I hcompat := by
  dsimp [projectionDescentRealizationInverseComponentNaturalityLaw,
    DescentCompletionObjectOver.HomOver.familyNaturality',
    projectionDescentRealizationInverseHomOver]
  intro W W' K A k a h m mk ma hmk hma
  exact
    projectionDescentRealizationInverseComponent_pullHom
      (J := J) hSheaf D hPull hComp hInner I K A k a h m mk ma hmk hma

/-- The inverse explicit middle owner bridge gives restriction/naturality for the actual inverse
local realization component. -/
theorem projectionDescentRealizationInverseComponent_naturality_of_explicitMiddle
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (hmiddle :
      projectionDescentRealizationInverseExplicitMiddlePullHomLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) :
    projectionDescentRealizationInverseComponentNaturalityLaw
      (J := J) hSheaf D hPull hComp I hcompat :=
  projectionDescentRealizationInverseComponent_naturality_of_inner
    (J := J) hSheaf D hPull hComp
    (projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw_of_explicitMiddle
      (J := J) hSheaf D hmiddle)
    I hcompat

namespace ProjectionDescentTotalCoverSourceRealizationFrontier

/-- For a source-realization frontier, an inverse explicit middle owner bridge supplies the
`HomOver.familyNaturality'` field for the componentwise inverse of `Lambda_a`. -/
theorem inverseNaturality_of_explicitMiddle
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (hmiddle :
      projectionDescentRealizationInverseExplicitMiddlePullHomLaw (J := J) hSheaf D)
    (I : S.Arrow) :
    projectionDescentRealizationInverseComponentNaturalityLaw
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I
      (projectionDescentRealizationInverseComponent_compatible
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I) :=
  projectionDescentRealizationInverseComponent_naturality_of_explicitMiddle
    (J := J) hSheaf D H.transitionPullHom H.transitionHomComp hmiddle I
    (projectionDescentRealizationInverseComponent_compatible
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I)

end ProjectionDescentTotalCoverSourceRealizationFrontier

/-- The inverse restricted-composite component frontier gives restriction/naturality for the
actual inverse local realization component. -/
theorem projectionDescentRealizationInverseComponent_naturality_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (hrestricted :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationInverseComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) :
    projectionDescentRealizationInverseComponentNaturalityLaw
      (J := J) hSheaf D hPull hComp I hcompat :=
  projectionDescentRealizationInverseComponent_naturality_of_inner
    (J := J) hSheaf D hPull hComp
    (projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw_of_restrictedComposite
      (J := J) hSheaf D hrestricted)
    I hcompat

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
