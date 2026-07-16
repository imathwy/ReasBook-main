import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseComposite

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
namespace ProjectionDescentTotalCoverSourceRealizationFrontier

/-- The total descent-completion morphism underlying the explicit local map `Lambda_I`. -/
noncomputable def explicitLocalHomAsHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (I : S.Arrow) :
    Hom (J := J)
      (pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
        I.f)
      (projectionDescentDatumObject (J := J) hSheaf D I) where
  base := 𝟙 I.Y
  components := H.componentFrontier.naturalHomOver I

/-- The total descent-completion morphism underlying the explicit local inverse of `Lambda_I`. -/
noncomputable def explicitLocalInvAsHom
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
    Hom (J := J)
      (projectionDescentDatumObject (J := J) hSheaf D I)
      (pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
        I.f) where
  base := 𝟙 I.Y
  components :=
    projectionDescentRealizationInverseNaturalHomOver
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I hcompat hnat

set_option maxHeartbeats 800000 in
/-- Total descent-completion form of `Lambda_I ; Lambda_I^{-1} = id`. -/
theorem explicitLocalHomAsHom_comp_explicitLocalInvAsHom
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
    Hom.compose (J := J) hSheaf
        (explicitLocalHomAsHom (J := J) H I)
        (explicitLocalInvAsHom (J := J) H I hcompat hnat) =
      identity (J := J)
        (pullback (J := J)
          (projectionDescentTotalCoverGluedObjectOfTransitionLaws
            (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
          I.f) := by
  refine Hom.ext_base_family
    (Hom.compose (J := J) hSheaf
      (explicitLocalHomAsHom (J := J) H I)
      (explicitLocalInvAsHom (J := J) H I hcompat hnat))
    (identity (J := J)
      (pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
        I.f)) ?_ ?_
  · simp [Hom.compose, identity, explicitLocalHomAsHom, explicitLocalInvAsHom]
  · intro W A B a b h
    simpa [Hom.compose, identity, explicitLocalHomAsHom, explicitLocalInvAsHom,
      DescentCompletionObjectOver.NaturalHomOver.compose,
      DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
      DescentCompletionObjectOver.NaturalHomOver.composeCandidate] using
      projectionDescentRealizationComponent_comp_inverse_compositionFamily
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I
        (H.componentFrontier.compatible I) (H.componentFrontier.naturality I)
        hcompat hnat A B a b h

set_option maxHeartbeats 800000 in
/-- Total descent-completion form of `Lambda_I^{-1} ; Lambda_I = id`. -/
theorem explicitLocalInvAsHom_comp_explicitLocalHomAsHom
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
    Hom.compose (J := J) hSheaf
        (explicitLocalInvAsHom (J := J) H I hcompat hnat)
        (explicitLocalHomAsHom (J := J) H I) =
      identity (J := J) (projectionDescentDatumObject (J := J) hSheaf D I) := by
  refine Hom.ext_base_family
    (Hom.compose (J := J) hSheaf
      (explicitLocalInvAsHom (J := J) H I hcompat hnat)
      (explicitLocalHomAsHom (J := J) H I))
    (identity (J := J) (projectionDescentDatumObject (J := J) hSheaf D I)) ?_ ?_
  · simp [Hom.compose, identity, explicitLocalHomAsHom, explicitLocalInvAsHom]
  · intro W K L k l h
    simpa [Hom.compose, identity, explicitLocalHomAsHom, explicitLocalInvAsHom,
      DescentCompletionObjectOver.NaturalHomOver.compose,
      DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
      DescentCompletionObjectOver.NaturalHomOver.composeCandidate] using
      projectionDescentRealizationInverseComponent_comp_realization_compositionFamily
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I
        (H.componentFrontier.compatible I) (H.componentFrontier.naturality I)
        hcompat hnat K L k l h

/-- The fibre morphism `explicitLocalHom` has the expected total morphism underneath. -/
theorem fiberInclusion_map_explicitLocalHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (I : S.Arrow) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    Functor.Fiber.fiberInclusion.map (H.explicitLocalHom I) =
      explicitLocalHomAsHom (J := J) H I := by
  rfl

/-- The fibre morphism `explicitLocalInv` has the expected total morphism underneath. -/
theorem fiberInclusion_map_explicitLocalInv
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
    Functor.Fiber.fiberInclusion.map
        (explicitLocalInv (J := J) H I hcompat hnat) =
      explicitLocalInvAsHom (J := J) H I hcompat hnat := by
  rfl

set_option maxHeartbeats 800000 in
/-- Fibre form of `Lambda_I ; Lambda_I^{-1} = id`. -/
theorem explicitLocalHom_comp_explicitLocalInv
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
    H.explicitLocalHom I ≫ explicitLocalInv (J := J) H I hcompat hnat =
      𝟙 (explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
        I.f) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  apply Functor.Fiber.hom_ext
  simpa [Functor.map_comp, fiberInclusion_map_explicitLocalHom,
    fiberInclusion_map_explicitLocalInv, category, explicitPullbackFiberObject] using
    explicitLocalHomAsHom_comp_explicitLocalInvAsHom (J := J) H I hcompat hnat

set_option maxHeartbeats 800000 in
/-- Fibre form of `Lambda_I^{-1} ; Lambda_I = id`. -/
theorem explicitLocalInv_comp_explicitLocalHom
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
    explicitLocalInv (J := J) H I hcompat hnat ≫ H.explicitLocalHom I =
      𝟙 (projectionFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  apply Functor.Fiber.hom_ext
  simpa [Functor.map_comp, fiberInclusion_map_explicitLocalHom,
    fiberInclusion_map_explicitLocalInv, category, projectionFiberObject] using
    explicitLocalInvAsHom_comp_explicitLocalHomAsHom (J := J) H I hcompat hnat

/-- Package compatible and natural inverse components into the explicit local inverse frontier. -/
noncomputable def explicitLocalInverseFrontierOfInverseData
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (hcompat :
      ∀ I : S.Arrow,
        projectionDescentRealizationInverseComponentCompatibleLaw
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I)
    (hnat :
      ∀ I : S.Arrow,
        projectionDescentRealizationInverseComponentNaturalityLaw
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I (hcompat I)) :
    ExplicitLocalInverseFrontier (J := J) H where
  inverseCompatible := hcompat
  inverseNaturality := hnat
  hom_inv_id I := explicitLocalHom_comp_explicitLocalInv (J := J) H I (hcompat I) (hnat I)
  inv_hom_id I := explicitLocalInv_comp_explicitLocalHom (J := J) H I (hcompat I) (hnat I)

/-- Build the explicit local inverse frontier from the inverse restricted-composite owner law. -/
noncomputable def explicitLocalInverseFrontierOfRestrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (hrestricted :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    ExplicitLocalInverseFrontier (J := J) H :=
  explicitLocalInverseFrontierOfInverseData (J := J) H
    (fun I =>
      projectionDescentRealizationInverseComponent_compatible
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I)
    (fun I =>
      projectionDescentRealizationInverseComponent_naturality_of_restrictedComposite
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp hrestricted I
        (projectionDescentRealizationInverseComponent_compatible
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp I))

/-- The inverse restricted-composite owner law gives the explicit local isomorphism frontier. -/
noncomputable def explicitLocalIsoFrontierOfRestrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (hrestricted :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    ExplicitLocalIsoFrontier (J := J) H :=
  (explicitLocalInverseFrontierOfRestrictedComposite (J := J) H hrestricted).toExplicitLocalIsoFrontier

/-- Outer descent compatibility for a chosen explicit local isomorphism frontier:
`Theta_ab o Lambda_a = Lambda_b` after transporting through the explicit source and target
owners. -/
abbrev explicitLocalIsoCommLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D}
    (R : ExplicitLocalIsoFrontier (J := J) H) : Prop :=
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I K : S.Arrow⦄
    (i : Y ⟶ I.Y) (k : Y ⟶ K.Y)
    (hi : i ≫ I.f = q) (hk : k ≫ K.f = q),
      ((canonicalFiberPseudofunctor P).map i.op.toLoc).toFunctor.map
          (R.localIso I).hom ≫ D.hom q i k hi hk =
        (H.realizationDescentData).hom q i k hi hk ≫
          ((canonicalFiberPseudofunctor P).map k.op.toLoc).toFunctor.map
            (R.localIso K).hom

/-- Reduced total-cover frontier from the source-text local inverse and final outer
compatibility laws. -/
noncomputable def reducedFrontierOfRestrictedCompositeAndComm
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (hrestricted :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D)
    (hcomm :
      explicitLocalIsoCommLaw (J := J)
        (explicitLocalIsoFrontierOfRestrictedComposite (J := J) H hrestricted)) :
    ProjectionDescentTotalCoverReducedFrontier (J := J) hSheaf D :=
  ((explicitLocalIsoFrontierOfRestrictedComposite (J := J) H hrestricted).toRealizationIsoFrontier
    hcomm).toReducedFrontier

end ProjectionDescentTotalCoverSourceRealizationFrontier
end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
