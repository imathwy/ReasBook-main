import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.NaiveConstruction
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage2HomSheafBridge
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseTotal
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage2HomSheafTruePlusFrontier

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

/-- Source stage 2.8 split into the two concrete facts needed to identify the current
conjugated pointwise model with the genuine plus presheaf.

The field `objEquiv` is the source-text statement at a single test object `T -> U`: a fixed-base
locally-defined morphism over `T` is a plus section over the same slice test object.  The field
`map_naturality` is the remaining restriction compatibility.  This structure deliberately keeps
both facts explicit instead of converting them into a definitional equality of owners. -/
structure SourceStage2TruePlusObjectwiseFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  objEquiv :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U)
      (T : Over U),
      sourceStage2HomSheafModelObj (J := J) X x y T ≃
        (sourceStage2TruePlusPresheaf (J := J) X x y).obj (op T)
  map_naturality :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U)
      {T T' : Over U} (f : T ⟶ T')
      (s : sourceStage2HomSheafModelObj (J := J) X x y T'),
      objEquiv U x y T
          ((sourceStage2HomSheafModelPresheaf (J := J) X x y).map f.op s) =
        (sourceStage2TruePlusPresheaf (J := J) X x y).map f.op
          (objEquiv U x y T' s)

namespace SourceStage2TruePlusObjectwiseFrontier

/-- The objectwise comparison plus its restriction compatibility upgrades to the presheaf-level
true-plus comparison frontier used by the draft-input layer. -/
noncomputable def toComparisonFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2TruePlusObjectwiseFrontier (J := J) X) :
    SourceStage2TruePlusComparisonFrontier (J := J) X where
  modelIso := fun U x y => by
    refine NatIso.ofComponents
      (fun T => (H.objEquiv U x y T.unop).toIso) ?_
    intro T T' f
    funext s
    exact H.map_naturality U x y f.unop s

/-- Post-quotient objectwise stage 2.8 data gives the true-plus bridge required by the
plus-plus construction. -/
noncomputable def toSourceStage2Bridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H :
      SourceStage2TruePlusObjectwiseFrontier
        (J := J) (separatedQuotientStage (J := J) X).quotient) :
    SourceStage2HomSheafBridge (J := J) X :=
  H.toComparisonFrontier.toSourceStage2Bridge

end SourceStage2TruePlusObjectwiseFrontier

end LocallyDefinedHomTotal

/-- Source-text combined stage 3.13 frontier for the total-cover transition components and the
local realization maps `Lambda_a`.  The final descent-datum isomorphism is still the explicit
`realizesObligation` of the underlying frontier. -/
abbrev SourceTextNaiveStage3RealizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S) :=
  DescentCompletionObject.ProjectionDescentTotalCoverSourceRealizationFrontier
    (J := J) hSheaf D

namespace SourceTextNaiveStage3RealizationFrontier

/-- Package the two source-text restricted-composite component calculations: the total-cover
transition `rho_(ai)(bj)` and the local realization component
`Lambda_a,(b,j),i = rho_(b,j),(a,i)`. -/
noncomputable def ofRestrictedComposites
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S)
    (hTransition :
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D)
    (hRealization :
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    SourceTextNaiveStage3RealizationFrontier (J := J) hSheaf D where
  transitionRestrictedComposite := hTransition
  realizationRestrictedComposite := hRealization

end SourceTextNaiveStage3RealizationFrontier

/-- Source-text local-isomorphism frontier before the outer descent compatibility check:
`Lambda_a` is an isomorphism on explicit pullback owners, with the forward arrow pinned to the
constructed component family `rho_(b,j),(a,i)`. -/
abbrev SourceTextNaiveStage3ExplicitLocalIsoFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S}
    (H : SourceTextNaiveStage3RealizationFrontier (J := J) hSheaf D) :=
  DescentCompletionObject.ProjectionDescentTotalCoverSourceRealizationFrontier.ExplicitLocalIsoFrontier
    (J := J) H

/-- Source-text outer compatibility law for the transported local isomorphisms:
`Theta_ab o Lambda_a = Lambda_b`. -/
abbrev SourceTextNaiveStage3ExplicitLocalIsoCommLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S}
    {H : SourceTextNaiveStage3RealizationFrontier (J := J) hSheaf D}
    (R : SourceTextNaiveStage3ExplicitLocalIsoFrontier (J := J) H) :=
  DescentCompletionObject.ProjectionDescentTotalCoverSourceRealizationFrontier.explicitLocalIsoCommLaw
    (J := J) R

namespace SourceTextNaiveStage3RealizationFrontier

/-- The source-text component conditions for `rho`, `Lambda`, `Lambda^{-1}`, and
`Theta_ab o Lambda_a = Lambda_b` supply the reduced total-cover frontier for stage 3.13. -/
noncomputable def reducedTotalCoverFrontierOfRestrictedCompositesAndComm
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S)
    (hTransition :
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D)
    (hRealization :
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
        (J := J) hSheaf D)
    (hInverse :
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D)
    (hcomm :
      let H :=
        ofRestrictedComposites (J := J) hSheaf D hTransition hRealization
      let R :=
        DescentCompletionObject.ProjectionDescentTotalCoverSourceRealizationFrontier.explicitLocalIsoFrontierOfRestrictedComposite
          (J := J) H hInverse
      SourceTextNaiveStage3ExplicitLocalIsoCommLaw (J := J) R) :
    DescentCompletionObject.ProjectionDescentTotalCoverReducedFrontier (J := J) hSheaf D :=
  let H := ofRestrictedComposites (J := J) hSheaf D hTransition hRealization
  DescentCompletionObject.ProjectionDescentTotalCoverSourceRealizationFrontier.reducedFrontierOfRestrictedCompositeAndComm
    (J := J) H hInverse hcomm

end SourceTextNaiveStage3RealizationFrontier

/-- Coverwise source-text transition restricted-composite law for stage 3.13. -/
abbrev SourceTextNaiveStage3CoverwiseTransitionRestrictedCompositeLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    Prop :=
  ∀ (U : C) (S : J.Cover U)
    (D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S),
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D

/-- Coverwise source-text restricted-composite law for the local realization maps `Lambda_a`. -/
abbrev SourceTextNaiveStage3CoverwiseRealizationRestrictedCompositeLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    Prop :=
  ∀ (U : C) (S : J.Cover U)
    (D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S),
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
        (J := J) hSheaf D

/-- Coverwise source-text restricted-composite law for the inverse local realization maps. -/
abbrev SourceTextNaiveStage3CoverwiseInverseRestrictedCompositeLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    Prop :=
  ∀ (U : C) (S : J.Cover U)
    (D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S),
      DescentCompletionObject.projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D

/-- Coverwise source-text final compatibility law
`Theta_ab o Lambda_a = Lambda_b`, stated after the explicit local isomorphism is built from the
restricted-composite inverse components. -/
abbrev SourceTextNaiveStage3CoverwiseExplicitLocalIsoCommLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    (hTransition :
      SourceTextNaiveStage3CoverwiseTransitionRestrictedCompositeLaw (J := J) hSheaf)
    (hRealization :
      SourceTextNaiveStage3CoverwiseRealizationRestrictedCompositeLaw (J := J) hSheaf)
    (hInverse :
      SourceTextNaiveStage3CoverwiseInverseRestrictedCompositeLaw (J := J) hSheaf) :
    Prop :=
  ∀ (U : C) (S : J.Cover U)
    (D : DescentCompletionObject.ProjectionDescentDatum (J := J) hSheaf S),
      let H :=
        SourceTextNaiveStage3RealizationFrontier.ofRestrictedComposites
          (J := J) hSheaf D (hTransition U S D) (hRealization U S D)
      let R :=
        DescentCompletionObject.ProjectionDescentTotalCoverSourceRealizationFrontier.explicitLocalIsoFrontierOfRestrictedComposite
          (J := J) H (hInverse U S D)
      SourceTextNaiveStage3ExplicitLocalIsoCommLaw (J := J) R

namespace SourceTextNaiveStage3RealizationFrontier

/-- Coverwise reduced stage 3.13 frontier from the source-text component laws for `rho`,
`Lambda`, `Lambda^{-1}`, and the final outer descent compatibility square. -/
noncomputable def coverwiseReducedTotalCoverFrontierOfRestrictedCompositesAndComm
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (hTransition :
      SourceTextNaiveStage3CoverwiseTransitionRestrictedCompositeLaw (J := J) hSheaf)
    (hRealization :
      SourceTextNaiveStage3CoverwiseRealizationRestrictedCompositeLaw (J := J) hSheaf)
    (hInverse :
      SourceTextNaiveStage3CoverwiseInverseRestrictedCompositeLaw (J := J) hSheaf)
    (hcomm :
      SourceTextNaiveStage3CoverwiseExplicitLocalIsoCommLaw
        (J := J) hTransition hRealization hInverse) :
    DescentCompletionObject.ProjectionFunctorCoverwiseReducedDescentEffectiveFrontier
      (J := J) hSheaf where
  reducedTotalCover U S D :=
    reducedTotalCoverFrontierOfRestrictedCompositesAndComm
      (J := J) hSheaf D
      (hTransition U S D)
      (hRealization U S D)
      (hInverse U S D)
      (hcomm U S D)

end SourceTextNaiveStage3RealizationFrontier

/-- Source-order package for the draft proof of Chap08 Lemma 8.8.1.

This is the small interface corresponding to the end of the Stacks construction:

* stage 2.8 supplies Hom sheaves for the locally-defined-Hom plus construction;
* stage 3.12 supplies Hom sheaves for the descent-object projection;
* stage 3.13 supplies effectivity by the total-cover construction.

The result deliberately stops at the mixed-owner construction.  Converting this mixed owner to the
same-owner `NaiveStackificationConstruction` is the separate universe/owner bridge. -/
structure SourceTextPlusPlusConstruction
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Source stage 2.8: locally-defined Hom presheaves are sheaves. -/
  stage2HomSheaves :
    LocallyDefinedHomTotal.pointwiseSourceHomSheavesObligation
      (J := J) (separatedQuotientStage (J := J) X).quotient
  /-- Hom-sheaf input used to define morphism composition in the descent-object completion. -/
  stage3HomSheaves :
    DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J)
      (LocallyDefinedHomTotal.pointwiseSourceHomSheafificationMixedAssembly
        (J := J) (separatedQuotientStage (J := J) X).quotient stage2HomSheaves).sheafified
  /-- Source stage 3.12: Hom presheaves of the completed projection are sheaves. -/
  stage3ProjectionHomSheaves :
    DescentCompletionObject.projectionFunctorHomPresheavesAreSheaves
      (J := J) stage3HomSheaves
  /-- Source stage 3.13: every coverwise descent datum is realized by the total-cover object. -/
  stage3TotalCover :
    DescentCompletionObject.ProjectionFunctorCoverwiseDescentEffectiveFrontier
      (J := J) stage3HomSheaves

namespace SourceTextPlusPlusConstruction

/-- Assemble the source-order package from the explicit stage-2 Hom-sheaf bridge plus the
stage-3 source frontiers. -/
noncomputable def ofStage2BridgeAndStage3
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (Bstage2 : LocallyDefinedHomTotal.SourceStage2HomSheafBridge (J := J) X)
    (hStage3Hom :
      DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J)
        (LocallyDefinedHomTotal.pointwiseSourceHomSheafificationMixedAssembly
          (J := J) (separatedQuotientStage (J := J) X).quotient
          (LocallyDefinedHomTotal.sourceStage2HomSheavesObligation_of_bridge
            (J := J) Bstage2)).sheafified)
    (hProjectionHom :
      DescentCompletionObject.projectionFunctorHomPresheavesAreSheaves
        (J := J) hStage3Hom)
    (Htotal :
      DescentCompletionObject.ProjectionFunctorCoverwiseDescentEffectiveFrontier
        (J := J) hStage3Hom) :
    SourceTextPlusPlusConstruction (J := J) X where
  stage2HomSheaves :=
    LocallyDefinedHomTotal.sourceStage2HomSheavesObligation_of_bridge
      (J := J) Bstage2
  stage3HomSheaves := hStage3Hom
  stage3ProjectionHomSheaves := hProjectionHom
  stage3TotalCover := Htotal

/-- Convert the source-order proof package into the current mixed-owner naive construction. -/
noncomputable def toMixedConstruction
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : SourceTextPlusPlusConstruction (J := J) X) :
    SourceNaivePlusPlusMixedConstruction (J := J) X :=
  SourceNaivePlusPlusMixedConstruction.ofPointwiseStage2AndTotalCoverFrontier
    (J := J) X S.stage2HomSheaves S.stage3HomSheaves
    S.stage3ProjectionHomSheaves S.stage3TotalCover

end SourceTextPlusPlusConstruction

/-- Source-order plus-plus construction specialized to a Cat-valued co-Grothendieck model. -/
abbrev CatValuedSourceTextPlusPlusConstruction
    (F : Cᵒᵖ ⥤ Cat.{vX, uX}) :=
  SourceTextPlusPlusConstruction (J := J) (catValuedCoGrothendieckModel F)

/-- The mixed-owner construction determined by a Cat-valued source-order proof package. -/
noncomputable def CatValuedSourceTextPlusPlusConstruction.toMixedConstruction
    {F : Cᵒᵖ ⥤ Cat.{vX, uX}}
    (S : CatValuedSourceTextPlusPlusConstruction (J := J) F) :
    CatValuedSourceNaivePlusPlusMixedConstruction (J := J) F :=
  SourceTextPlusPlusConstruction.toMixedConstruction (J := J) S

/-- The explicit unresolved owner bridge.

The parameter `M` keeps the mixed-owner source construction visible.  A proof of this structure must
produce the corresponding same-owner `NaiveStackificationConstruction`; no definitional owner
identification is asserted here. -/
structure CatValuedSourceNaivePlusPlusSameOwnerBridge
    (F : Cᵒᵖ ⥤ Cat.{vX, uX})
    (M : CatValuedSourceNaivePlusPlusMixedConstruction (J := J) F) where
  /-- Same-owner construction obtained from the mixed-owner source construction. -/
  sameOwner : CatValuedNaiveStackificationConstruction (J := J) F

/-- Owner bridge needed after the source-order package has been assembled. -/
abbrev CatValuedSourceTextSameOwnerBridge
    (F : Cᵒᵖ ⥤ Cat.{vX, uX})
    (S : CatValuedSourceTextPlusPlusConstruction (J := J) F) :=
  CatValuedSourceNaivePlusPlusSameOwnerBridge (J := J) F
    (CatValuedSourceTextPlusPlusConstruction.toMixedConstruction (J := J) S)

/-- Once the mixed-owner construction has been converted to the same-owner interface, the usual
stackification existence statement follows. -/
theorem catPseudofunctorPlusPlusStackificationExists_of_mixedOwnerBridge
    (F : Cᵒᵖ ⥤ Cat.{vX, uX})
    (M : CatValuedSourceNaivePlusPlusMixedConstruction (J := J) F)
    (B : CatValuedSourceNaivePlusPlusSameOwnerBridge (J := J) F M) :
    ∃ Y : StackOver J,
      ∃ G :
        FibredCategoryOver.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')) ⟶ Y,
        FibredCategoryMor.IsStackification G := by
  simpa [catValuedCoGrothendieckModel] using
    catValued_stackification_exists_of_naiveConstruction (J := J) F B.sameOwner

/-- Source-order version of the previous theorem: the only remaining non-source-text input is the
same-owner bridge for the mixed-owner construction produced from the draft stages. -/
theorem catPseudofunctorPlusPlusStackificationExists_of_sourceTextBridge
    (F : Cᵒᵖ ⥤ Cat.{vX, uX})
    (S : CatValuedSourceTextPlusPlusConstruction (J := J) F)
    (B : CatValuedSourceTextSameOwnerBridge (J := J) F S) :
    ∃ Y : StackOver J,
      ∃ G :
        FibredCategoryOver.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')) ⟶ Y,
        FibredCategoryMor.IsStackification G :=
  catPseudofunctorPlusPlusStackificationExists_of_mixedOwnerBridge
    (J := J) F
    (CatValuedSourceTextPlusPlusConstruction.toMixedConstruction (J := J) S) B

/-- Source-text inputs where stage 3.13 is supplied by the four component laws appearing in the
draft: the total-cover transition components `rho`, the realization components `Lambda`, the
inverse realization components `Lambda^{-1}`, and the final outer descent compatibility
`Theta_ab o Lambda_a = Lambda_b`.

The final same-owner bridge is deliberately not a field here.  This package only converts the
source's component-level proof surface into the source-order construction. -/
structure SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Source stage 2.8 as objectwise plus sections plus restriction naturality. -/
  stage2Objectwise :
    LocallyDefinedHomTotal.SourceStage2TruePlusObjectwiseFrontier
      (J := J) (separatedQuotientStage (J := J) X).quotient
  /-- Stage 3 Hom-sheaf input for composition in the descent-object completion. -/
  stage3Hom :
    DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J)
      (LocallyDefinedHomTotal.pointwiseSourceHomSheafificationMixedAssembly
        (J := J) (separatedQuotientStage (J := J) X).quotient
        (LocallyDefinedHomTotal.sourceStage2HomSheavesObligation_of_bridge
          (J := J)
          (LocallyDefinedHomTotal.SourceStage2TruePlusObjectwiseFrontier.toSourceStage2Bridge
            (J := J) stage2Objectwise))).sheafified
  /-- Source stage 3.12. -/
  stage3ProjectionHom :
    DescentCompletionObject.projectionFunctorHomPresheavesAreSheaves
      (J := J) stage3Hom
  /-- Component law for the total-cover transitions `rho_(ai),(bj)`. -/
  stage3Transition :
    SourceTextNaiveStage3CoverwiseTransitionRestrictedCompositeLaw (J := J) stage3Hom
  /-- Component law for the local realization maps `Lambda_a`. -/
  stage3Realization :
    SourceTextNaiveStage3CoverwiseRealizationRestrictedCompositeLaw (J := J) stage3Hom
  /-- Component law for the inverse local realization maps `Lambda_a^{-1}`. -/
  stage3Inverse :
    SourceTextNaiveStage3CoverwiseInverseRestrictedCompositeLaw (J := J) stage3Hom
  /-- Final compatibility law `Theta_ab o Lambda_a = Lambda_b`. -/
  stage3Comm :
    SourceTextNaiveStage3CoverwiseExplicitLocalIsoCommLaw
      (J := J) stage3Transition stage3Realization stage3Inverse

namespace SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs

/-- The reduced total-cover frontier read out from the four source-text component laws. -/
noncomputable def stage3ReducedTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (I : SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs (J := J) X) :
    DescentCompletionObject.ProjectionFunctorCoverwiseReducedDescentEffectiveFrontier
      (J := J) I.stage3Hom :=
  SourceTextNaiveStage3RealizationFrontier.coverwiseReducedTotalCoverFrontierOfRestrictedCompositesAndComm
    (J := J) I.stage3Hom I.stage3Transition I.stage3Realization
    I.stage3Inverse I.stage3Comm

/-- The full total-cover frontier read out from the reduced component-law surface. -/
noncomputable def stage3TotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (I : SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs (J := J) X) :
    DescentCompletionObject.ProjectionFunctorCoverwiseDescentEffectiveFrontier
      (J := J) I.stage3Hom :=
  I.stage3ReducedTotalCover.toTotalCoverFrontier

/-- Convert the source-text component-law package directly into the source-order construction. -/
noncomputable def toConstruction
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (I : SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs (J := J) X) :
    SourceTextPlusPlusConstruction (J := J) X :=
  SourceTextPlusPlusConstruction.ofStage2BridgeAndStage3
    (J := J)
    (LocallyDefinedHomTotal.SourceStage2TruePlusObjectwiseFrontier.toSourceStage2Bridge
      (J := J) I.stage2Objectwise)
    I.stage3Hom I.stage3ProjectionHom I.stage3TotalCover

/-- The mixed-owner construction obtained from the component-law package. -/
noncomputable def toMixedConstruction
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (I : SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs (J := J) X) :
    SourceNaivePlusPlusMixedConstruction (J := J) X :=
  I.toConstruction.toMixedConstruction

end SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs

/-- Cat-valued specialization of the source-text component-law draft inputs. -/
abbrev CatValuedSourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs
    (F : Cᵒᵖ ⥤ Cat.{vX, uX}) :=
  SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs
    (J := J) (catValuedCoGrothendieckModel F)

/-- Cat-valued component-law inputs plus the explicit same-owner bridge.

This is the current source-faithful frontier for the final existence theorem: the stage-3
descent-effectivity proof has been reduced to the four component laws, while converting the
resulting mixed-owner construction to a same-owner `NaiveStackificationConstruction` remains a
separate field. -/
structure CatValuedSourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputsWithOwner
    (F : Cᵒᵖ ⥤ Cat.{vX, uX}) where
  inputs :
    CatValuedSourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs
      (J := J) F
  sameOwner :
    CatValuedSourceTextSameOwnerBridge (J := J) F inputs.toConstruction

namespace CatValuedSourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputsWithOwner

/-- The stackification existence statement obtained from component-law source inputs plus the
explicit same-owner bridge. -/
theorem stackificationExists
    (F : Cᵒᵖ ⥤ Cat.{vX, uX})
    (I :
      CatValuedSourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputsWithOwner
        (J := J) F) :
    ∃ Y : StackOver J,
      ∃ G :
        FibredCategoryOver.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')) ⟶ Y,
        FibredCategoryMor.IsStackification G :=
  catPseudofunctorPlusPlusStackificationExists_of_sourceTextBridge
    (J := J) F I.inputs.toConstruction I.sameOwner

end CatValuedSourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputsWithOwner

/-- Source-text stage 3.13 total-cover component laws, grouped by the four pieces used in
the Stacks proof:

* `transition` is the cocycle-compatible total-cover transition `rho_(ai),(bj)`;
* `realization` is the local map `Lambda_a` with component `rho_(bj),(ai)`;
* `inverse` is the inverse local map with component `rho_(ai),(bj)`;
* `comm` is the final outer compatibility `Theta_ab o Lambda_a = Lambda_b`.

This helper only reorganizes the proof surface.  It does not identify the explicit,
canonical, or repackaged owners by definitional equality. -/
structure SourceTextStage3TotalCoverComponentLaws
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) where
  /-- Component law for the total-cover transitions `rho_(ai),(bj)`. -/
  transition :
    SourceTextNaiveStage3CoverwiseTransitionRestrictedCompositeLaw (J := J) hSheaf
  /-- Component law for the local realization maps `Lambda_a`. -/
  realization :
    SourceTextNaiveStage3CoverwiseRealizationRestrictedCompositeLaw (J := J) hSheaf
  /-- Component law for the inverse local realization maps `Lambda_a^{-1}`. -/
  inverse :
    SourceTextNaiveStage3CoverwiseInverseRestrictedCompositeLaw (J := J) hSheaf
  /-- Final compatibility law `Theta_ab o Lambda_a = Lambda_b`. -/
  comm :
    SourceTextNaiveStage3CoverwiseExplicitLocalIsoCommLaw
      (J := J) transition realization inverse

namespace SourceTextStage3TotalCoverComponentLaws

/-- Convert the four source-text component laws into the reduced stage 3.13 frontier. -/
noncomputable def toReducedTotalCoverFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    (L : SourceTextStage3TotalCoverComponentLaws (J := J) hSheaf) :
    DescentCompletionObject.ProjectionFunctorCoverwiseReducedDescentEffectiveFrontier
      (J := J) hSheaf :=
  SourceTextNaiveStage3RealizationFrontier.coverwiseReducedTotalCoverFrontierOfRestrictedCompositesAndComm
    (J := J) hSheaf L.transition L.realization L.inverse L.comm

end SourceTextStage3TotalCoverComponentLaws

/-- Source-faithful proof surface for the plus construction part of Chap08 Lemma 8.8.1.

The stage-3 descent-effectivity proof is split by function through
`SourceTextStage3TotalCoverComponentLaws`.  The final same-owner comparison is not included
here; it remains a separate owner/universe bridge. -/
structure SourceTextPlusConstructionDraft
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Source stage 2.8 as objectwise plus sections plus restriction naturality. -/
  stage2Objectwise :
    LocallyDefinedHomTotal.SourceStage2TruePlusObjectwiseFrontier
      (J := J) (separatedQuotientStage (J := J) X).quotient
  /-- Stage 3 Hom-sheaf input for composition in the descent-object completion. -/
  stage3Hom :
    DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J)
      (LocallyDefinedHomTotal.pointwiseSourceHomSheafificationMixedAssembly
        (J := J) (separatedQuotientStage (J := J) X).quotient
        (LocallyDefinedHomTotal.sourceStage2HomSheavesObligation_of_bridge
          (J := J)
          (LocallyDefinedHomTotal.SourceStage2TruePlusObjectwiseFrontier.toSourceStage2Bridge
            (J := J) stage2Objectwise))).sheafified
  /-- Source stage 3.12. -/
  stage3ProjectionHom :
    DescentCompletionObject.projectionFunctorHomPresheavesAreSheaves
      (J := J) stage3Hom
  /-- Source stage 3.13 component laws for `rho`, `Lambda`, `Lambda^{-1}`, and
  `Theta_ab o Lambda_a = Lambda_b`. -/
  stage3TotalCover :
    SourceTextStage3TotalCoverComponentLaws (J := J) stage3Hom

namespace SourceTextPlusConstructionDraft

/-- Forget the grouped stage-3 package to the existing component-law draft-input package. -/
noncomputable def toComponentDraftInputs
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (I : SourceTextPlusConstructionDraft (J := J) X) :
    SourceTextPlusPlusObjectwiseTruePlusReducedComponentDraftInputs (J := J) X where
  stage2Objectwise := I.stage2Objectwise
  stage3Hom := I.stage3Hom
  stage3ProjectionHom := I.stage3ProjectionHom
  stage3Transition := I.stage3TotalCover.transition
  stage3Realization := I.stage3TotalCover.realization
  stage3Inverse := I.stage3TotalCover.inverse
  stage3Comm := I.stage3TotalCover.comm

/-- Convert the grouped source-text draft into the source-order construction package. -/
noncomputable def toConstruction
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (I : SourceTextPlusConstructionDraft (J := J) X) :
    SourceTextPlusPlusConstruction (J := J) X :=
  I.toComponentDraftInputs.toConstruction

/-- The mixed-owner construction obtained from the grouped source-text draft. -/
noncomputable def toMixedConstruction
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (I : SourceTextPlusConstructionDraft (J := J) X) :
    SourceNaivePlusPlusMixedConstruction (J := J) X :=
  I.toConstruction.toMixedConstruction

end SourceTextPlusConstructionDraft

/-- Cat-valued specialization of the grouped source-text plus-construction draft. -/
abbrev CatValuedSourceTextPlusConstructionDraft
    (F : Cᵒᵖ ⥤ Cat.{vX, uX}) :=
  SourceTextPlusConstructionDraft (J := J) (catValuedCoGrothendieckModel F)

/-- Cat-valued grouped source-text draft plus the explicit same-owner bridge.

This is the source-faithful final frontier for the existence statement: stage 3.13 is reduced
to the four component laws, and the owner/universe comparison remains a separate field. -/
structure CatValuedSourceTextPlusConstructionDraftWithOwner
    (F : Cᵒᵖ ⥤ Cat.{vX, uX}) where
  draft :
    CatValuedSourceTextPlusConstructionDraft (J := J) F
  sameOwner :
    CatValuedSourceTextSameOwnerBridge (J := J) F
      (SourceTextPlusConstructionDraft.toConstruction (J := J) draft)

namespace CatValuedSourceTextPlusConstructionDraftWithOwner

/-- The stackification existence statement obtained from the grouped source-text draft plus the
explicit same-owner bridge. -/
theorem stackificationExists
    (F : Cᵒᵖ ⥤ Cat.{vX, uX})
    (I : CatValuedSourceTextPlusConstructionDraftWithOwner (J := J) F) :
    ∃ Y : StackOver J,
      ∃ G :
        FibredCategoryOver.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')) ⟶ Y,
        FibredCategoryMor.IsStackification G :=
  catPseudofunctorPlusPlusStackificationExists_of_sourceTextBridge
    (J := J) F (SourceTextPlusConstructionDraft.toConstruction (J := J) I.draft)
    I.sameOwner

end CatValuedSourceTextPlusConstructionDraftWithOwner

end FibredCategoryMor

end CategoryTheory
