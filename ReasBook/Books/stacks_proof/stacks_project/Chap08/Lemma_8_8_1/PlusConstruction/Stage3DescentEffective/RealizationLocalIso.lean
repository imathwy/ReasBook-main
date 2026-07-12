import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationFrontier

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

/-- The descent datum obtained by pulling the glued total-cover object back to the original
outer cover.  This is the source side of the final `Lambda_a` comparison. -/
noncomputable abbrev realizationDescentData
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    (canonicalFiberPseudofunctor P).DescentData
      (X := fun I : S.Arrow => I.Y) (fun I => I.f) :=
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  ((canonicalFiberPseudofunctor P).toDescentData
      (fun I : S.Arrow => I.f)).obj
    (projectionFiberObject (J := J) hSheaf
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp))

/-- The explicit-owner morphism `Lambda_a : X|T_a -> X_a` in the fibre of the
descent-completion projection.  This packages the already constructed natural component family
as an actual fibre morphism; the subsequent owner bridge transports it to
`realizationDescentData.obj I`. -/
noncomputable def explicitLocalHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (I : S.Arrow) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
        I.f ⟶
      projectionFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let G :=
    projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp
  let m : Hom (J := J)
      (pullback (J := J) G I.f)
      (projectionDescentDatumObject (J := J) hSheaf D I) := {
    base := 𝟙 I.Y
    components := H.componentFrontier.naturalHomOver I }
  letI : P.IsHomLift (𝟙 I.Y) m := by
    simpa [P, projectionFunctor, m]
      using (inferInstance : P.IsHomLift (P.map m) m)
  exact Functor.Fiber.homMk P I.Y m

/-- The final source stage 3.13 isomorphism split into the exact two component obligations
required by `Pseudofunctor.DescentData.isoMk`.

The intended source proof of `localIso I` is the local isomorphism
`Lambda_I : X|T_I -> X_I`.  The intended source proof of `localIso_comm` is the equality
`Theta_IK o Lambda_I = Lambda_K` on overlaps. -/
structure RealizationIsoFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) where
  /-- The local realization isomorphism `Lambda_a` over each outer cover member. -/
  localIso :
    ∀ I : S.Arrow,
      (H.realizationDescentData).obj I ≅ D.obj I
  /-- Compatibility with the outer descent transitions:
  `Theta_ab o Lambda_a = Lambda_b`. -/
  localIso_comm :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I K : S.Arrow⦄
      (i : Y ⟶ I.Y) (k : Y ⟶ K.Y)
      (hi : i ≫ I.f = q) (hk : k ≫ K.f = q),
        ((canonicalFiberPseudofunctor P).map i.op.toLoc).toFunctor.map
            (localIso I).hom ≫ D.hom q i k hi hk =
          (H.realizationDescentData).hom q i k hi hk ≫
            ((canonicalFiberPseudofunctor P).map k.op.toLoc).toFunctor.map
              (localIso K).hom

namespace RealizationIsoFrontier

/-- A componentwise `Lambda_a` isomorphism compatible with outer descent transitions gives the
final realization isomorphism of descent data. -/
noncomputable def realizes
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D}
    (R : RealizationIsoFrontier (J := J) H) :
    H.realizesObligation :=
  Pseudofunctor.DescentData.isoMk R.localIso (by
    intro Y q I K i k hi hk
    exact R.localIso_comm q i k hi hk)

/-- Convert the split isomorphism frontier to the reduced total-cover frontier expected by the
existing stage 3.13 interface. -/
noncomputable def toReducedFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D}
    (R : RealizationIsoFrontier (J := J) H) :
    ProjectionDescentTotalCoverReducedFrontier (J := J) hSheaf D :=
  H.toReducedFrontier R.realizes

end RealizationIsoFrontier

/-- Owner bridge from the explicit pullback object used in the source construction to the
canonical pullback owner used by `toDescentData`.

This is the source side of the local comparison `Lambda_a`.  It intentionally records the
cartesian uniqueness bridge instead of identifying the two pullback owners by definitional
equality. -/
noncomputable def explicitSourceOwnerIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (I : S.Arrow) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
        I.f ≅
      (H.realizationDescentData).obj I := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  simpa [realizationDescentData] using
    explicitPullbackFiberObjectIsoCanonical
      (J := J) hSheaf
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp) I.f

set_option backward.isDefEq.respectTransparency false in
/-- The source-owner bridge for `Lambda_a` is the concrete cartesian bridge: after composing
with the canonical pullback projection it is the explicit pullback projection. -/
theorem explicitSourceOwnerIso_hom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (I : S.Arrow) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let G :=
      projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp
    (explicitSourceOwnerIso (J := J) H I).hom.1 ≫
        (canonicalPullbackChoice P).map I.f (projectionFiberObject (J := J) hSheaf G) =
      pullbackMap (J := J) G I.f := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let G :=
    projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp
  simpa [explicitSourceOwnerIso, realizationDescentData, G] using
    explicitPullbackFiberObjectIsoCanonical_hom_fac (J := J) hSheaf G I.f

set_option backward.isDefEq.respectTransparency false in
/-- Inverse form of `explicitSourceOwnerIso_hom_fac`. -/
theorem explicitSourceOwnerIso_inv_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (I : S.Arrow) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let G :=
      projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp
    (explicitSourceOwnerIso (J := J) H I).inv.1 ≫
        pullbackMap (J := J) G I.f =
      (canonicalPullbackChoice P).map I.f (projectionFiberObject (J := J) hSheaf G) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let G :=
    projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp
  simpa [explicitSourceOwnerIso, realizationDescentData, G] using
    explicitPullbackFiberObjectIsoCanonical_inv_fac (J := J) hSheaf G I.f

/-- Owner bridge from the repackaged datum object with definitional base `I.Y` back to the
original outer descent object `D.obj I`. -/
noncomputable def explicitTargetOwnerIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow) :
    letI := category (J := J) hSheaf
    projectionFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I) ≅
      D.obj I := by
  letI := category (J := J) hSheaf
  exact eqToIso (projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I)

/-- Source-faithful local isomorphism frontier for the sentence:
`Lambda_a` is an isomorphism, with inverse given componentwise by
`rho_(a,i),(b,j)`.

The field `localExplicitIso` lives on the explicit pullback owners used by the component
construction.  The theorem `localExplicitIso_hom` pins its forward morphism to the already built
`explicitLocalHom`, whose components are `rho_(b,j),(a,i)`. -/
structure ExplicitLocalIsoFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) where
  /-- The explicit-owner local isomorphism
  `X|T_a -> X_a`; its inverse is the source-text component family
  `rho_(a,i),(b,j)`. -/
  localExplicitIso :
    ∀ I : S.Arrow,
      letI := category (J := J) hSheaf
      let P := projectionFunctor (J := J) hSheaf
      haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
      explicitPullbackFiberObject (J := J) hSheaf
          (projectionDescentTotalCoverGluedObjectOfTransitionLaws
            (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)
          I.f ≅
        projectionFiberObject (J := J) hSheaf
          (projectionDescentDatumObject (J := J) hSheaf D I)
  /-- The forward arrow of `localExplicitIso` is the already constructed `Lambda_a`. -/
  localExplicitIso_hom :
    ∀ I : S.Arrow,
      (localExplicitIso I).hom = H.explicitLocalHom I

namespace ExplicitLocalIsoFrontier

/-- Transport an explicit-owner local isomorphism to the owner required by
`Pseudofunctor.DescentData.isoMk`. -/
noncomputable def localIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D}
    (R : ExplicitLocalIsoFrontier (J := J) H)
    (I : S.Arrow) :
    (H.realizationDescentData).obj I ≅ D.obj I := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  exact (explicitSourceOwnerIso (J := J) H I).symm ≪≫
    R.localExplicitIso I ≪≫ explicitTargetOwnerIso (J := J) hSheaf D I

/-- Once the source-text outer compatibility
`Theta_ab o Lambda_a = Lambda_b` is proved for the transported local isomorphisms, the explicit
local-isomorphism frontier gives the existing final realization-isomorphism frontier. -/
noncomputable def toRealizationIsoFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D}
    (R : ExplicitLocalIsoFrontier (J := J) H)
    (hcomm :
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
                (R.localIso K).hom) :
    RealizationIsoFrontier (J := J) H where
  localIso := R.localIso
  localIso_comm := hcomm

end ExplicitLocalIsoFrontier

end ProjectionDescentTotalCoverSourceRealizationFrontier
end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
