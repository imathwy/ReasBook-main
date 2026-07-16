import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ReducedFrontier
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationTargetOverlap
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationSourceCocycle
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationComponent
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationMiddleRestrictedComponents

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

/-- The restricted local object of the pulled-back total-cover glued object is the corresponding
inner local object of the original descent datum, with the pullback-cover owner translated back to
the total-cover owner. -/
theorem projectionDescentRealizationSource_restrictedLocalObject_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    {W : C} (a : W ⟶ A.Y) :
    let G :=
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object
    let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
    (DescentCompletionObjectOver.pullback (J := J) G I.f).restrictedLocalObject A a =
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D Atot)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D Atot) a := by
  dsimp only
  rfl

/-- The actual component of the local realization map on the pullback object is definitionally
the lower-level source-text component `rho_(b,j),(a,i)` after translating the pullback-cover owner
back to the total-cover owner.

This small rewrite lemma isolates the owner translation hidden in
`projectionDescentRealizationComponent`.  It is intentionally proved by `dsimp only; rfl`, so
later proofs can rewrite by a named lemma instead of asking `simp`/defeq to rediscover the same
large expansion. -/
theorem projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    {W : C} (a : W ⟶ A.Y) (k : W ⟶ K.Y)
    (h : a ≫ A.f ≫ 𝟙 I.Y = k ≫ K.f) :
    let G :=
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object
    let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
    let htotal : a ≫ Atot.f = k ≫ K.f ≫ I.f := by
      dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
      calc
        a ≫ A.f ≫ I.f = (a ≫ A.f ≫ 𝟙 I.Y) ≫ I.f := by
          simp [Category.assoc]
        _ = (k ≫ K.f) ≫ I.f := by
          rw [h]
        _ = k ≫ K.f ≫ I.f := by
          simp [Category.assoc]
    projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K a k h =
      projectionDescentRealizationComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D Atot I a K k htotal := by
  dsimp only
  rfl

/-- The source transition of `X|T_a` is the total-cover transition `rho` after translating the
two pullback-cover owners back to total-cover owners.  This is the source side of the
`Λ_a` compatibility square in the notation of the text. -/
theorem projectionDescentRealizationSource_overlapIso_hom_eq_transition
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    {W : C}
    (A₁ A₂ : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (a₁ : W ⟶ A₁.Y) (a₂ : W ⟶ A₂.Y)
    (hA : a₁ ≫ A₁.f = a₂ ≫ A₂.f) :
    let G :=
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object
    let Atot₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A₁
    let Atot₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A₂
    let htotal : a₁ ≫ Atot₁.f = a₂ ≫ Atot₂.f := by
      dsimp [Atot₁, Atot₂, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
      simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hA
    ((DescentCompletionObjectOver.pullback (J := J) G I.f).overlapIso a₁ a₂ hA).hom =
      projectionDescentTotalCoverTransitionComponent (J := J)
        hSheaf D Atot₁ Atot₂ a₁ a₂ htotal := by
  dsimp only
  rw [DescentCompletionObjectOver.pullback_overlapIso_hom]
  dsimp [DescentCompletionObjectOver.overlapIso, DescentCompletionObjectOver.transitionIso,
    projectionDescentTotalCoverGluedObjectOfTransitionLaws,
    projectionDescentTotalCoverGluedObjectOfLaws,
    projectionDescentTotalCoverGluedObjectOverOfLaws,
    projectionDescentTotalCoverGluedDatumOfLaws,
    projectionDescentTotalCoverGluedHom]

/-- Source stage 3.13 realization cocycle on the actual pulled-back source object
`X|T_a`.

This is the already-unfolded source side of the future compatibility square for
`Lambda_a`: changing the source cover member by the source overlap and then applying the local
realization component is the same as applying the realization component from the first source
cover member, provided the target inner owner is fixed. -/
theorem projectionDescentRealizationSourceOverlap_comp_component_sameTarget
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    {W : C}
    (A₁ A₂ : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (a₁ : W ⟶ A₁.Y) (a₂ : W ⟶ A₂.Y) (k : W ⟶ K.Y)
    (hA : a₁ ≫ A₁.f = a₂ ≫ A₂.f)
    (h₂ : a₂ ≫ A₂.f ≫ 𝟙 I.Y = k ≫ K.f) :
    let Source :=
      DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f
    let h₁ : a₁ ≫ A₁.f ≫ 𝟙 I.Y = k ≫ K.f := by
      calc
        a₁ ≫ A₁.f ≫ 𝟙 I.Y = a₂ ≫ A₂.f ≫ 𝟙 I.Y := by
          simpa [Category.assoc] using congrArg (fun q => q ≫ 𝟙 I.Y) hA
        _ = k ≫ K.f := h₂
    (Source.overlapIso a₁ a₂ hA).hom ≫
        projectionDescentRealizationComponent (J := J)
          hSheaf D hPull hComp I A₂ K a₂ k h₂ =
      projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A₁ K a₁ k h₁ := by
  dsimp only
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A₁
  let Atot₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A₂
  let htotalA : a₁ ≫ Atot₁.f = a₂ ≫ Atot₂.f := by
    dsimp [Atot₁, Atot₂, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hA
  let htotal₂ : a₂ ≫ Atot₂.f = k ≫ K.f ≫ I.f := by
    dsimp [Atot₂, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      a₂ ≫ A₂.f ≫ I.f = (a₂ ≫ A₂.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (k ≫ K.f) ≫ I.f := by rw [h₂]
      _ = k ≫ K.f ≫ I.f := by simp [Category.assoc]
  let h₁ : a₁ ≫ A₁.f ≫ 𝟙 I.Y = k ≫ K.f := by
    calc
      a₁ ≫ A₁.f ≫ 𝟙 I.Y = a₂ ≫ A₂.f ≫ 𝟙 I.Y := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ 𝟙 I.Y) hA
      _ = k ≫ K.f := h₂
  have hsource :=
    projectionDescentRealizationSource_overlapIso_hom_eq_transition
      (J := J) hSheaf D hPull hComp I A₁ A₂ a₁ a₂ hA
  have hcomp₂ :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A₂ K a₂ k h₂
  have hcomp₁ :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A₁ K a₁ k h₁
  rw [hsource, hcomp₂, hcomp₁]
  simpa [G, Atot₁, Atot₂, htotalA, htotal₂, h₁] using
    projectionDescentTotalCoverTransitionComponent_comp_realizationComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D Atot₁ Atot₂ I a₁ a₂ K k htotalA htotal₂

/-- Target-overlap for the actual realization component on the pulled-back source object. -/
theorem projectionDescentRealizationComponent_targetOverlap_sameSource
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    {W : C}
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (a : W ⟶ A.Y)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (h₁ : a ≫ A.f ≫ 𝟙 I.Y = k₁ ≫ K₁.f)
    (h₂ : a ≫ A.f ≫ 𝟙 I.Y = k₂ ≫ K₂.f) :
    let Target := projectionDescentDatumLocalObject (J := J) hSheaf D I
    projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K₁ (W := W) a k₁ h₁ ≫
        (Target.overlapIso k₁ k₂ hK).hom =
      projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K₂ (W := W) a k₂ h₂ := by
  dsimp only
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  let htotal₁ : a ≫ Atot.f = k₁ ≫ K₁.f ≫ I.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      a ≫ A.f ≫ I.f = (a ≫ A.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (k₁ ≫ K₁.f) ≫ I.f := by rw [h₁]
      _ = k₁ ≫ K₁.f ≫ I.f := by simp [Category.assoc]
  let htotal₂ : a ≫ Atot.f = k₂ ≫ K₂.f ≫ I.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      a ≫ A.f ≫ I.f = (a ≫ A.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (k₂ ≫ K₂.f) ≫ I.f := by rw [h₂]
      _ = k₂ ≫ K₂.f ≫ I.f := by simp [Category.assoc]
  have hcomp₁ :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A K₁ a k₁ h₁
  have hcomp₂ :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A K₂ a k₂ h₂
  rw [hcomp₁, hcomp₂]
  simpa [G, Atot, htotal₁, htotal₂] using
    projectionDescentRealizationComponentFromTotalCoverToDatumInner_targetOverlap
      (J := J) hSheaf D Atot I a K₁ K₂ k₁ k₂ hK htotal₁ htotal₂

/-- Source-text compatibility square for the actual local realization component `Λ_a`. -/
theorem projectionDescentRealizationComponent_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow) :
    projectionDescentRealizationComponentCompatibleLaw
      (J := J) hSheaf D hPull hComp I := by
  dsimp [projectionDescentRealizationComponentCompatibleLaw]
  intro W A₁ A₂ K₁ K₂ a₁ a₂ k₁ k₂ hA hK h₁ h₂
  let Source :=
    DescentCompletionObjectOver.pullback (J := J)
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object I.f
  let Target := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let h₁K₂ : a₁ ≫ A₁.f ≫ 𝟙 I.Y = k₂ ≫ K₂.f := by
    calc
      a₁ ≫ A₁.f ≫ 𝟙 I.Y = a₂ ≫ A₂.f ≫ 𝟙 I.Y := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ 𝟙 I.Y) hA
      _ = k₂ ≫ K₂.f := h₂
  have hsource :=
    projectionDescentRealizationSourceOverlap_comp_component_sameTarget
      (J := J) hSheaf D hPull hComp I A₁ A₂ K₂ a₁ a₂ k₂ hA h₂
  have htarget :=
    projectionDescentRealizationComponent_targetOverlap_sameSource
      (J := J) hSheaf D hPull hComp I A₁ K₁ K₂ a₁ k₁ k₂ hK h₁ h₁K₂
  dsimp [Source, Target] at hsource htarget
  calc
    (Source.overlapIso a₁ a₂ hA).hom ≫
        projectionDescentRealizationComponent (J := J)
          hSheaf D hPull hComp I A₂ K₂ (W := W) a₂ k₂ h₂ =
      projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A₁ K₂ (W := W) a₁ k₂ h₁K₂ := hsource
    _ =
      projectionDescentRealizationComponent (J := J)
          hSheaf D hPull hComp I A₁ K₁ (W := W) a₁ k₁ h₁ ≫
        (Target.overlapIso k₁ k₂ hK).hom := htarget.symm

/-- Pointwise restriction/naturality for the actual local realization component, lifted from the
owner-faithful lower-level pull-hom law. -/
theorem projectionDescentRealizationComponent_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (hInner : projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw
      (J := J) hSheaf D)
    (I : S.Arrow)
    {W W' : C}
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (a : W ⟶ A.Y) (k : W ⟶ K.Y)
    (h : a ≫ A.f ≫ 𝟙 I.Y = k ≫ K.f)
    (m : W' ⟶ W) (ma : W' ⟶ A.Y) (mk : W' ⟶ K.Y)
    (hma : m ≫ a = ma) (hmk : m ≫ k = mk) :
    let hsmall : ma ≫ A.f ≫ 𝟙 I.Y = mk ≫ K.f := by
      calc
        ma ≫ A.f ≫ 𝟙 I.Y = m ≫ a ≫ A.f ≫ 𝟙 I.Y := by
          rw [← hma]
          simp [Category.assoc]
        _ = m ≫ k ≫ K.f := by
          simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
        _ = mk ≫ K.f := by
          simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationComponent (J := J)
          hSheaf D hPull hComp I A K a k h)
        m ma mk hma hmk =
      projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K ma mk hsmall := by
  dsimp only
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  let htotal : a ≫ Atot.f = k ≫ K.f ≫ I.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      a ≫ A.f ≫ I.f = (a ≫ A.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (k ≫ K.f) ≫ I.f := by rw [h]
      _ = k ≫ K.f ≫ I.f := by simp [Category.assoc]
  let hsmall : ma ≫ A.f ≫ 𝟙 I.Y = mk ≫ K.f := by
    calc
      ma ≫ A.f ≫ 𝟙 I.Y = m ≫ a ≫ A.f ≫ 𝟙 I.Y := by
        rw [← hma]
        simp [Category.assoc]
      _ = m ≫ k ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
      _ = mk ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk
  let htotalSmall : ma ≫ Atot.f = mk ≫ K.f ≫ I.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      ma ≫ A.f ≫ I.f = (ma ≫ A.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (mk ≫ K.f) ≫ I.f := by rw [hsmall]
      _ = mk ≫ K.f ≫ I.f := by simp [Category.assoc]
  have hcomp :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A K a k h
  have hcompSmall :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A K ma mk hsmall
  rw [hcomp, hcompSmall]
  simpa [G, Atot, htotal, hsmall, htotalSmall] using
    hInner (A := Atot) m I a K k htotal ma mk hma hmk

/-- Source stage 3.13 realization frontier for the local maps
`Λ_a : X|T_a -> X_a`.

The first field is the already isolated owner-level restricted-composite component frontier for
`rho_(b,j),(a,i)`.  The remaining two fields are the source-text checks that `Λ_a` is a
compatible and restriction-natural double-indexed family on the actual pullback object
`X|T_a`.

This keeps the current owner/universe gap explicit: the lower-level `Lambda` pullback law has
been proved from `restrictedComposite`, but the final lift through
`projectionDescentRealizationComponent` is still a separate owner-translation step. -/
structure ProjectionDescentRealizationComponentFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D) where
  /-- Restricted-composite component expansion for the realization-side outer transition. -/
  restrictedComposite :
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
      (J := J) hSheaf D
  /-- Source-text compatibility square for each `Λ_a`. -/
  compatible :
    ∀ I : S.Arrow,
      projectionDescentRealizationComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I
  /-- Restriction/naturality law for each actual local realization map `Λ_a`. -/
  naturality :
    ∀ I : S.Arrow,
      projectionDescentRealizationComponentNaturalityLaw
        (J := J) hSheaf D hPull hComp I (compatible I)

namespace ProjectionDescentRealizationComponentFrontier

/-- The realization frontier packages each `Λ_a` as a natural owner-level morphism over
`T_a`. -/
noncomputable def naturalHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D}
    {hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D}
    (H : ProjectionDescentRealizationComponentFrontier (J := J) hSheaf D hPull hComp)
    (I : S.Arrow) :
    DescentCompletionObjectOver.NaturalHomOver (J := J)
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (𝟙 I.Y) :=
  projectionDescentRealizationNaturalHomOver
    (J := J) hSheaf D hPull hComp I (H.compatible I) (H.naturality I)

/-- The restricted-composite field recovers the lower-level realization pullback law for
`Λ_a,(b,j),i`. -/
theorem componentFromTotalCoverPullHomLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    {hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D}
    {hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D}
    (H : ProjectionDescentRealizationComponentFrontier (J := J) hSheaf D hPull hComp) :
    projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw
      (J := J) hSheaf D :=
  projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw_of_restrictedComposite
    (J := J) hSheaf D H.restrictedComposite

end ProjectionDescentRealizationComponentFrontier

/-- Restriction/naturality for the actual local realization component, packaged as the
`HomOver.familyNaturality'` law. -/
theorem projectionDescentRealizationComponent_naturality_of_inner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (hInner : projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw
      (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) :
    projectionDescentRealizationComponentNaturalityLaw
      (J := J) hSheaf D hPull hComp I hcompat := by
  dsimp [projectionDescentRealizationComponentNaturalityLaw,
    DescentCompletionObjectOver.HomOver.familyNaturality',
    projectionDescentRealizationHomOver]
  intro W W' A K a k h m ma mk hma hmk
  exact
    projectionDescentRealizationComponent_pullHom
      (J := J) hSheaf D hPull hComp hInner I A K a k h m ma mk hma hmk

/-- Realization component frontier supplied by the restricted-composite owner calculation. -/
noncomputable def projectionDescentRealizationComponentFrontier_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (hRestricted :
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    ProjectionDescentRealizationComponentFrontier (J := J) hSheaf D hPull hComp where
  restrictedComposite := hRestricted
  compatible := by
    intro I
    exact projectionDescentRealizationComponent_compatible
      (J := J) hSheaf D hPull hComp I
  naturality := by
    intro I
    exact projectionDescentRealizationComponent_naturality_of_inner
      (J := J) hSheaf D hPull hComp
      (projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw_of_restrictedComposite
        (J := J) hSheaf D hRestricted)
      I (projectionDescentRealizationComponent_compatible
        (J := J) hSheaf D hPull hComp I)

/-- Source stage 3.13 frontier around the total-cover construction and the local realization
maps.

The two fields are the source component calculations:
* `transitionRestrictedComposite` is the `rho_(ai)(bj)` calculation used to build the glued
  total-cover object;
* `realizationRestrictedComposite` is the `Lambda_a,(b,j),i = rho_(b,j),(a,i)` calculation used
  to build the local maps from the glued object back to the original descent datum.

The final statement that these local maps assemble to an isomorphism of outer descent data is
kept as `realizesObligation` below; it is not collapsed into a definitional equality. -/
structure ProjectionDescentTotalCoverSourceRealizationFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) where
  /-- Component expansion for the total-cover transition `rho_(ai)(bj)`. -/
  transitionRestrictedComposite :
    projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
      (J := J) hSheaf D
  /-- Component expansion for the realization map `Lambda_a,(b,j),i`. -/
  realizationRestrictedComposite :
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
      (J := J) hSheaf D

namespace ProjectionDescentTotalCoverSourceRealizationFrontier

/-- The transition restriction law derived from the source component calculation. -/
theorem transitionPullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D :=
  projectionDescentTotalCoverTransitionComponentPullHomLaw_of_restrictedComposite
    (J := J) hSheaf D H.transitionRestrictedComposite

/-- The transition cocycle law derived from the already explicit outer component calculation. -/
theorem transitionHomComp
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (_H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D :=
  projectionDescentTotalCoverTransitionComponentHomCompLaw_of_explicit
    (J := J) hSheaf D
    (projectionDescentTotalCoverExplicitTransitionComponentHomCompLaw_of_outer
      (J := J) hSheaf D)

/-- The target-overlap part of the `Lambda_a` compatibility square is already discharged. -/
noncomputable def targetOverlapFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (_H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) :
    ProjectionDescentRealizationTargetOverlapFrontier (J := J) hSheaf D :=
  projectionDescentRealizationTargetOverlapFrontier (J := J) hSheaf D

/-- The component-level `Lambda_a` realization frontier derived from the restricted-composite
owner calculation. -/
noncomputable def componentFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) :
    ProjectionDescentRealizationComponentFrontier
      (J := J) hSheaf D H.transitionPullHom H.transitionHomComp :=
  projectionDescentRealizationComponentFrontier_of_restrictedComposite
    (J := J) hSheaf D H.transitionPullHom H.transitionHomComp
    H.realizationRestrictedComposite

/-- The remaining source statement: the local maps `Lambda_a` assemble to an isomorphism from
the descent datum of the glued total-cover object to the original outer descent datum. -/
abbrev realizesObligation
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D) :
    Type _ :=
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  ((canonicalFiberPseudofunctor P).toDescentData
      (fun I : S.Arrow => I.f)).obj
    (projectionFiberObject (J := J) hSheaf
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D H.transitionPullHom H.transitionHomComp)) ≅ D

/-- Once the final realization obligation is supplied, the source realization frontier gives the
existing reduced total-cover frontier. -/
noncomputable def toReducedFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverSourceRealizationFrontier (J := J) hSheaf D)
    (hRealizes : H.realizesObligation) :
    ProjectionDescentTotalCoverReducedFrontier (J := J) hSheaf D where
  transitionRestrictedComposite := H.transitionRestrictedComposite
  realizes := by
    simpa [realizesObligation, transitionPullHom, transitionHomComp] using hRealizes

end ProjectionDescentTotalCoverSourceRealizationFrontier

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
