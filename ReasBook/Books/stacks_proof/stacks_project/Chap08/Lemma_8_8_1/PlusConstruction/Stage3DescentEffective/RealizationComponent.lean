import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.Frontier

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

/-- Source stage 3.13 realization helper: after restricting an inner cover member
`U_ai -> T_a` along `W -> U_ai`, keep the result as an arrow of the same inner cover.

This is the target-side analogue of
`projectionDescentTotalCoverRefinedInner`, but it is indexed by the explicit outer owner `I`
and inner owner `K` instead of by an arrow of the bound total cover. -/
noncomputable abbrev projectionDescentDatumRefinedInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow :=
  K.precomp k

@[simp]
theorem projectionDescentDatumRefinedInner_f
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y) :
    (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k).f =
      k ≫ K.f :=
  rfl

/-- Target-side local-refinement comparison used in the realization map `Λ_a`. -/
noncomputable def projectionDescentDatumLocalRestrictionIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject K k ≅
      (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject
        (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k) (𝟙 W) :=
  (projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
    (I₁ := K)
    (I₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
    k (𝟙 W) (by simp [projectionDescentDatumRefinedInner])

/-- Target-side explicit pullback-cover arrow for `X_a` along `W -> U_ai -> T_a`. -/
noncomputable def projectionDescentDatumExplicitPullbackArrow
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y) :
    ((projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.pullback
        (k ≫ K.f)).Arrow where
  Y := W
  f := 𝟙 W
  hf := by
    simpa [projectionDescentDatumRefinedInner] using
      (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k).hf

@[simp]
theorem projectionDescentDatumExplicitPullbackArrow_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y) :
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k ≫ K.f)
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k) =
      projectionDescentDatumRefinedInner (J := J) hSheaf D I K k := by
  ext <;> simp [projectionDescentDatumExplicitPullbackArrow,
    projectionDescentDatumRefinedInner]

/-- Compare the target-side explicit pullback cover with the refined inner cover owner. -/
noncomputable def projectionDescentDatumExplicitPullbackArrowRestrictionIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y) :
    (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k ≫ K.f)).restrictedLocalObject
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k) (𝟙 W) ≅
      (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject
        (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k) (𝟙 W) := by
  let D₀ := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let h := k ≫ K.f
  let K' := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
  let Kb := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D₀ h K'
  change D₀.restrictedLocalObject Kb (𝟙 W) ≅
    D₀.restrictedLocalObject
      (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k) (𝟙 W)
  exact D₀.overlapIso (I₁ := Kb)
    (I₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
    (𝟙 W) (𝟙 W) (by
      dsimp [Kb, K', D₀, h, projectionDescentDatumExplicitPullbackArrow,
        projectionDescentDatumRefinedInner,
        DescentCompletionObjectOver.pullbackCoverBaseArrow]
      simp)

/-- Source stage 3.13 realization helper: specialize the outer transition from a total-cover
member `(b,j)` to the explicit target owner `(a,i)`.

This is the canonical-pullback owner form of the source component
`theta_ba,ji`; the explicit-owner version below transports it to the descent-completion
pullback objects. -/
noncomputable def projectionDescentOuterFiberHomFromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ((canonicalFiberPseudofunctor P).map
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a).op.toLoc).toFunctor.obj
        (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A)) ⟶
      ((canonicalFiberPseudofunctor P).map (k ≫ K.f).op.toLoc).toFunctor.obj
        (D.obj I) :=
  projectionDescentOuterFiberHom (J := J) hSheaf D
    (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    I
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (k ≫ K.f)
    (by
      calc
        projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f =
          a ≫ A.f := by
            have hA :
                a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                    (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
                  a ≫ A.f :=
              congrArg (fun q => a ≫ q)
                (projectionDescentTotalCover_fac (J := J) hSheaf D A)
            simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using hA
        _ = (k ≫ K.f) ≫ I.f := by simpa [Category.assoc] using h)

/-- Source stage 3.13 realization helper: specialize the outer transition from a total-cover
member `(b,j)` to the explicit target owner `(a,i)`.

This is the owner-faithful form of the source component
`rho_(b,j),(a,i) = theta_ba,ji`; the target is not rebuilt as an arrow of the bound
total cover, so no `bind` choice is treated as definitional. -/
noncomputable def projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) ⟶
      explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I)
        (k ≫ K.f) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let eB :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D I (k ≫ K.f)
  exact eA.hom ≫
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h ≫
      eB.inv

/-- The explicit-owner realization transition is vertical over `W`. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    letI := category (J := J) hSheaf
    (projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
      hSheaf D A I a K k h).1.base = 𝟙 W := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
      hSheaf D A I a K k h
  letI : P.IsHomLift (𝟙 W) α.1 := α.2
  have hfac := IsHomLift.fac' P (𝟙 W) α.1
  simpa [P, projectionFunctor, α] using hfac

/-- Component of `theta_ba,ji` on the two explicit pullback covers. -/
noncomputable def projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) (𝟙 W) ⟶
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k ≫ K.f)).restrictedLocalObject
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k) (𝟙 W) := by
  letI := category (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
      hSheaf D A I a K k h
  have hbase :
      α.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
      (J := J) hSheaf D A I a K k h
  exact α.1.components.toHomOver.family
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
    (𝟙 W) (𝟙 W)
    (by
      rw [hbase]
      dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      calc
        𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
        _ = 𝟙 W ≫ 𝟙 W := rfl)

/-- The source-text realization component
`Λ_a,(b,j),i := rho_(b,j),(a,i)`, with all owner transports explicit. -/
noncomputable def projectionDescentRealizationComponentFromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D A) a ⟶
      (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject K k :=
  (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom ≫
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D A a).inv ≫
    projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner (J := J)
      hSheaf D A I a K k h ≫
    (projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D I K k).hom ≫
    (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).inv

/-- The component formula for the local realization map
`(glued X)|_{T_a} -> X_a`, before the compatibility field is supplied. -/
noncomputable def projectionDescentRealizationComponent
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
    (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).restrictedLocalObject A a ⟶
      (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject K k := by
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  have htotal : a ≫ Atot.f = k ≫ K.f ≫ I.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      a ≫ A.f ≫ I.f = (a ≫ A.f ≫ 𝟙 I.Y) ≫ I.f := by simp [Category.assoc]
      _ = (k ≫ K.f) ≫ I.f := by rw [h]
      _ = k ≫ K.f ≫ I.f := by simp [Category.assoc]
  simpa [G, Atot, projectionDescentTotalCoverGluedObjectOfTransitionLaws,
    projectionDescentTotalCoverGluedObjectOfLaws,
    projectionDescentTotalCoverGluedObjectOverOfLaws,
    projectionDescentTotalCoverGluedDatumOfLaws,
    projectionDescentTotalCoverGluedLocalObject,
    DescentCompletionObjectOver.pullback,
    DescentCompletionObjectOver.restrictedLocalObject,
    DescentCompletionObjectOver.pullbackCoverBaseArrow] using
    projectionDescentRealizationComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D Atot I a K k htotal

/-- Compatibility obligation for the local realization component.  This is exactly the
HomOver compatibility square for `Λ_a`; the next source-faithful step is to prove it by
expanding the total-cover cocycle `rho_(a,i),(b,j)`. -/
def projectionDescentRealizationComponentCompatibleLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow) : Prop :=
  let Source :=
    DescentCompletionObjectOver.pullback (J := J)
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object I.f
  let Target := projectionDescentDatumLocalObject (J := J) hSheaf D I
  ∀ {W : C} (A₁ A₂ : Source.cover.Arrow) (K₁ K₂ : Target.cover.Arrow)
    (a₁ : W ⟶ A₁.Y) (a₂ : W ⟶ A₂.Y)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hA : a₁ ≫ A₁.f = a₂ ≫ A₂.f)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (h₁ : a₁ ≫ A₁.f ≫ 𝟙 I.Y = k₁ ≫ K₁.f)
    (h₂ : a₂ ≫ A₂.f ≫ 𝟙 I.Y = k₂ ≫ K₂.f),
      (Source.overlapIso a₁ a₂ hA).hom ≫
          projectionDescentRealizationComponent (J := J)
            hSheaf D hPull hComp I A₂ K₂ (W := W) a₂ k₂ h₂ =
        projectionDescentRealizationComponent (J := J)
            hSheaf D hPull hComp I A₁ K₁ (W := W) a₁ k₁ h₁ ≫
          (Target.overlapIso k₁ k₂ hK).hom

/-- Local realization morphism over `T_a`, conditional on the component compatibility law. -/
noncomputable def projectionDescentRealizationHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) :
    DescentCompletionObjectOver.HomOver (J := J)
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (𝟙 I.Y) where
  family A K a k h :=
    projectionDescentRealizationComponent (J := J)
      hSheaf D hPull hComp I A K a k h
  compatible := by
    intro W A₁ A₂ K₁ K₂ a₁ a₂ k₁ k₂ hA hK h₁ h₂
    exact hcompat A₁ A₂ K₁ K₂ a₁ a₂ k₁ k₂ hA hK h₁ h₂

/-- Naturality obligation for the local realization map. -/
def projectionDescentRealizationComponentNaturalityLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I) : Prop :=
  DescentCompletionObjectOver.HomOver.familyNaturality' (J := J)
    (projectionDescentRealizationHomOver
      (J := J) hSheaf D hPull hComp I hcompat)

/-- Local realization morphism over `T_a`, bundled with the restriction/naturality law. -/
noncomputable def projectionDescentRealizationNaturalHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (hcompat :
      projectionDescentRealizationComponentCompatibleLaw
        (J := J) hSheaf D hPull hComp I)
    (hnat :
      projectionDescentRealizationComponentNaturalityLaw
        (J := J) hSheaf D hPull hComp I hcompat) :
    DescentCompletionObjectOver.NaturalHomOver (J := J)
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (𝟙 I.Y) where
  toHomOver :=
    projectionDescentRealizationHomOver
      (J := J) hSheaf D hPull hComp I hcompat
  naturality := hnat

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
