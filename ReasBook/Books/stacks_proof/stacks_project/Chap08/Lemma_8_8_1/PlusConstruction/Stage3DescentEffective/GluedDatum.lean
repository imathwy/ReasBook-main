import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionComponent
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionLaws

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

/-- Source stage 3.13 glued object, object field: on the total cover
`{U_ai -> U}`, keep the original local object `x_ai`. -/
noncomputable abbrev projectionDescentTotalCoverGluedLocalObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow) :
    X.p.Fiber A.Y :=
  projectionDescentTotalCoverLocalObject (J := J) hSheaf D A

/-- Source stage 3.13 glued object, hom field: the descent transition on the total cover is the
source `rho_(ai)(bj)`, obtained by evaluating the outer transition `Theta_ab` and transporting
back to the original local objects. -/
noncomputable def projectionDescentTotalCoverGluedHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (q : W ⟶ U)
    {A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow}
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (ha : a ≫ A.f = q) (hb : b ≫ B.f = q) :
    ((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj
        (projectionDescentTotalCoverGluedLocalObject (J := J) hSheaf D A) ⟶
      ((canonicalFiberPseudofunctor X.p).map b.op.toLoc).toFunctor.obj
        (projectionDescentTotalCoverGluedLocalObject (J := J) hSheaf D B) :=
  projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b
    (ha.trans hb.symm)

@[simp]
theorem projectionDescentTotalCoverGluedHom_eq_transition
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (q : W ⟶ U)
    {A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow}
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (ha : a ≫ A.f = q) (hb : b ≫ B.f = q) :
    projectionDescentTotalCoverGluedHom (J := J) hSheaf D q a b ha hb =
      projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b
        (ha.trans hb.symm) :=
  rfl

/-- Source stage 3.13 self condition for the hom field of the glued total-cover datum. -/
theorem projectionDescentTotalCoverGluedHom_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (q : W ⟶ U)
    {A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow}
    (a : W ⟶ A.Y)
    (ha : a ≫ A.f = q) :
    projectionDescentTotalCoverGluedHom (J := J) hSheaf D q a a ha ha =
      𝟙 (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj
        (projectionDescentTotalCoverGluedLocalObject (J := J) hSheaf D A)) := by
  simpa [projectionDescentTotalCoverGluedHom] using
    projectionDescentTotalCoverTransitionComponent_self (J := J) hSheaf D A a

/-- Source stage 3.13 `pullHom` law for the total-cover glued datum.  This is the
formal owner of the source assertion that the components `rho_(ai)(bj)` commute with further
restriction. -/
def projectionDescentTotalCoverGluedDatumPullHomLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U)
    (hq : g ≫ q = q')
    ⦃A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (ha : a ≫ A.f = q) (hb : b ≫ B.f = q)
    (ga : Y' ⟶ A.Y) (gb : Y' ⟶ B.Y)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb),
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (projectionDescentTotalCoverGluedHom (J := J) hSheaf D q a b ha hb)
          g ga gb hga hgb =
        projectionDescentTotalCoverGluedHom (J := J) hSheaf D q' ga gb
          (by rw [← hq, ← hga, Category.assoc, ha])
          (by rw [← hq, ← hgb, Category.assoc, hb])

/-- Source stage 3.13 cocycle law for the total-cover glued datum.  This is the formal owner of
the source equality `rho_(bj)(ck) rho_(ai)(bj) = rho_(ai)(ck)` on triple overlaps. -/
def projectionDescentTotalCoverGluedDatumHomCompLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y : C⦄ (q : Y ⟶ U)
    ⦃A B K : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y) (k : Y ⟶ K.Y)
    (ha : a ≫ A.f = q) (hb : b ≫ B.f = q) (hk : k ≫ K.f = q),
      projectionDescentTotalCoverGluedHom (J := J) hSheaf D q a b ha hb ≫
          projectionDescentTotalCoverGluedHom (J := J) hSheaf D q b k hb hk =
        projectionDescentTotalCoverGluedHom (J := J) hSheaf D q a k ha hk

/-- The transition-level restriction law is exactly the pullback law required by the total-cover
glued descent datum, after inserting the redundant base map `q`. -/
theorem projectionDescentTotalCoverGluedDatumPullHomLaw_of_transitionComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hρ : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D) :
    projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D := by
  intro Y' Y g q q' hq A B a b ha hb ga gb hga hgb
  simpa [projectionDescentTotalCoverGluedHom] using
    hρ g a b (ha.trans hb.symm) ga gb hga hgb

/-- The transition-level cocycle law is exactly the composition law required by the total-cover
glued descent datum, after inserting the redundant base map `q`. -/
theorem projectionDescentTotalCoverGluedDatumHomCompLaw_of_transitionComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hρ : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D) :
    projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D := by
  intro Y q A B K a b k ha hb hk
  simpa [projectionDescentTotalCoverGluedHom] using
    hρ a b k (ha.trans hb.symm) (hb.trans hk.symm)

/-- Source stage 3.13 constructor: once the restriction law and cocycle law for the
total-cover transitions have been proved, they assemble into the descent datum
`({U_ai -> U}, x_ai, rho_(ai)(bj))`. -/
noncomputable def projectionDescentTotalCoverGluedDatumOfLaws
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D) :
    (canonicalFiberPseudofunctor X.p).DescentData
      (X := fun A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow => A.Y)
      (fun A => A.f) where
  obj A :=
    projectionDescentTotalCoverGluedLocalObject (J := J) hSheaf D A
  hom := fun {_Y} q {_A _B} a b ha hb =>
    projectionDescentTotalCoverGluedHom (J := J) hSheaf D q a b ha hb
  pullHom_hom := fun {_Y' _Y} g q q' hq {_A _B} a b ha hb ga gb hga hgb =>
    hpull g q q' hq a b ha hb ga gb hga hgb
  hom_self := fun {_Y} q {_A} a ha =>
    projectionDescentTotalCoverGluedHom_self (J := J) hSheaf D q a ha
  hom_comp := fun {_Y} q {_A _B _K} a b k ha hb hk =>
    hcomp q a b k ha hb hk

@[simp]
theorem projectionDescentTotalCoverGluedDatumOfLaws_obj
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow) :
    (projectionDescentTotalCoverGluedDatumOfLaws (J := J) hSheaf D hpull hcomp).obj A =
      projectionDescentTotalCoverGluedLocalObject (J := J) hSheaf D A :=
  rfl

@[simp]
theorem projectionDescentTotalCoverGluedDatumOfLaws_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D)
    (q : Y ⟶ U)
    {A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow}
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (ha : a ≫ A.f = q) (hb : b ≫ B.f = q) :
    (projectionDescentTotalCoverGluedDatumOfLaws (J := J) hSheaf D hpull hcomp).hom
        q a b ha hb =
      projectionDescentTotalCoverGluedHom (J := J) hSheaf D q a b ha hb :=
  rfl

/-- Source stage 3.13 glued object over `U`, conditional on the two total-cover laws.  This is
the completed object `X := ({U_ai -> U}, x_ai, rho_(ai)(bj))`. -/
noncomputable def projectionDescentTotalCoverGluedObjectOverOfLaws
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D) :
    DescentCompletionObjectOver (J := J) X U where
  cover := projectionDescentTotalCover (J := J) hSheaf S D
  datum := projectionDescentTotalCoverGluedDatumOfLaws (J := J) hSheaf D hpull hcomp

@[simp]
theorem projectionDescentTotalCoverGluedObjectOverOfLaws_cover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D) :
    (projectionDescentTotalCoverGluedObjectOverOfLaws (J := J)
      hSheaf D hpull hcomp).cover =
      projectionDescentTotalCover (J := J) hSheaf S D :=
  rfl

@[simp]
theorem projectionDescentTotalCoverGluedObjectOverOfLaws_datum
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D) :
    (projectionDescentTotalCoverGluedObjectOverOfLaws (J := J)
      hSheaf D hpull hcomp).datum =
      projectionDescentTotalCoverGluedDatumOfLaws (J := J) hSheaf D hpull hcomp :=
  rfl

/-- Total-category version of the stage 3.13 glued object. -/
noncomputable def projectionDescentTotalCoverGluedObjectOfLaws
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D) :
    DescentCompletionObject (J := J) X where
  base := U
  object := projectionDescentTotalCoverGluedObjectOverOfLaws (J := J)
    hSheaf D hpull hcomp

@[simp]
theorem projectionDescentTotalCoverGluedObjectOfLaws_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverGluedDatumPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverGluedDatumHomCompLaw (J := J) hSheaf D) :
    (projectionDescentTotalCoverGluedObjectOfLaws (J := J)
      hSheaf D hpull hcomp).base = U :=
  rfl

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
