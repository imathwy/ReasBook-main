import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionComponent
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RestrictedExplicitArrow

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

/-- The old explicit outer component, evaluated at the cover arrows obtained by restricting the
old explicit pullback covers along `g`, and transported to the directly rebuilt
`IAnew`/`IBnew` owners.

This isolates the last owner-identification step in the stage 3.13 middle square. -/
noncomputable def projectionDescentExplicitOuterFiberHomForTotalCoverOldRestrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f)
    (ga : Y' ⟶ A.Y) (gb : Y' ⟶ B.Y)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    let DA :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let DB :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
    let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
    let IBnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
    DA.restrictedLocalObject IAnew (𝟙 Y') ⟶
      DB.restrictedLocalObject IBnew (𝟙 Y') := by
  letI := category (J := J) hSheaf
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let DB :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let IBnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
  let IAres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga
  let IBres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D B g b gb hgb
  let IAresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAres
  let IBresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b) IBres
  let α :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B a b h
  let sourceCast :
      DA.restrictedLocalObject IAnew (𝟙 Y') ⟶
        DA.restrictedLocalObject IAresBase (𝟙 Y') :=
    (DA.overlapIso (I₁ := IAnew) (I₂ := IAresBase) (𝟙 Y') (𝟙 Y') (by
      dsimp [IAnew, IAresBase, IAres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
        projectionDescentTotalCoverExplicitPullbackArrow,
        DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
      rw [← hga]
      simp [Category.assoc])).hom
  let targetCast :
      DB.restrictedLocalObject IBresBase (𝟙 Y') ⟶
        DB.restrictedLocalObject IBnew (𝟙 Y') :=
    (DB.overlapIso (I₁ := IBresBase) (I₂ := IBnew) (𝟙 Y') (𝟙 Y') (by
      dsimp [IBnew, IBresBase, IBres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
        projectionDescentTotalCoverExplicitPullbackArrow,
        DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
      rw [← hgb]
      simp [Category.assoc])).hom
  exact sourceCast ≫
    α.1.components.toHomOver.family IAres IBres (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomForTotalCover_base
            (J := J) hSheaf D A B a b h
        rw [hbase]
        dsimp [IAres, IBres, projectionDescentTotalCoverExplicitPullbackArrowAlong]
        calc
          𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
            rw [← Category.assoc]
          _ = 𝟙 Y' ≫ g := Category.comp_id _) ≫
    targetCast

/-- The remaining component owner-identification after the old-cover compatibility square:
the old outer component evaluated on the restricted old explicit-cover arrows agrees with the
component rebuilt directly over `(ga, gb)`. -/
def projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    ⦃A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f)
    (ga : Y' ⟶ A.Y) (gb : Y' ⟶ B.Y)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb),
    let hsmall : ga ≫ A.f = gb ≫ B.f := by
      calc
        ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
        _ = g ≫ b ≫ B.f := by
          simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
        _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc]
    projectionDescentExplicitOuterFiberHomForTotalCoverOldRestrictedComponent
        (J := J) hSheaf D A B g a b h ga gb hga hgb =
      (let α :=
        projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
          hSheaf D A B ga gb hsmall
      α.1.components.toHomOver.family
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
        (𝟙 Y') (𝟙 Y')
        (by
          have hbase :
              α.1.base = 𝟙 Y' :=
            projectionDescentExplicitOuterFiberHomForTotalCover_base
              (J := J) hSheaf D A B ga gb hsmall
          rw [hbase]
          dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
          calc
            𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
            _ = 𝟙 Y' ≫ 𝟙 Y' := rfl))

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
