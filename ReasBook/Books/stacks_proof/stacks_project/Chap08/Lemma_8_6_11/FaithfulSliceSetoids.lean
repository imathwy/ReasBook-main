import Mathlib
import StacksProject_2024.Chap04.Lemma_4_42_5
import StacksProject_2024.Chap07.Lemma_7_26_4.TerminalCovers
import StacksProject_2024.Chap08.Definition_8_5_1
import StacksProject_2024.Chap08.Definition_8_6_1
import StacksProject_2024.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import StacksProject_2024.Chap08.Lemma_8_4_6.FixedCoverEquivalenceBridge
import StacksProject_2024.Chap08.Lemma_8_6_3

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X T : FibredInGroupoidsOver C}
variable [IsStackInGroupoids J T.p]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

/-- Helper for Chap08 Lemma 8 6 11: a faithful functor reflects thinness from its target. -/
theorem isThin_of_faithful_to_thin
    {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) [G.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A := by
  -- Equality of arrows is checked after applying the faithful functor, where the target is thin.
  intro a b
  refine ⟨?_⟩
  intro f g
  exact G.map_injective (Subsingleton.elim _ _)

/-- Helper for Chap08 Lemma 8 6 11: in a groupoid-valued faithful functor, a structured-arrow
category over a fixed target object is thin. -/
theorem structuredArrow_isThin_of_faithful
    {A B : Type*} [Category A] [Category B]
    (b : B) (G : A ⥤ B) [G.Faithful] [IsGroupoid B] :
    Quiver.IsThin (StructuredArrow b G) := by
  -- A structured-arrow morphism is determined by its right component; faithfulness identifies the
  -- right components after normalizing both commutativity equations in the groupoid target.
  intro X Y
  refine ⟨?_⟩
  intro f g
  apply StructuredArrow.hom_ext
  apply G.map_injective
  have hf :
      inv X.hom ≫ Y.hom = G.map f.right := by
    simpa [Category.assoc] using congrArg (fun k ↦ inv X.hom ≫ k) f.w
  have hg :
      inv X.hom ≫ Y.hom = G.map g.right := by
    simpa [Category.assoc] using congrArg (fun k ↦ inv X.hom ≫ k) g.w
  exact hf.symm.trans hg

/-- Helper for Chap08 Lemma 8 6 11: a faithful morphism makes every canonical slice base
change fibred in setoids. -/
theorem sliceTwoFibreProduct_isFibredInSetoids_of_faithful
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    {U : C} (G : ofFunctor (Over.forget U) ⟶ T) :
    IsFibredInSetoids (F.sliceTwoFibreProduct G).p := by
  -- Reduce total faithfulness to fiberwise faithfulness, then use the structured-arrow
  -- description of each slice fiber from Lemma 4.42.1.
  have hFiber : ∀ V : C, (fiberFunctor F V).Faithful :=
    (faithful_iff_fiberwise (F := F)).1 hFaithful
  refine { fiber_isThin := ?_ }
  intro f
  let E :
      StructuredArrow ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl)) (fiberFunctor F f.left) ≌
        ((F.sliceTwoFibreProduct G).p).Fiber f := by
    simpa [FibredInGroupoidsMor.sliceTwoFibreProduct] using
      (sliceTwoFibreProductStructuredArrowEquivFiber
        (G := FibredInGroupoidsMor.toBasedFunctor G)
        (F := FibredInGroupoidsMor.toBasedFunctor F)
        (f := f))
  letI : (fiberFunctor F f.left).Faithful := hFiber f.left
  letI :
      Quiver.IsThin
        (StructuredArrow ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl))
          (fiberFunctor F f.left)) :=
    structuredArrow_isThin_of_faithful
      ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl))
      (fiberFunctor F f.left)
  -- Transport thinness across the equivalence between the structured-arrow model and the fiber.
  exact isThin_of_faithful_to_thin E.symm.functor

omit [IsStackInGroupoids J T.p] in
/-- Helper for Chap08 Lemma 8 6 11: the sheaf hypothesis on a canonical slice iso-class
presheaf gives the owner-level stack-in-setoids condition for that slice. -/
theorem sliceTwoFibreProduct_isStackInSetoids_of_isoClassPresheaf_isSheaf
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    {U : C} (G : ofFunctor (Over.forget U) ⟶ T)
    (hG : Presheaf.IsSheaf (J.over U) ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf)) :
    IsStackInSetoids (J.over U) (F.sliceTwoFibreProduct G).p := by
  -- Lemma 8.6.3 applies after installing the setoid-fiber structure supplied by faithfulness.
  letI : IsFibredInSetoids (F.sliceTwoFibreProduct G).p :=
    sliceTwoFibreProduct_isFibredInSetoids_of_faithful F hFaithful G
  exact
    (isStackInSetoids_iff_isoClassPresheaf_isSheaf
      (J.over U) (F.sliceTwoFibreProduct G).p).2 hG

/-- Helper for Chap08 Lemma 8 6 11: a faithful morphism into a stack makes the fixed-cover
canonical descent functor on the source faithful. -/
theorem canonicalDescentFunctor_faithful_of_targetStack_and_faithful
    (F : FibredInGroupoidsMor X T)
    (hFaithful : (toBasedFunctor F).Faithful)
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor X.p).toDescentData (fun I : S.Arrow ↦ I.f)).Faithful := by
  let ΦX := (canonicalFiberPseudofunctor X.p).toDescentData (fun I : S.Arrow ↦ I.f)
  let ΦT := (canonicalFiberPseudofunctor T.p).toDescentData (fun I : S.Arrow ↦ I.f)
  have hTarget : ΦT.IsEquivalence := by
    -- The target stack gives equivalence of the target canonical descent functor on this cover.
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
        (J := J) (p := T.p)).1 inferInstance U S
  have hFiber : (fiberFunctor F U).Faithful :=
    (faithful_iff_fiberwise (F := F)).1 hFaithful U
  letI : ΦT.Faithful := hTarget.faithful
  letI : (fiberFunctor F U).Faithful := hFiber
  refine ⟨?_⟩
  intro x y f g hfg
  -- Reflect equality through the faithful fiber functor after checking it in target descent data.
  apply (fiberFunctor F U).map_injective
  apply ΦT.map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  let H := FibredInGroupoidsMor.toFibredCategoryMor F
  let ex := FibredCategoryMor.pullbackComparison H I.f x
  let ey := FibredCategoryMor.pullbackComparison H I.f y
  have hcomponent :
      (ΦX.map f).hom I = (ΦX.map g).hom I := by
    exact congrArg (fun η ↦ η.hom I) hfg
  have hpost :
      (ΦT.map ((fiberFunctor F U).map f)).hom I ≫ ey.hom =
        (ΦT.map ((fiberFunctor F U).map g)).hom I ≫ ey.hom := by
    -- The pullback-comparison naturality square changes equality of source restrictions into
    -- equality of target restrictions after applying `F`.
    have hnat_f :
        (ΦT.map ((fiberFunctor F U).map f)).hom I ≫ ey.hom =
          ex.hom ≫ (fiberFunctor F I.Y).map ((ΦX.map f).hom I) := by
      simpa only [ΦX, ΦT, H, ex, ey] using
        FibredCategoryMor.pullbackComparison_naturality_over_vertical H I.f f
    have hmiddle :
        ex.hom ≫ (fiberFunctor F I.Y).map ((ΦX.map f).hom I) =
          ex.hom ≫ (fiberFunctor F I.Y).map ((ΦX.map g).hom I) := by
      exact congrArg (fun k ↦ ex.hom ≫ (fiberFunctor F I.Y).map k) hcomponent
    have hnat_g :
        ex.hom ≫ (fiberFunctor F I.Y).map ((ΦX.map g).hom I) =
          (ΦT.map ((fiberFunctor F U).map g)).hom I ≫ ey.hom := by
      simpa only [ΦX, ΦT, H, ex, ey] using
        (FibredCategoryMor.pullbackComparison_naturality_over_vertical H I.f g).symm
    exact hnat_f.trans (hmiddle.trans hnat_g)
  exact (Iso.cancel_iso_hom_right _ _ ey).1 hpost
end FibredInGroupoidsMor

end

end CategoryTheory
