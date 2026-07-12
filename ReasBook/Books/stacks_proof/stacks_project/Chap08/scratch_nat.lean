import StacksProject_2024.Chap08.Lemma_8_8_1.ComparisonEquivalence
import StacksProject_2024.Chap08.Lemma_8_8_1.ForcedComparisonComponents
import Mathlib.Tactic.StacksAttribute

universe u v

namespace CategoryTheory

open Bicategory BasedFunctor FibredCategoryMor InducedCategory.Hom Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

noncomputable def realForcedHomIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J} (G₁ : X ⟶ Y₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    ((FibredCategoryMor.fiberFunctor K W).obj y) ≅ ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
  (FibredCategoryMor.fiberFunctor K W).mapIso cx.symm ≪≫ (cFiberComp G₁ c x) ≪≫
    (FibredCategoryMor.fiberFunctor K' W).mapIso cx

private theorem realComparisonComponent_comm
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (S : J.Cover W)
    (model : ∀ I : S.Arrow, Σ' (xI : X.p.Fiber I.Y),
      ((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅ (I.f ^*[canonicalPullbackChoice Y₁.p] y))
    (e : ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor K W).obj y)).obj I ≅
        (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor K' W).obj y)).obj I)
    (he : ∀ I : S.Arrow, e I =
        (FibredCategoryMor.pullbackComparison K I.f y) ≪≫
        realForcedHomIso G₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y) (model I).1 (model I).2 ≪≫
        (FibredCategoryMor.pullbackComparison K' I.f y).symm) :
    ∀ ⦃Z : C⦄ (q : Z ⟶ W) ⦃i₁ i₂ : S.Arrow⦄ (f₁ : Z ⟶ i₁.Y) (f₂ : Z ⟶ i₂.Y)
      (hf₁ : f₁ ≫ i₁.f = q) (hf₂ : f₂ ≫ i₂.f = q),
      ((canonicalFiberPseudofunctor Y₂.p).map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor K' W).obj y)).hom q f₁ f₂ hf₁ hf₂ =
        (((canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor K W).obj y)).hom q f₁ f₂ hf₁ hf₂ ≫
          ((canonicalFiberPseudofunctor Y₂.p).map f₂.op.toLoc).toFunctor.map (e i₂).hom :=
  sorry

noncomputable def realComparisonComponent
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) :
    ((FibredCategoryMor.fiberFunctor K W).obj y) ≅ ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
  let hsurj := hG₁.locallyEssentiallySurjectiveOnObjects W y
  let S : J.Cover W := hsurj.choose
  let model : ∀ I : S.Arrow, Σ' (xI : X.p.Fiber I.Y),
      ((FibredCategoryMor.fiberFunctor G₁ I.Y).obj xI) ≅ (I.f ^*[canonicalPullbackChoice Y₁.p] y) :=
    fun I => ⟨(hsurj.choose_spec I).choose, (hsurj.choose_spec I).choose_spec.some⟩
  let Φ := (canonicalFiberPseudofunctor Y₂.p).toDescentData (fun I : S.Arrow ↦ I.f)
  let e : ∀ I : S.Arrow, (Φ.obj ((FibredCategoryMor.fiberFunctor K W).obj y)).obj I ≅
        (Φ.obj ((FibredCategoryMor.fiberFunctor K' W).obj y)).obj I :=
    fun I => (FibredCategoryMor.pullbackComparison K I.f y) ≪≫
        realForcedHomIso G₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y) (model I).1 (model I).2 ≪≫
        (FibredCategoryMor.pullbackComparison K' I.f y).symm
  let ddIso : Φ.obj ((FibredCategoryMor.fiberFunctor K W).obj y) ≅
      Φ.obj ((FibredCategoryMor.fiberFunctor K' W).obj y) :=
    Pseudofunctor.DescentData.isoMk e
      (realComparisonComponent_comm G₁ hG₁ c y S model e (fun I => rfl))
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence (J := J) (p := Y₂.p)).1 inferInstance W S
  (Functor.FullyFaithful.ofFullyFaithful Φ).preimageIso ddIso

-- KEY: pullback of rcc along a cover arrow equals (e I).hom (existential model form)
private theorem realComparisonComponent_pullback_eq
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W)
    (I : (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose.Arrow) :
    ∃ (x : X.p.Fiber I.Y)
      (cx : ((FibredCategoryMor.fiberFunctor G₁ I.Y).obj x) ≅
        (I.f ^*[canonicalPullbackChoice Y₁.p] y)),
    ((canonicalFiberPseudofunctor Y₂.p).map I.f.op.toLoc).toFunctor.map
        (realComparisonComponent G₁ hG₁ c y).hom =
      (FibredCategoryMor.pullbackComparison K I.f y).hom ≫
        realForcedHom G₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y) x cx ≫
        (FibredCategoryMor.pullbackComparison K' I.f y).inv := by
  refine ⟨((hG₁.locallyEssentiallySurjectiveOnObjects W y).choose_spec I).choose,
    ((hG₁.locallyEssentiallySurjectiveOnObjects W y).choose_spec I).choose_spec.some, ?_⟩
  dsimp only [realComparisonComponent]
  rw [Functor.FullyFaithful.preimageIso_hom]
  set Φ := (canonicalFiberPseudofunctor Y₂.p).toDescentData
    (fun I : (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose.Arrow ↦ I.f) with hΦ
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence (J := J) (p := Y₂.p)).1
      inferInstance W (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose
  -- M_{I.f}.map (preimage g) = (Φ.map (preimage g)).hom I = (ddIso.hom).hom I = (e I).hom
  change (Φ.map ((Functor.FullyFaithful.ofFullyFaithful Φ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem realComparisonComponent_eq_forced.{w}
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, w, max u v} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {W : C} (y : Y₁.p.Fiber W) (x : X.p.Fiber W)
    (cx : ((FibredCategoryMor.fiberFunctor G₁ W).obj x) ≅ y) :
    (realComparisonComponent G₁ hG₁ c y).hom = realForcedHom G₁ c y x cx := by
  apply stack_cover_hom_ext (J := J) Y₂ (hG₁.locallyEssentiallySurjectiveOnObjects W y).choose
  intro I
  obtain ⟨xI, cxI, hI⟩ := realComparisonComponent_pullback_eq G₁ hG₁ c y I
  rw [hI, Mf_realForcedHom_pullback G₁ c I.f y x cx]
  -- Both middles are realForcedHom over (I.f^*y) for two models; equal by model_indep.
  rw [realForcedHom_model_indep G₁ hG₁ c (I.f ^*[canonicalPullbackChoice Y₁.p] y)
    xI cxI
    (I.f ^*[canonicalPullbackChoice X.p] x)
    ((FibredCategoryMor.pullbackComparison G₁ I.f x).symm ≪≫
      (((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.mapIso cx))]

-- TARGET: prove this naturality theorem (replace `sorry`).
private theorem realComparisonComponent_naturality.{w}
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver.{u, v, w, max u v} J}
    (G₁ : X ⟶ Y₁) (hG₁ : FibredCategoryMor.IsStackification G₁)
    {K K' : Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver} (c : (G₁ ≫ K) ≅ (G₁ ≫ K'))
    {T T' : Y₁.S} (φ : T ⟶ T') :
    (FibredCategoryMor.toFunctor K).map φ ≫ (realComparisonComponent G₁ hG₁ c ⟨T', rfl⟩).hom.1 =
      (realComparisonComponent G₁ hG₁ c ⟨T, rfl⟩).hom.1 ≫
        (FibredCategoryMor.toFunctor K').map φ := by
  sorry

end

end CategoryTheory
