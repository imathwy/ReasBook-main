import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.MapIdCancellation
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.LocalModelComparison
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.Basic

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The pulled local model comparison is compatible with a vertical map on the base object.

This is the HomExtension-only core of pullback-comparison vertical naturality: after replacing
the local models for `f ^* yᵢ` by the pulled local models from `yᵢ`, the middle vertical
HomExtension is the one obtained by pulling back the original vertical HomExtension. -/
theorem stackificationLiftPulledModelComparisonIso_verticalMap
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U)
    {y₀ y₁ : S'.p.Fiber U} (d : y₀ ⟶ y₁)
    (I : ((stackificationLiftVerticalCommonCover (J := J) G hG y₀ y₁).pullback f).Arrow) :
    let I₀ : (stackificationLiftPulledObjectCover (J := J) G hG f y₀).Arrow :=
      ⟨I.Y, I.f, by
        dsimp [stackificationLiftPulledObjectCover,
          stackificationLiftVerticalCommonCover] at I
        exact I.base.hf.1⟩
    let I₁ : (stackificationLiftPulledObjectCover (J := J) G hG f y₁).Arrow :=
      ⟨I.Y, I.f, by
        dsimp [stackificationLiftPulledObjectCover,
          stackificationLiftVerticalCommonCover] at I
        exact I.base.hf.2⟩
    let Iv : (stackificationLiftVerticalCommonCover (J := J) G hG
        (f ^*[canonicalPullbackChoice S'.p] y₀)
        (f ^*[canonicalPullbackChoice S'.p] y₁)).Arrow :=
      ⟨I.Y, I.f, by
        exact ⟨(stackificationLiftPulledToObjectCover (J := J) G hG f y₀ I₀).hf,
          (stackificationLiftPulledToObjectCover (J := J) G hG f y₁ I₁).hf⟩⟩
    let Hbase := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₀ I₀).1
      (stackificationLiftPulledObjectCoverModel (J := J) G hG f y₁ I₁).1
      ((stackificationLiftObjectModel (J := J) G hG y₀ I₀.base).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I₀.base.f.op.toLoc).toFunctor.map d ≫
        (stackificationLiftObjectModel (J := J) G hG y₁ I₁.base).2.inv)
    (stackificationLiftPulledModelComparisonIso X G hG F f y₀ I₀).hom ≫
        Hbase ≫
        (stackificationLiftPulledModelComparisonIso X G hG F f y₁ I₁).inv =
      stackificationLiftHomExtensionFiberMap X G hG F
        (stackificationLiftObjectModel (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y₀)
          (stackificationLiftVerticalCommonCover_left (J := J) G hG
            (f ^*[canonicalPullbackChoice S'.p] y₀)
            (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).1
        (stackificationLiftObjectModel (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y₁)
          (stackificationLiftVerticalCommonCover_right (J := J) G hG
            (f ^*[canonicalPullbackChoice S'.p] y₀)
            (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).1
        ((stackificationLiftObjectModel (J := J) G hG
            (f ^*[canonicalPullbackChoice S'.p] y₀)
            (stackificationLiftVerticalCommonCover_left (J := J) G hG
              (f ^*[canonicalPullbackChoice S'.p] y₀)
              (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).2.hom ≫
          ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d) ≫
          (stackificationLiftObjectModel (J := J) G hG
            (f ^*[canonicalPullbackChoice S'.p] y₁)
            (stackificationLiftVerticalCommonCover_right (J := J) G hG
              (f ^*[canonicalPullbackChoice S'.p] y₀)
              (f ^*[canonicalPullbackChoice S'.p] y₁) Iv)).2.inv) := by
  intro I₀ I₁ Iv Hbase
  dsimp only [Hbase]
  rw [stackificationLiftPulledModelComparisonIso_hom,
    stackificationLiftPulledModelComparisonIso_inv]
  dsimp [stackificationLiftPulledToObjectCover,
    stackificationLiftVerticalCommonCover_left,
    stackificationLiftVerticalCommonCover_right]
  rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F]
  rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F]
  congr 1
  dsimp [stackificationLiftPulledObjectCoverModel]
  simp only [Category.assoc]
  let ez₀ :=
    (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y₀)
      { Y := I₀.Y, f := I₀.f, hf := by
          exact (stackificationLiftPulledToObjectCover (J := J) G hG f y₀ I₀).hf }).2
  let ez₁ :=
    (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y₁)
      { Y := I₁.Y, f := I₁.f, hf := by
          exact (stackificationLiftPulledToObjectCover (J := J) G hG f y₁ I₁).hf }).2
  let cy₀ := (stackificationLiftObjectModel (J := J) G hG y₀ I₀.base).2
  let cy₁ := (stackificationLiftObjectModel (J := J) G hG y₁ I₁.base).2
  let κ₀ := mapCompAppIso S'.p f I₀.f (I₀.f ≫ f)
    (FibredCategoryMor.comp_toLoc_eq f I₀.f (I₀.f ≫ f) rfl) y₀
  let κ₁ := mapCompAppIso S'.p f I₁.f (I₁.f ≫ f)
    (FibredCategoryMor.comp_toLoc_eq f I₁.f (I₁.f ≫ f) rfl) y₁
  let N := ((canonicalFiberPseudofunctor S'.p).map
    (f.op.toLoc ≫ I₀.f.op.toLoc)).toFunctor.map d
  let Mfd := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
    (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map d)
  have hκ : κ₀.inv ≫ N ≫ κ₁.hom = Mfd := by
    let FpS := canonicalFiberPseudofunctor S'.p
    let κ := FpS.mapComp' f.op.toLoc I.f.op.toLoc
      (f.op.toLoc ≫ I.f.op.toLoc) rfl
    have hnat := κ.hom.toNatTrans.naturality d
    have hκ' :
        κ.inv.toNatTrans.app y₀ ≫
            (FpS.map (f.op.toLoc ≫ I.f.op.toLoc)).toFunctor.map d ≫
              κ.hom.toNatTrans.app y₁ =
          (FpS.map f.op.toLoc ≫ FpS.map I.f.op.toLoc).toFunctor.map d := by
      calc
        κ.inv.toNatTrans.app y₀ ≫
            (FpS.map (f.op.toLoc ≫ I.f.op.toLoc)).toFunctor.map d ≫
              κ.hom.toNatTrans.app y₁ =
          κ.inv.toNatTrans.app y₀ ≫
            ((FpS.map (f.op.toLoc ≫ I.f.op.toLoc)).toFunctor.map d ≫
              κ.hom.toNatTrans.app y₁) := by
            rfl
        _ = κ.inv.toNatTrans.app y₀ ≫
              (κ.hom.toNatTrans.app y₀ ≫
                (FpS.map f.op.toLoc ≫ FpS.map I.f.op.toLoc).toFunctor.map d) := by
            rw [hnat]
        _ = (κ.inv.toNatTrans.app y₀ ≫ κ.hom.toNatTrans.app y₀) ≫
              (FpS.map f.op.toLoc ≫ FpS.map I.f.op.toLoc).toFunctor.map d := by
            simp only [Category.assoc]
        _ = 𝟙 _ ≫
              (FpS.map f.op.toLoc ≫ FpS.map I.f.op.toLoc).toFunctor.map d := by
            rw [Cat.Hom.inv_hom_id_toNatTrans_app]
        _ = (FpS.map f.op.toLoc ≫ FpS.map I.f.op.toLoc).toFunctor.map d := by
            rw [Category.id_comp]
    simpa [κ₀, κ₁, κ, N, Mfd, mapCompAppIso, Cat.Hom.comp_toFunctor] using hκ'
  change
    ((ez₀.hom ≫ κ₀.inv ≫ cy₀.inv) ≫ cy₀.hom ≫ N ≫
        cy₁.inv ≫ cy₁.hom ≫ κ₁.hom ≫ ez₁.inv) =
      ez₀.hom ≫ Mfd ≫ ez₁.inv
  calc
    ((ez₀.hom ≫ κ₀.inv ≫ cy₀.inv) ≫ cy₀.hom ≫ N ≫
        cy₁.inv ≫ cy₁.hom ≫ κ₁.hom ≫ ez₁.inv) =
        ez₀.hom ≫ κ₀.inv ≫ (cy₀.inv ≫ cy₀.hom) ≫
          N ≫ (cy₁.inv ≫ cy₁.hom) ≫ κ₁.hom ≫ ez₁.inv := by
      simp only [Category.assoc]
    _ = ez₀.hom ≫ κ₀.inv ≫ 𝟙 _ ≫ N ≫
          (cy₁.inv ≫ cy₁.hom) ≫ κ₁.hom ≫ ez₁.inv := by
      exact congrArg
        (fun t => ez₀.hom ≫ κ₀.inv ≫ t ≫ N ≫
          (cy₁.inv ≫ cy₁.hom) ≫ κ₁.hom ≫ ez₁.inv)
        cy₀.inv_hom_id
    _ = ez₀.hom ≫ κ₀.inv ≫ 𝟙 _ ≫ N ≫ 𝟙 _ ≫ κ₁.hom ≫ ez₁.inv := by
      exact congrArg
        (fun t => ez₀.hom ≫ κ₀.inv ≫ 𝟙 _ ≫ N ≫ t ≫ κ₁.hom ≫ ez₁.inv)
        cy₁.inv_hom_id
    _ = ez₀.hom ≫ (κ₀.inv ≫ N ≫ κ₁.hom) ≫ ez₁.inv := by
      simp only [Category.assoc, Category.id_comp]
    _ = ez₀.hom ≫ Mfd ≫ ez₁.inv := by
      rw [hκ]
      rfl

end

end CategoryTheory
