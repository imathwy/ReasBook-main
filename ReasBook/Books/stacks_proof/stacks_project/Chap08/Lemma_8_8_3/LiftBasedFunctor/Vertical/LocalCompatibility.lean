import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.LocalMap

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The small compatibility target for the vertical local maps in Chap08 Lemma 8 8 3.

Proving this proposition is the next blocker before the local maps can be packaged as a morphism
of descent data and glued to a global fiber morphism. -/
abbrev stackificationLiftVerticalLocalMapCommTarget
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y') : Prop :=
  ∀ ⦃V : C⦄
    (q : V ⟶ U)
    ⦃I₁ I₂ : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow⦄
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q),
    ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
        (stackificationLiftVerticalLocalMap X G hG F d I₁) ≫
      (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow ↦ I.f)).obj
        (stackificationLiftObjectGlued X G hG F y')).hom q f₁ f₂ hf₁ hf₂ =
    (((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow ↦ I.f)).obj
      (stackificationLiftObjectGlued X G hG F y)).hom q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
        (stackificationLiftVerticalLocalMap X G hG F d I₂)


/-- Helper for Chap08 Lemma 8 8 3: the local vertical maps commute with the descent
transition maps on every common refinement. -/
theorem stackificationLiftVerticalLocalMap_comm
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y') :
    stackificationLiftVerticalLocalMapCommTarget X G hG F d := by
  classical
  intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
  let Iy₁ := stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₁
  let Iy₂ := stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₂
  let Iy'₁ := stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₁
  let Iy'₂ := stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₂
  let ly₁ := stackificationLiftObjectGluedLocalIso X G hG F y Iy₁
  let ly₂ := stackificationLiftObjectGluedLocalIso X G hG F y Iy₂
  let ly'₁ := stackificationLiftObjectGluedLocalIso X G hG F y' Iy'₁
  let ly'₂ := stackificationLiftObjectGluedLocalIso X G hG F y' Iy'₂
  let m₁ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y Iy₁).1
      (stackificationLiftObjectModel (J := J) G hG y' Iy'₁).1
      ((stackificationLiftObjectModel (J := J) G hG y Iy₁).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I₁.f.op.toLoc).toFunctor.map d ≫
        (stackificationLiftObjectModel (J := J) G hG y' Iy'₁).2.inv)
  let m₂ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y Iy₂).1
      (stackificationLiftObjectModel (J := J) G hG y' Iy'₂).1
      ((stackificationLiftObjectModel (J := J) G hG y Iy₂).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I₂.f.op.toLoc).toFunctor.map d ≫
        (stackificationLiftObjectModel (J := J) G hG y' Iy'₂).2.inv)
  let Ty :=
    stackificationLiftObjectTransition X G hG F y
      (stackificationLiftObjectCover (J := J) G hG y)
      (stackificationLiftObjectModel (J := J) G hG y) q
      (I₁ := Iy₁) (I₂ := Iy₂) f₁ f₂ hf₁ hf₂
  let Ty' :=
    stackificationLiftObjectTransition X G hG F y'
      (stackificationLiftObjectCover (J := J) G hG y')
      (stackificationLiftObjectModel (J := J) G hG y') q
      (I₁ := Iy'₁) (I₂ := Iy'₂) f₁ f₂ hf₁ hf₂
  have htarget :=
    stackificationLiftObjectGluedLocalIso_inv_comm X G hG F y' q
      (I₁ := Iy'₁) (I₂ := Iy'₂) f₁ f₂ hf₁ hf₂
  have hsource :=
    stackificationLiftObjectGluedLocalIso_comm X G hG F y q
      (I₁ := Iy₁) (I₂ := Iy₂) f₁ f₂ hf₁ hf₂
  have hmiddle :
      ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map m₁ ≫ Ty' =
        Ty ≫ ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map m₂ := by
    let x₁ := (stackificationLiftObjectModel (J := J) G hG y Iy₁).1
    let x₂ := (stackificationLiftObjectModel (J := J) G hG y Iy₂).1
    let x₁' := (stackificationLiftObjectModel (J := J) G hG y' Iy'₁).1
    let x₂' := (stackificationLiftObjectModel (J := J) G hG y' Iy'₂).1
    let cy₁ := (stackificationLiftObjectModel (J := J) G hG y Iy₁).2
    let cy₂ := (stackificationLiftObjectModel (J := J) G hG y Iy₂).2
    let cy₁' := (stackificationLiftObjectModel (J := J) G hG y' Iy'₁).2
    let cy₂' := (stackificationLiftObjectModel (J := J) G hG y' Iy'₂).2
    let α₁ := cy₁.hom ≫
      ((canonicalFiberPseudofunctor S'.p).map I₁.f.op.toLoc).toFunctor.map d ≫ cy₁'.inv
    let α₂ := cy₂.hom ≫
      ((canonicalFiberPseudofunctor S'.p).map I₂.f.op.toLoc).toFunctor.map d ≫ cy₂'.inv
    let cG₁ := FibredCategoryMor.pullbackComparison G f₁ x₁
    let cG₂ := FibredCategoryMor.pullbackComparison G f₂ x₂
    let cG₁' := FibredCategoryMor.pullbackComparison G f₁ x₁'
    let cG₂' := FibredCategoryMor.pullbackComparison G f₂ x₂'
    let cF₁ := FibredCategoryMor.pullbackComparison F f₁ x₁
    let cF₂ := FibredCategoryMor.pullbackComparison F f₂ x₂
    let cF₁' := FibredCategoryMor.pullbackComparison F f₁ x₁'
    let cF₂' := FibredCategoryMor.pullbackComparison F f₂ x₂'
    let δ₁ := cG₁.inv ≫
      ((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor.map α₁ ≫ cG₁'.hom
    let δ₂ := cG₂.inv ≫
      ((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor.map α₂ ≫ cG₂'.hom
    let e₁ := stackificationLiftObjectModelPullbackIso (J := J) G y
      (stackificationLiftObjectCover (J := J) G hG y)
      (stackificationLiftObjectModel (J := J) G hG y) q Iy₁ f₁ hf₁
    let e₂ := stackificationLiftObjectModelPullbackIso (J := J) G y
      (stackificationLiftObjectCover (J := J) G hG y)
      (stackificationLiftObjectModel (J := J) G hG y) q Iy₂ f₂ hf₂
    let e₁' := stackificationLiftObjectModelPullbackIso (J := J) G y'
      (stackificationLiftObjectCover (J := J) G hG y')
      (stackificationLiftObjectModel (J := J) G hG y') q Iy'₁ f₁ hf₁
    let e₂' := stackificationLiftObjectModelPullbackIso (J := J) G y'
      (stackificationLiftObjectCover (J := J) G hG y')
      (stackificationLiftObjectModel (J := J) G hG y') q Iy'₂ f₂ hf₂
    let β := e₁.hom ≫ e₂.inv
    let β' := e₁'.hom ≫ e₂'.inv
    have hδ₁_src :
        cG₁.hom ≫ δ₁ ≫ cG₁'.inv =
          ((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor.map α₁ := by
      dsimp only [δ₁]
      rw [← Category.assoc]
      rw [cG₁.hom_inv_id_assoc]
      rw [Iso.comp_inv_eq cG₁']
      rfl
    have hδ₂_src :
        cG₂.hom ≫ δ₂ ≫ cG₂'.inv =
          ((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor.map α₂ := by
      dsimp only [δ₂]
      rw [← Category.assoc]
      rw [cG₂.hom_inv_id_assoc]
      rw [Iso.comp_inv_eq cG₂']
      rfl
    have hm₁ :
        ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map m₁ =
          cF₁.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁)
              (f₁ ^*[canonicalPullbackChoice S.p] x₁') δ₁ ≫
            cF₁'.inv := by
      have hmap :=
        stackificationLiftHomExtensionFiberMap_pullback X G hG F f₁
          (x := x₁) (y := x₁') α₁
      have happ :=
        stackificationLiftHomExtension_app_pullbackComparison X G hG F f₁
          (x := x₁) (y := x₁') δ₁
      have hfirst :
          ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map m₁ =
            (stackificationLiftHomExtension X G hG F x₁ x₁').app
              (op (Over.mk f₁))
              (((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor.map α₁) := by
        simpa [m₁, α₁, x₁, x₁'] using hmap.symm
      have hsecond :
          (stackificationLiftHomExtension X G hG F x₁ x₁').app
              (op (Over.mk f₁))
              (((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor.map α₁) =
            cF₁.hom ≫
              stackificationLiftHomExtensionFiberMap X G hG F
                (f₁ ^*[canonicalPullbackChoice S.p] x₁)
                (f₁ ^*[canonicalPullbackChoice S.p] x₁') δ₁ ≫
              cF₁'.inv := by
        exact (congrArg
          ((stackificationLiftHomExtension X G hG F x₁ x₁').app (op (Over.mk f₁)))
          hδ₁_src).symm.trans
          (by simpa only [cG₁, cG₁', cF₁, cF₁', x₁, x₁'] using happ)
      exact hfirst.trans hsecond
    have hm₂ :
        ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map m₂ =
          cF₂.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₂ ^*[canonicalPullbackChoice S.p] x₂)
              (f₂ ^*[canonicalPullbackChoice S.p] x₂') δ₂ ≫
            cF₂'.inv := by
      have hmap :=
        stackificationLiftHomExtensionFiberMap_pullback X G hG F f₂
          (x := x₂) (y := x₂') α₂
      have happ :=
        stackificationLiftHomExtension_app_pullbackComparison X G hG F f₂
          (x := x₂) (y := x₂') δ₂
      have hfirst :
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map m₂ =
            (stackificationLiftHomExtension X G hG F x₂ x₂').app
              (op (Over.mk f₂))
              (((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor.map α₂) := by
        simpa [m₂, α₂, x₂] using hmap.symm
      have hsecond :
          (stackificationLiftHomExtension X G hG F x₂ x₂').app
              (op (Over.mk f₂))
              (((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor.map α₂) =
            cF₂.hom ≫
              stackificationLiftHomExtensionFiberMap X G hG F
                (f₂ ^*[canonicalPullbackChoice S.p] x₂)
                (f₂ ^*[canonicalPullbackChoice S.p] x₂') δ₂ ≫
              cF₂'.inv := by
        exact (congrArg
          ((stackificationLiftHomExtension X G hG F x₂ x₂').app (op (Over.mk f₂)))
          hδ₂_src).symm.trans
          (by simpa only [cG₂, cG₂', cF₂, cF₂', x₂, x₂'] using happ)
      exact hfirst.trans hsecond
    have hbranch₁ : δ₁ ≫ e₁'.hom = e₁.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d := by
      dsimp only [δ₁, e₁, e₁', α₁,
        stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover_right]
      unfold stackificationLiftObjectModelPullbackIso
      let Mf1 := ((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor
      let MI1 := ((canonicalFiberPseudofunctor S'.p).map I₁.f.op.toLoc).toFunctor
      let Mq := ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor
      change
        (cG₁.inv ≫ Mf1.map (cy₁.hom ≫ (MI1.map d ≫ cy₁'.inv)) ≫ cG₁'.hom) ≫
            ((cG₁'.symm ≪≫ Mf1.mapIso cy₁') ≪≫
                (mapCompAppIso S'.p I₁.f f₁ q
                  (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) y').symm).hom =
          ((cG₁.symm ≪≫ Mf1.mapIso cy₁) ≪≫
                (mapCompAppIso S'.p I₁.f f₁ q
                  (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) y).symm).hom ≫
            Mq.map d
      rw [Mf1.map_comp, Mf1.map_comp]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, mapCompAppIso]
      let κ := (canonicalFiberPseudofunctor S'.p).mapComp' I₁.f.op.toLoc
        f₁.op.toLoc q.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)
      have hnat :
          Mf1.map (MI1.map d) ≫ κ.inv.toNatTrans.app y' =
            κ.inv.toNatTrans.app y ≫ Mq.map d := by
        simpa [κ, Mf1, MI1, Mq] using
          ((canonicalFiberPseudofunctor S'.p).mapComp'_inv_naturality
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) d)
      have hcancel :
          Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫ Mf1.map cy₁'.hom =
            𝟙 (Mf1.obj (MI1.obj y')) := by
        calc
          Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫ Mf1.map cy₁'.hom =
              Mf1.map cy₁'.inv ≫ (cG₁'.hom ≫ cG₁'.inv) ≫
                Mf1.map cy₁'.hom := by
                simp only [Category.assoc]
          _ = Mf1.map cy₁'.inv ≫ 𝟙 _ ≫ Mf1.map cy₁'.hom := by
                exact congrArg
                  (fun t => Mf1.map cy₁'.inv ≫ t ≫ Mf1.map cy₁'.hom)
                  cG₁'.hom_inv_id
          _ = Mf1.map cy₁'.inv ≫ Mf1.map cy₁'.hom := by
                simp only [Category.assoc, Category.id_comp, Category.comp_id]
          _ = Mf1.map (cy₁'.inv ≫ cy₁'.hom) := by
                exact (Mf1.map_comp cy₁'.inv cy₁'.hom).symm
          _ = Mf1.map (𝟙 _) := by
                exact congrArg Mf1.map cy₁'.inv_hom_id
          _ = 𝟙 _ := by
                rw [Functor.map_id]
      have hleft :
          (cG₁.inv ≫ (Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
              Mf1.map cy₁'.inv) ≫ cG₁'.hom) ≫
              (cG₁'.inv ≫ Mf1.map cy₁'.hom) ≫ κ.inv.toNatTrans.app y' =
            cG₁.inv ≫ Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
              κ.inv.toNatTrans.app y' := by
        calc
          (cG₁.inv ≫ (Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
              Mf1.map cy₁'.inv) ≫ cG₁'.hom) ≫
              (cG₁'.inv ≫ Mf1.map cy₁'.hom) ≫ κ.inv.toNatTrans.app y' =
            cG₁.inv ≫ Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
              (Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫
                Mf1.map cy₁'.hom) ≫ κ.inv.toNatTrans.app y' := by
              simp only [Category.assoc]
          _ = cG₁.inv ≫ Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
              κ.inv.toNatTrans.app y' := by
              calc
                cG₁.inv ≫ Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
                    (Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫
                      Mf1.map cy₁'.hom) ≫ κ.inv.toNatTrans.app y' =
                  cG₁.inv ≫ Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
                      𝟙 _ ≫ κ.inv.toNatTrans.app y' := by
                    exact congrArg
                      (fun t => cG₁.inv ≫ Mf1.map cy₁.hom ≫
                        Mf1.map (MI1.map d) ≫ t ≫ κ.inv.toNatTrans.app y')
                      hcancel
                _ = cG₁.inv ≫ Mf1.map cy₁.hom ≫ Mf1.map (MI1.map d) ≫
                    κ.inv.toNatTrans.app y' := by
                    simp only [Category.id_comp, Category.comp_id]
      exact hleft.trans (by
        simpa only [Category.assoc] using
          congrArg (fun t => cG₁.inv ≫ Mf1.map cy₁.hom ≫ t) hnat)
    have hbranch₂ :
        ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d ≫ e₂'.inv =
          e₂.inv ≫ δ₂ := by
      dsimp only [δ₂, e₂, e₂', α₂,
        stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover_right]
      unfold stackificationLiftObjectModelPullbackIso
      let Mf2 := ((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor
      let MI2 := ((canonicalFiberPseudofunctor S'.p).map I₂.f.op.toLoc).toFunctor
      let Mq := ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor
      change
        Mq.map d ≫
            ((cG₂'.symm ≪≫ Mf2.mapIso cy₂') ≪≫
                (mapCompAppIso S'.p I₂.f f₂ q
                  (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) y').symm).inv =
          ((cG₂.symm ≪≫ Mf2.mapIso cy₂) ≪≫
                (mapCompAppIso S'.p I₂.f f₂ q
                  (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) y).symm).inv ≫
            cG₂.inv ≫ Mf2.map (cy₂.hom ≫ (MI2.map d ≫ cy₂'.inv)) ≫ cG₂'.hom
      rw [Mf2.map_comp, Mf2.map_comp]
      simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, mapCompAppIso]
      let κ := (canonicalFiberPseudofunctor S'.p).mapComp' I₂.f.op.toLoc
        f₂.op.toLoc q.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)
      have hnat :
          Mq.map d ≫ κ.hom.toNatTrans.app y' =
            κ.hom.toNatTrans.app y ≫ Mf2.map (MI2.map d) := by
        simpa [κ, Mf2, MI2, Mq] using
          ((canonicalFiberPseudofunctor S'.p).mapComp'_hom_naturality
            I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) d)
      have hcancel :
          Mf2.map cy₂.inv ≫ cG₂.hom ≫ cG₂.inv ≫ Mf2.map cy₂.hom =
            𝟙 (Mf2.obj (I₂.f ^*[canonicalPullbackChoice S'.p] y)) := by
        calc
          Mf2.map cy₂.inv ≫ cG₂.hom ≫ cG₂.inv ≫ Mf2.map cy₂.hom =
              Mf2.map cy₂.inv ≫ (cG₂.hom ≫ cG₂.inv) ≫
                Mf2.map cy₂.hom := by
                simp only [Category.assoc]
          _ = Mf2.map cy₂.inv ≫ 𝟙 _ ≫ Mf2.map cy₂.hom := by
                exact congrArg
                  (fun t => Mf2.map cy₂.inv ≫ t ≫ Mf2.map cy₂.hom)
                  cG₂.hom_inv_id
          _ = Mf2.map cy₂.inv ≫ Mf2.map cy₂.hom := by
                simp only [Category.assoc, Category.id_comp, Category.comp_id]
          _ = Mf2.map (cy₂.inv ≫ cy₂.hom) := by
                exact (Mf2.map_comp cy₂.inv cy₂.hom).symm
          _ = Mf2.map (𝟙 _) := by
                exact congrArg Mf2.map cy₂.inv_hom_id
          _ = 𝟙 _ := by
                rw [Functor.map_id]
      have hright :
          κ.hom.toNatTrans.app y ≫ Mf2.map cy₂.inv ≫ cG₂.hom ≫ cG₂.inv ≫
              (Mf2.map cy₂.hom ≫ Mf2.map (MI2.map d) ≫ Mf2.map cy₂'.inv) ≫
                cG₂'.hom =
            κ.hom.toNatTrans.app y ≫ Mf2.map (MI2.map d) ≫
              Mf2.map cy₂'.inv ≫ cG₂'.hom := by
        calc
          κ.hom.toNatTrans.app y ≫ Mf2.map cy₂.inv ≫ cG₂.hom ≫ cG₂.inv ≫
              (Mf2.map cy₂.hom ≫ Mf2.map (MI2.map d) ≫ Mf2.map cy₂'.inv) ≫
                cG₂'.hom =
            κ.hom.toNatTrans.app y ≫
              (Mf2.map cy₂.inv ≫ cG₂.hom ≫ cG₂.inv ≫ Mf2.map cy₂.hom) ≫
                Mf2.map (MI2.map d) ≫ Mf2.map cy₂'.inv ≫ cG₂'.hom := by
              simp only [Category.assoc]
          _ =
            κ.hom.toNatTrans.app y ≫ 𝟙 _ ≫
                Mf2.map (MI2.map d) ≫ Mf2.map cy₂'.inv ≫ cG₂'.hom := by
              exact congrArg
                (fun t => κ.hom.toNatTrans.app y ≫ t ≫
                  Mf2.map (MI2.map d) ≫ Mf2.map cy₂'.inv ≫ cG₂'.hom)
                hcancel
          _ =
            κ.hom.toNatTrans.app y ≫ Mf2.map (MI2.map d) ≫
              Mf2.map cy₂'.inv ≫ cG₂'.hom := by
              simp only [Category.id_comp, Category.comp_id]
      have hmain :
          Mq.map d ≫ κ.hom.toNatTrans.app y' ≫ Mf2.map cy₂'.inv ≫ cG₂'.hom =
            (κ.hom.toNatTrans.app y ≫ Mf2.map cy₂.inv ≫ cG₂.hom) ≫ cG₂.inv ≫
              (Mf2.map cy₂.hom ≫ Mf2.map (MI2.map d) ≫ Mf2.map cy₂'.inv) ≫
                cG₂'.hom := by
        calc
          Mq.map d ≫ κ.hom.toNatTrans.app y' ≫ Mf2.map cy₂'.inv ≫ cG₂'.hom =
              (κ.hom.toNatTrans.app y ≫ Mf2.map (MI2.map d)) ≫
                Mf2.map cy₂'.inv ≫ cG₂'.hom := by
              simpa only [← Category.assoc] using
                congrArg (fun t => t ≫ Mf2.map cy₂'.inv ≫ cG₂'.hom) hnat
          _ =
            (κ.hom.toNatTrans.app y ≫ Mf2.map cy₂.inv ≫ cG₂.hom) ≫ cG₂.inv ≫
                (Mf2.map cy₂.hom ≫ Mf2.map (MI2.map d) ≫ Mf2.map cy₂'.inv) ≫
                  cG₂'.hom := by
              simpa only [← Category.assoc] using hright.symm
      simpa only [κ] using hmain
    have hsource_square : δ₁ ≫ β' = β ≫ δ₂ := by
      dsimp only [β, β']
      have hleft :
          δ₁ ≫ e₁'.hom ≫ e₂'.inv =
            e₁.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d ≫
                e₂'.inv := by
        calc
          δ₁ ≫ e₁'.hom ≫ e₂'.inv =
              (δ₁ ≫ e₁'.hom) ≫ e₂'.inv := by
                exact (Category.assoc δ₁ e₁'.hom e₂'.inv).symm
          _ =
              (e₁.hom ≫
                ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d) ≫
                  e₂'.inv := by
                exact congrArg (fun t => t ≫ e₂'.inv) hbranch₁
          _ =
              e₁.hom ≫
                ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d ≫
                  e₂'.inv := by
                simp only [Category.assoc]
      have hright :
          e₁.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d ≫
                e₂'.inv =
            e₁.hom ≫ e₂.inv ≫ δ₂ := by
        calc
          e₁.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d ≫
                e₂'.inv =
            e₁.hom ≫
              (((canonicalFiberPseudofunctor S'.p).map q.op.toLoc).toFunctor.map d ≫
                e₂'.inv) := by
              simp only [Category.assoc]
          _ = e₁.hom ≫ (e₂.inv ≫ δ₂) := by
              exact congrArg (fun t => e₁.hom ≫ t) hbranch₂
          _ = e₁.hom ≫ e₂.inv ≫ δ₂ := by
              simp only [Category.assoc]
      simpa only [Category.assoc] using hleft.trans hright
    have hHFE_square :
        stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁)
              (f₁ ^*[canonicalPullbackChoice S.p] x₁') δ₁ ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁')
              (f₂ ^*[canonicalPullbackChoice S.p] x₂') β' =
          stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁)
              (f₂ ^*[canonicalPullbackChoice S.p] x₂) β ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₂ ^*[canonicalPullbackChoice S.p] x₂)
              (f₂ ^*[canonicalPullbackChoice S.p] x₂') δ₂ :=
      stackificationLiftHomExtensionFiberMap_square X G hG F δ₁ β β' δ₂ hsource_square
    dsimp only [Ty, Ty', stackificationLiftObjectTransition]
    change
      ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map m₁ ≫
          (cF₁'.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁')
              (f₂ ^*[canonicalPullbackChoice S.p] x₂') β' ≫
            cF₂'.inv) =
        (cF₁.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁)
              (f₂ ^*[canonicalPullbackChoice S.p] x₂) β ≫
            cF₂.inv) ≫
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map m₂
    rw [hm₁]
    calc
      (cF₁.hom ≫
              stackificationLiftHomExtensionFiberMap X G hG F
                (f₁ ^*[canonicalPullbackChoice S.p] x₁)
                (f₁ ^*[canonicalPullbackChoice S.p] x₁') δ₁ ≫
            cF₁'.inv) ≫
          (cF₁'.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁')
              (f₂ ^*[canonicalPullbackChoice S.p] x₂') β' ≫
            cF₂'.inv) =
        (cF₁.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁)
              (f₂ ^*[canonicalPullbackChoice S.p] x₂) β ≫
            cF₂.inv) ≫
          (cF₂.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₂ ^*[canonicalPullbackChoice S.p] x₂)
              (f₂ ^*[canonicalPullbackChoice S.p] x₂') δ₂ ≫
            cF₂'.inv) := by
          simp only [Category.assoc]
          rw [cF₁'.inv_hom_id_assoc]
          rw [cF₂.inv_hom_id_assoc]
          simpa only [Category.assoc] using
            congrArg (fun t => cF₁.hom ≫ t ≫ cF₂'.inv) hHFE_square
      _ =
        (cF₁.hom ≫
            stackificationLiftHomExtensionFiberMap X G hG F
              (f₁ ^*[canonicalPullbackChoice S.p] x₁)
              (f₂ ^*[canonicalPullbackChoice S.p] x₂) β ≫
            cF₂.inv) ≫
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map m₂ := by
          exact congrArg
            (fun t =>
              (cF₁.hom ≫
                stackificationLiftHomExtensionFiberMap X G hG F
                  (f₁ ^*[canonicalPullbackChoice S.p] x₁)
                  (f₂ ^*[canonicalPullbackChoice S.p] x₂) β ≫
                cF₂.inv) ≫ t)
            hm₂.symm
  have htarget' :
      ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            (stackificationLiftObjectGluedLocalIso X G hG F y'
              (stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₁)).inv ≫
          ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁])).inv.toNatTrans.app
              (stackificationLiftObjectGlued X G hG F y') ≫
            ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (by rw [← FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂])).hom.toNatTrans.app
                (stackificationLiftObjectGlued X G hG F y') =
        stackificationLiftObjectTransition X G hG F y'
            (stackificationLiftObjectCover (J := J) G hG y')
            (stackificationLiftObjectModel (J := J) G hG y') q
            (I₁ := stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₁)
            (I₂ := stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₂)
            f₁ f₂ hf₁ hf₂ ≫
          ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            (stackificationLiftObjectGluedLocalIso X G hG F y'
              (stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₂)).inv := by
    simpa [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj, Ty',
      Iy'₁, Iy'₂, stackificationLiftVerticalCommonCover_right] using htarget
  have hsource' :
      ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            (stackificationLiftObjectGluedLocalIso X G hG F y
              (stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₁)).hom ≫
          stackificationLiftObjectTransition X G hG F y
            (stackificationLiftObjectCover (J := J) G hG y)
            (stackificationLiftObjectModel (J := J) G hG y) q
            (I₁ := stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₁)
            (I₂ := stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₂)
            f₁ f₂ hf₁ hf₂ =
        ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁])).inv.toNatTrans.app
              (stackificationLiftObjectGlued X G hG F y) ≫
            ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (by rw [← FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂])).hom.toNatTrans.app
                (stackificationLiftObjectGlued X G hG F y) ≫
              ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
                (stackificationLiftObjectGluedLocalIso X G hG F y
                  (stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₂)).hom := by
    simpa [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj, Ty,
      Iy₁, Iy₂, stackificationLiftVerticalCommonCover_left] using hsource
  let A₁ := ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
    (stackificationLiftObjectGluedLocalIso X G hG F y
      (stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₁)).hom
  let B₁ := ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map m₁
  let C₁ := ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
    (stackificationLiftObjectGluedLocalIso X G hG F y'
      (stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₁)).inv
  let D₁ :=
    ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (by rw [← FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁])).inv.toNatTrans.app
          (stackificationLiftObjectGlued X G hG F y') ≫
      ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (by rw [← FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂])).hom.toNatTrans.app
          (stackificationLiftObjectGlued X G hG F y')
  let D₀ :=
    ((canonicalFiberPseudofunctor X.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (by rw [← FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁])).inv.toNatTrans.app
          (stackificationLiftObjectGlued X G hG F y) ≫
      ((canonicalFiberPseudofunctor X.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (by rw [← FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂])).hom.toNatTrans.app
          (stackificationLiftObjectGlued X G hG F y)
  let A₂ := ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
    (stackificationLiftObjectGluedLocalIso X G hG F y
      (stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I₂)).hom
  let B₂ := ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map m₂
  let C₂ := ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
    (stackificationLiftObjectGluedLocalIso X G hG F y'
      (stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I₂)).inv
  have htarget_pre : A₁ ≫ B₁ ≫ C₁ ≫ D₁ = A₁ ≫ B₁ ≫ Ty' ≫ C₂ := by
    have h := congrArg (fun t => A₁ ≫ B₁ ≫ t) htarget'
    simpa [A₁, B₁, C₁, D₁, C₂, Category.assoc] using h
  have hmiddle_pre : A₁ ≫ B₁ ≫ Ty' ≫ C₂ = A₁ ≫ Ty ≫ B₂ ≫ C₂ := by
    have hmid' : B₁ ≫ Ty' = Ty ≫ B₂ := by
      simpa [B₁, B₂] using hmiddle
    calc
      A₁ ≫ B₁ ≫ Ty' ≫ C₂ = A₁ ≫ (B₁ ≫ Ty') ≫ C₂ := by
        simp only [Category.assoc]
      _ = A₁ ≫ (Ty ≫ B₂) ≫ C₂ := by
        exact congrArg (fun t => A₁ ≫ t ≫ C₂) hmid'
      _ = A₁ ≫ Ty ≫ B₂ ≫ C₂ := by
        simp only [Category.assoc]
  have hsource_pre : A₁ ≫ Ty ≫ B₂ ≫ C₂ = D₀ ≫ A₂ ≫ B₂ ≫ C₂ := by
    have hsource'' : A₁ ≫ Ty = D₀ ≫ A₂ := by
      simpa [A₁, D₀, A₂] using hsource'
    calc
      A₁ ≫ Ty ≫ B₂ ≫ C₂ = (A₁ ≫ Ty) ≫ B₂ ≫ C₂ := by
        simp only [Category.assoc]
      _ = (D₀ ≫ A₂) ≫ B₂ ≫ C₂ := by
        exact congrArg (fun t => t ≫ B₂ ≫ C₂) hsource''
      _ = D₀ ≫ A₂ ≫ B₂ ≫ C₂ := by
        simp only [Category.assoc]
  dsimp [stackificationLiftVerticalLocalMap, Iy₁, Iy₂, Iy'₁, Iy'₂, ly₁, ly₂, ly'₁, ly'₂,
    m₁, m₂, Ty, Ty']
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  simpa [A₁, B₁, C₁, D₁, D₀, A₂, B₂, C₂, Category.assoc] using
    htarget_pre.trans (hmiddle_pre.trans hsource_pre)


end

end CategoryTheory
