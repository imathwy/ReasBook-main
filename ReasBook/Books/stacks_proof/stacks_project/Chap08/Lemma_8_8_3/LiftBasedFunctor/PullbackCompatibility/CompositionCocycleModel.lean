import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.LocalModelComparison
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.MapCompCocycle
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.CompositionCocycleLocal

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

theorem stackificationLiftPulledModelComparisonIso_comp_cocycle
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V W : C} (g : W ⟶ V) (f : V ⟶ U)
    (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG (g ≫ f) y).Arrow) :
    let If : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow :=
      ⟨I.Y, I.f ≫ g, by
        dsimp [stackificationLiftPulledObjectCover] at I ⊢
        simpa [Category.assoc] using I.hf⟩
    let Ig : (stackificationLiftPulledObjectCover (J := J) G hG g
        (f ^*[canonicalPullbackChoice S'.p] y)).Arrow :=
      ⟨I.Y, I.f, by
        dsimp [stackificationLiftPulledObjectCover]
        exact (stackificationLiftPulledToObjectCover (J := J) G hG f y If).hf⟩
    let Izg := stackificationLiftPulledToObjectCover (J := J) G hG g
      (f ^*[canonicalPullbackChoice S'.p] y) Ig
    let Izgf := stackificationLiftPulledToObjectCover (J := J) G hG (g ≫ f) y I
    let Hmid := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG
        (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y)) Izg).1
      (stackificationLiftObjectModel (J := J) G hG
        ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y) Izgf).1
      ((stackificationLiftObjectModel (J := J) G hG
          (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y)) Izg).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
          (mapCompAppIso S'.p f g (g ≫ f)
            (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) y).inv ≫
        (stackificationLiftObjectModel (J := J) G hG
          ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y) Izgf).2.inv)
    let PgInv' := (stackificationLiftPulledModelComparisonIso X G hG F g
      (f ^*[canonicalPullbackChoice S'.p] y) Ig).inv
    let PgfHom := (stackificationLiftPulledModelComparisonIso X G hG F (g ≫ f) y I).hom
    let PfHom := (stackificationLiftPulledModelComparisonIso X G hG F f y If).hom
    let IbaseF : (stackificationLiftObjectCover (J := J) G hG y).Arrow := If.base
    let IbaseGf : (stackificationLiftObjectCover (J := J) G hG y).Arrow := I.base
    let qbase : I.Y ⟶ U := (I.f ≫ g) ≫ f
    let hfBaseF : (𝟙 I.Y) ≫ IbaseF.f = qbase := by
      dsimp [IbaseF, qbase, If, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base]
      simp only [Category.id_comp]
    let hfBaseGf : (𝟙 I.Y) ≫ IbaseGf.f = qbase := by
      dsimp [IbaseGf, qbase, stackificationLiftPulledObjectCover,
        GrothendieckTopology.Cover.Arrow.base]
      simp only [Category.id_comp, Category.assoc]
    let Tbase := stackificationLiftObjectTransition X G hG F y
      (stackificationLiftObjectCover (J := J) G hG y)
      (stackificationLiftObjectModel (J := J) G hG y)
      qbase (I₁ := IbaseF) (I₂ := IbaseGf) (𝟙 I.Y) (𝟙 I.Y)
      hfBaseF hfBaseGf
    let midBaseF := (FibredCategoryMor.fiberFunctor F I.Y).obj
      (stackificationLiftObjectModel (J := J) G hG y IbaseF).1
    let midBaseGf := (FibredCategoryMor.fiberFunctor F I.Y).obj
      (stackificationLiftObjectModel (J := J) G hG y IbaseGf).1
    let idBaseF :=
      ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op I.Y))).inv.toNatTrans.app midBaseF
    let idBaseGf :=
      ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op I.Y))).hom.toNatTrans.app midBaseGf
    PgInv' ≫ Hmid ≫ PgfHom =
      PfHom ≫ idBaseF ≫ Tbase ≫ idBaseGf := by
  intro If Ig Izg Izgf Hmid PgInv' PgfHom PfHom IbaseF IbaseGf qbase
    hfBaseF hfBaseGf Tbase midBaseF midBaseGf idBaseF idBaseGf
  let FpX := canonicalFiberPseudofunctor X.p
  let FpS := canonicalFiberPseudofunctor S'.p
  let x₀ := (stackificationLiftObjectModel (J := J) G hG
    (f ^*[canonicalPullbackChoice S'.p] y)
    (stackificationLiftPulledToObjectCover (J := J) G hG f y If)).1
  let xF := (stackificationLiftObjectModel (J := J) G hG y IbaseF).1
  let xGf := (stackificationLiftObjectModel (J := J) G hG y IbaseGf).1
  let ez₀ := (stackificationLiftObjectModel (J := J) G hG
    (f ^*[canonicalPullbackChoice S'.p] y)
    (stackificationLiftPulledToObjectCover (J := J) G hG f y If)).2
  let ezg := (stackificationLiftObjectModel (J := J) G hG
    (g ^*[canonicalPullbackChoice S'.p] (f ^*[canonicalPullbackChoice S'.p] y))
    Izg).2
  let ezgf := (stackificationLiftObjectModel (J := J) G hG
    ((g ≫ f) ^*[canonicalPullbackChoice S'.p] y) Izgf).2
  let eF := (stackificationLiftObjectModel (J := J) G hG y IbaseF).2
  let eGf := (stackificationLiftObjectModel (J := J) G hG y IbaseGf).2
  let κfIf := mapCompAppIso S'.p f If.f (If.f ≫ f)
    (FibredCategoryMor.comp_toLoc_eq f If.f (If.f ≫ f) rfl) y
  let κg := mapCompAppIso S'.p g Ig.f (Ig.f ≫ g)
    (FibredCategoryMor.comp_toLoc_eq g Ig.f (Ig.f ≫ g) rfl)
    (f ^*[canonicalPullbackChoice S'.p] y)
  let κfg := mapCompAppIso S'.p f g (g ≫ f)
    (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) y
  let κgfI := mapCompAppIso S'.p (g ≫ f) I.f (I.f ≫ (g ≫ f))
    (FibredCategoryMor.comp_toLoc_eq (g ≫ f) I.f (I.f ≫ (g ≫ f)) rfl) y
  let αMid :
      IbaseF.f ^*[canonicalPullbackChoice S'.p] y ⟶
        IbaseGf.f ^*[canonicalPullbackChoice S'.p] y :=
    κfIf.hom ≫ κg.hom ≫
      (FpS.map I.f.op.toLoc).toFunctor.map κfg.inv ≫
      κgfI.inv
  let αBase :
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xF) ⟶
        ((FibredCategoryMor.fiberFunctor G I.Y).obj xGf) :=
    eF.hom ≫ αMid ≫ eGf.inv
  let B := stackificationLiftHomExtensionFiberMap X G hG F xF xGf αBase
  have hTbase : idBaseF ≫ Tbase ≫ idBaseGf = B := by
    let β :
        ((FibredCategoryMor.fiberFunctor G I.Y).obj
            ((𝟙 I.Y) ^*[canonicalPullbackChoice S.p] xF)) ⟶
          ((FibredCategoryMor.fiberFunctor G I.Y).obj
            ((𝟙 I.Y) ^*[canonicalPullbackChoice S.p] xGf)) :=
      (stackificationLiftObjectModelPullbackIso (J := J) G y
          (stackificationLiftObjectCover (J := J) G hG y)
          (stackificationLiftObjectModel (J := J) G hG y)
          qbase IbaseF (𝟙 I.Y) hfBaseF).hom ≫
        (stackificationLiftObjectModelPullbackIso (J := J) G y
          (stackificationLiftObjectCover (J := J) G hG y)
          (stackificationLiftObjectModel (J := J) G hG y)
          qbase IbaseGf (𝟙 I.Y) hfBaseGf).inv
    have hsource :
        (FpS.map (𝟙 I.Y).op.toLoc).toFunctor.map αBase =
          (FibredCategoryMor.pullbackComparison G (𝟙 I.Y) xF).hom ≫
            β ≫ (FibredCategoryMor.pullbackComparison G (𝟙 I.Y) xGf).inv := by
      let Msrc := (FpS.map (𝟙 I.Y).op.toLoc).toFunctor
      let c₁ := FibredCategoryMor.pullbackComparison G (𝟙 I.Y) xF
      let c₂ := FibredCategoryMor.pullbackComparison G (𝟙 I.Y) xGf
      let κbaseF := mapCompAppIso S'.p IbaseF.f (𝟙 I.Y) qbase
        (FibredCategoryMor.comp_toLoc_eq IbaseF.f (𝟙 I.Y) qbase hfBaseF) y
      let κbaseGf := mapCompAppIso S'.p IbaseGf.f (𝟙 I.Y) qbase
        (FibredCategoryMor.comp_toLoc_eq IbaseGf.f (𝟙 I.Y) qbase hfBaseGf) y
      have hmid :
          Msrc.map αMid =
            κbaseF.inv ≫ κbaseGf.hom := by
        let loc := LocallyDiscrete.mk (op I.Y)
        let κfIg := mapCompAppIso S'.p f (I.f ≫ g) (I.f ≫ (g ≫ f))
          (FibredCategoryMor.comp_toLoc_eq f (I.f ≫ g) (I.f ≫ (g ≫ f)) (by
            simp [Category.assoc])) y
        have htri := mapCompAppIso_hom_comp_map_inv (p := S'.p)
          f g I.f (g ≫ f) rfl y
        have htri' :
            κg.hom ≫ (FpS.map I.f.op.toLoc).toFunctor.map κfg.inv =
              κfIg.inv ≫ κgfI.hom := by
          simpa [κg, κfg, κgfI, κfIg, Ig, FpS, Category.assoc] using htri
        have hα :
            αMid = κfIf.hom ≫ κfIg.inv := by
          dsimp only [αMid]
          calc
            κfIf.hom ≫ κg.hom ≫
                (FpS.map I.f.op.toLoc).toFunctor.map κfg.inv ≫ κgfI.inv =
              κfIf.hom ≫
                (κg.hom ≫
                  (FpS.map I.f.op.toLoc).toFunctor.map κfg.inv) ≫
                κgfI.inv := by
                simp only [Category.assoc]
            _ =
              κfIf.hom ≫ (κfIg.inv ≫ κgfI.hom) ≫ κgfI.inv := by
                exact congrArg (fun t => κfIf.hom ≫ t ≫ κgfI.inv) htri'
            _ = κfIf.hom ≫ κfIg.inv ≫ κgfI.hom ≫ κgfI.inv := by
                simp only [Category.assoc]
            _ = κfIf.hom ≫ κfIg.inv := by
                rw [κgfI.hom_inv_id]
                simp only [Category.comp_id]
        have htail_raw :=
          Pseudofunctor.mapComp_id_assoc_tail_app FpS f g I.f y
        have htail :
            (FpS.mapId loc).inv.toNatTrans.app
                ((FpS.map qbase.op.toLoc).toFunctor.obj y) ≫
              (κbaseF.inv ≫ κbaseGf.hom) ≫
              (FpS.mapId loc).hom.toNatTrans.app
                ((FpS.map IbaseGf.f.op.toLoc).toFunctor.obj y) =
              κfIf.hom ≫ κfIg.inv := by
          dsimp only [loc] at htail_raw
          simpa [κbaseF, κbaseGf, κfIf, κfIg, qbase, IbaseF, IbaseGf, If,
            stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
            mapCompAppIso, FpS, Category.assoc] using htail_raw
        have hmapId :
            (FpS.mapId loc).inv.toNatTrans.app
                ((FpS.map qbase.op.toLoc).toFunctor.obj y) ≫
              Msrc.map (κfIf.hom ≫ κfIg.inv) ≫
              (FpS.mapId loc).hom.toNatTrans.app
                ((FpS.map IbaseGf.f.op.toLoc).toFunctor.obj y) =
              κfIf.hom ≫ κfIg.inv := by
          simpa [Msrc, loc, κfIf, κfIg, qbase, IbaseF, IbaseGf, If,
            stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
            FpS, Category.assoc] using
            Pseudofunctor.mapId_inv_map_hom_hom FpS I.Y
              (κfIf.hom ≫ κfIg.inv)
        rw [hα]
        let A :=
          (FpS.mapId loc).inv.toNatTrans.app
            ((FpS.map qbase.op.toLoc).toFunctor.obj y)
        let B :=
          (FpS.mapId loc).hom.toNatTrans.app
            ((FpS.map IbaseGf.f.op.toLoc).toFunctor.obj y)
        have hsand :
            A ≫ Msrc.map (κfIf.hom ≫ κfIg.inv) ≫ B =
              A ≫ (κbaseF.inv ≫ κbaseGf.hom) ≫ B := by
          dsimp only [A, B]
          exact hmapId.trans htail.symm
        apply (cancel_epi A).1
        apply (cancel_mono B).1
        calc
          (A ≫ Msrc.map (κfIf.hom ≫ κfIg.inv)) ≫ B =
              A ≫ Msrc.map (κfIf.hom ≫ κfIg.inv) ≫ B := by
              simp only [Category.assoc]
          _ = A ≫ (κbaseF.inv ≫ κbaseGf.hom) ≫ B := hsand
          _ = (A ≫ (κbaseF.inv ≫ κbaseGf.hom)) ≫ B := by
              simp only [Category.assoc]
      have hdecomp :
          Msrc.map αBase =
            Msrc.map eF.hom ≫ Msrc.map αMid ≫
              Msrc.map eGf.inv := by
        dsimp only [αBase]
        calc
          Msrc.map (eF.hom ≫ αMid ≫ eGf.inv) =
              Msrc.map eF.hom ≫ Msrc.map (αMid ≫ eGf.inv) := by
              exact Msrc.map_comp eF.hom (αMid ≫ eGf.inv)
          _ = Msrc.map eF.hom ≫
              (Msrc.map αMid ≫ Msrc.map eGf.inv) := by
              rw [Msrc.map_comp αMid eGf.inv]
          _ = Msrc.map eF.hom ≫ Msrc.map αMid ≫
              Msrc.map eGf.inv := by
              rfl
      rw [hdecomp, hmid]
      dsimp only [β, stackificationLiftObjectModelPullbackIso]
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
        Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
      change
        Msrc.map eF.hom ≫ (κbaseF.inv ≫ κbaseGf.hom) ≫ Msrc.map eGf.inv =
          c₁.hom ≫ (c₁.inv ≫ Msrc.map eF.hom ≫ κbaseF.inv) ≫
            (κbaseGf.hom ≫ Msrc.map eGf.inv ≫ c₂.hom) ≫ c₂.inv
      symm
      simp only [Category.assoc]
      slice_lhs 1 2 => exact c₁.hom_inv_id
      simp only [Category.id_comp]
      apply (cancel_mono c₂.hom).1
      simp only [Category.assoc]
      slice_lhs 6 7 => exact c₂.inv_hom_id
      simp only [Category.comp_id, ← Category.assoc]
      rfl
    have hmap :=
      stackificationLiftHomExtensionFiberMap_pullback X G hG F (𝟙 I.Y) αBase
    have happ :=
      stackificationLiftHomExtension_app_pullbackComparison X G hG F (𝟙 I.Y) β
    have hTmap : Tbase = (FpX.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map B := by
      dsimp only [Tbase, B, β, FpX]
      dsimp only [stackificationLiftObjectTransition]
      exact (hmap.symm.trans ((congrArg
        ((stackificationLiftHomExtension X G hG F xF xGf).app
          (op (Over.mk (𝟙 I.Y)))) hsource).trans happ)).symm
    calc
      idBaseF ≫ Tbase ≫ idBaseGf =
          idBaseF ≫ (FpX.map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map B ≫
            idBaseGf := by
        rw [hTmap]
        rfl
      _ = B := by
        dsimp only [idBaseF, idBaseGf, midBaseF, midBaseGf, B, FpX, xF, xGf]
        simpa only using
          (Pseudofunctor.mapId_inv_map_hom_hom (canonicalFiberPseudofunctor X.p) I.Y B)
  have hRhs :
      PfHom ≫ idBaseF ≫ Tbase ≫ idBaseGf = PfHom ≫ B := by
    simpa only [Category.assoc] using congrArg (fun t => PfHom ≫ t) hTbase
  rw [hRhs]
  dsimp only [PgInv', PgfHom, PfHom]
  rw [stackificationLiftPulledModelComparisonIso_inv]
  rw [stackificationLiftPulledModelComparisonIso_hom]
  rw [stackificationLiftPulledModelComparisonIso_hom]
  dsimp only [Izg, Izgf, Hmid,
    stackificationLiftPulledObjectCoverModel,
    stackificationLiftPulledToObjectCover]
  rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F]
  rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F]
  dsimp only [B, xF, xGf, αBase, IbaseF, IbaseGf]
  change _ =
    stackificationLiftHomExtensionFiberMap X G hG F x₀ xF
      (ez₀.hom ≫ (eF ≪≫ κfIf).inv) ≫
    stackificationLiftHomExtensionFiberMap X G hG F xF xGf
      (eF.hom ≫ αMid ≫ eGf.inv)
  calc
    _ = stackificationLiftHomExtensionFiberMap X G hG F x₀ xGf
        ((ez₀.hom ≫ (eF ≪≫ κfIf).inv) ≫
          (eF.hom ≫ αMid ≫ eGf.inv)) := by
      change stackificationLiftHomExtensionFiberMap X G hG F x₀ xGf _ =
        stackificationLiftHomExtensionFiberMap X G hG F x₀ xGf _
      congr 1
      change
        ((ez₀ ≪≫ κg).hom ≫ ezg.inv) ≫
              (ezg.hom ≫ (FpS.map I.f.op.toLoc).toFunctor.map κfg.inv ≫
                ezgf.inv) ≫
            ezgf.hom ≫ (eGf ≪≫ κgfI).inv =
          (ez₀.hom ≫ (eF ≪≫ κfIf).inv) ≫
            (eF.hom ≫ αMid ≫ eGf.inv)
      dsimp only [αMid]
      simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
      let M := (FpS.map I.f.op.toLoc).toFunctor.map κfg.inv
      change
        ez₀.hom ≫ κg.hom ≫ ezg.inv ≫ ezg.hom ≫ M ≫
            ezgf.inv ≫ ezgf.hom ≫ κgfI.inv ≫ eGf.inv =
          ez₀.hom ≫ (κfIf.inv ≫ eF.inv) ≫ eF.hom ≫
            (κfIf.hom ≫ κg.hom ≫ M ≫ κgfI.inv) ≫ eGf.inv
      calc
        ez₀.hom ≫ κg.hom ≫ ezg.inv ≫ ezg.hom ≫ M ≫
            ezgf.inv ≫ ezgf.hom ≫ κgfI.inv ≫ eGf.inv =
          ez₀.hom ≫ κg.hom ≫ (ezg.inv ≫ ezg.hom) ≫
            M ≫ (ezgf.inv ≫ ezgf.hom) ≫ κgfI.inv ≫ eGf.inv := by
            simp only [Category.assoc]
        _ =
          ez₀.hom ≫ κg.hom ≫ 𝟙 _ ≫
            M ≫ (ezgf.inv ≫ ezgf.hom) ≫ κgfI.inv ≫ eGf.inv := by
            exact congrArg
              (fun t => ez₀.hom ≫ κg.hom ≫ t ≫ M ≫
                (ezgf.inv ≫ ezgf.hom) ≫ κgfI.inv ≫ eGf.inv)
              ezg.inv_hom_id
        _ =
          ez₀.hom ≫ κg.hom ≫ 𝟙 _ ≫ M ≫ 𝟙 _ ≫
            κgfI.inv ≫ eGf.inv := by
            exact congrArg
              (fun t => ez₀.hom ≫ κg.hom ≫ 𝟙 _ ≫
                M ≫ t ≫ κgfI.inv ≫ eGf.inv)
              ezgf.inv_hom_id
        _ =
          ez₀.hom ≫ κg.hom ≫ M ≫ κgfI.inv ≫ eGf.inv := by
            simp only [Category.id_comp]
        _ =
          ez₀.hom ≫ (κfIf.inv ≫ eF.inv) ≫ eF.hom ≫
            (κfIf.hom ≫ κg.hom ≫ M ≫ κgfI.inv) ≫ eGf.inv := by
            symm
            calc
              ez₀.hom ≫ (κfIf.inv ≫ eF.inv) ≫ eF.hom ≫
                  (κfIf.hom ≫ κg.hom ≫ M ≫ κgfI.inv) ≫ eGf.inv =
                ez₀.hom ≫ κfIf.inv ≫ (eF.inv ≫ eF.hom) ≫
                  κfIf.hom ≫ κg.hom ≫ M ≫ κgfI.inv ≫ eGf.inv := by
                  simp only [Category.assoc]
              _ =
                ez₀.hom ≫ κfIf.inv ≫ 𝟙 _ ≫
                  κfIf.hom ≫ κg.hom ≫ M ≫ κgfI.inv ≫ eGf.inv := by
                  exact congrArg
                    (fun t => ez₀.hom ≫ κfIf.inv ≫ t ≫
                      κfIf.hom ≫ κg.hom ≫ M ≫ κgfI.inv ≫ eGf.inv)
                    eF.inv_hom_id
              _ =
                ez₀.hom ≫ (κfIf.inv ≫ κfIf.hom) ≫
                  κg.hom ≫ M ≫ κgfI.inv ≫ eGf.inv := by
                  simp only [Category.id_comp, Category.assoc]
              _ =
                ez₀.hom ≫ 𝟙 _ ≫ κg.hom ≫ M ≫ κgfI.inv ≫ eGf.inv := by
                  exact congrArg
                    (fun t => ez₀.hom ≫ t ≫ κg.hom ≫ M ≫
                      κgfI.inv ≫ eGf.inv)
                    κfIf.inv_hom_id
              _ =
                ez₀.hom ≫ κg.hom ≫ M ≫ κgfI.inv ≫ eGf.inv := by
                  simp only [Category.id_comp]
    _ = stackificationLiftHomExtensionFiberMap X G hG F x₀ xF
          (ez₀.hom ≫ (eF ≪≫ κfIf).inv) ≫
        stackificationLiftHomExtensionFiberMap X G hG F xF xGf
          (eF.hom ≫ αMid ≫ eGf.inv) := by
      exact stackificationLiftHomExtensionFiberMap_comp X G hG F
        (ez₀.hom ≫ (eF ≪≫ κfIf).inv)
        (eF.hom ≫ αMid ≫ eGf.inv)

end

end CategoryTheory
