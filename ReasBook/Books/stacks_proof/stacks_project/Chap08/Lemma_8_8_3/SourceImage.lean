import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.Prelude

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 3: one source-image local identification, pulled back to a
common overlap and followed by the target pullback comparison, normalizes to the Hom-extension
from the literal pulled-back source object. -/
theorem stackificationLiftObjectSourceImageLocalIso_coverLeg_normalized
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (x : S.p.Fiber U)
    (q : V ⟶ U)
    (I : (stackificationLiftObjectCover (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G U).obj x)).Arrow)
    (f : V ⟶ I.Y) (hf : f ≫ I.f = q) :
    ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageLocalIso X G hG F x I).hom ≫
      (FibredCategoryMor.pullbackComparison F f
        (stackificationLiftObjectModel (J := J) G hG
          ((FibredCategoryMor.fiberFunctor G U).obj x) I).1).hom =
    (mapCompAppIso X.p I.f f q
        (FibredCategoryMor.comp_toLoc_eq I.f f q hf)
        ((FibredCategoryMor.fiberFunctor F U).obj x)).inv ≫
      (FibredCategoryMor.pullbackComparison F q x).hom ≫
        stackificationLiftHomExtensionFiberMap X G hG F
          (q ^*[canonicalPullbackChoice S.p] x)
          (f ^*[canonicalPullbackChoice S.p]
            (stackificationLiftObjectModel (J := J) G hG
              ((FibredCategoryMor.fiberFunctor G U).obj x) I).1)
          ((FibredCategoryMor.pullbackComparison G q x).inv ≫
            (stackificationLiftObjectModelPullbackIso (J := J) G
              ((FibredCategoryMor.fiberFunctor G U).obj x)
              (stackificationLiftObjectCover (J := J) G hG
                ((FibredCategoryMor.fiberFunctor G U).obj x))
              (stackificationLiftObjectModel (J := J) G hG
                ((FibredCategoryMor.fiberFunctor G U).obj x))
              q I f hf).inv) := by
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let model := stackificationLiftObjectModel (J := J) G hG y
  let px : S.p.Fiber I.Y := I.f ^*[canonicalPullbackChoice S.p] x
  let fx : S.p.Fiber V := f ^*[canonicalPullbackChoice S.p] px
  let qx : S.p.Fiber V := q ^*[canonicalPullbackChoice S.p] x
  let fmodel : S.p.Fiber V := f ^*[canonicalPullbackChoice S.p] (model I).1
  let MX := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  let MG := ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor
  let κX :=
    mapCompAppIso X.p I.f f q
      (FibredCategoryMor.comp_toLoc_eq I.f f q hf)
      ((FibredCategoryMor.fiberFunctor F U).obj x)
  let κS :=
    mapCompAppIso S.p I.f f q
      (FibredCategoryMor.comp_toLoc_eq I.f f q hf) x
  let κG :=
    mapCompAppIso S'.p I.f f q
      (FibredCategoryMor.comp_toLoc_eq I.f f q hf)
      ((FibredCategoryMor.fiberFunctor G U).obj x)
  let cFI := FibredCategoryMor.pullbackComparison F I.f x
  let cFfpx := FibredCategoryMor.pullbackComparison F f px
  let cFfm := FibredCategoryMor.pullbackComparison F f (model I).1
  let cFq := FibredCategoryMor.pullbackComparison F q x
  let cGI := FibredCategoryMor.pullbackComparison G I.f x
  let cGfpx := FibredCategoryMor.pullbackComparison G f px
  let cGfm := FibredCategoryMor.pullbackComparison G f (model I).1
  let cGq := FibredCategoryMor.pullbackComparison G q x
  let eI := (model I).2
  let e :=
    stackificationLiftObjectModelPullbackIso (J := J) G y
      (stackificationLiftObjectCover (J := J) G hG y) model q I f hf
  let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj px) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj (model I).1) :=
    cGI.inv ≫ eI.inv
  let αpull : ((FibredCategoryMor.fiberFunctor G V).obj fx) ⟶
      ((FibredCategoryMor.fiberFunctor G V).obj fmodel) :=
    cGfpx.inv ≫ MG.map α ≫ cGfm.hom
  let m :=
    stackificationLiftHomExtensionFiberMap X G hG F px (model I).1 α
  let mpull :=
    stackificationLiftHomExtensionFiberMap X G hG F fx fmodel αpull
  let m' :=
    stackificationLiftHomExtensionFiberMap X G hG F qx fmodel
      (cGq.inv ≫ e.inv)
  have hm_pull :
      MX.map m = cFfpx.hom ≫ mpull ≫ cFfm.inv := by
    have hsrc :
        cGfpx.hom ≫ αpull ≫ cGfm.inv = MG.map α := by
      dsimp only [αpull]
      calc
        cGfpx.hom ≫ (cGfpx.inv ≫ MG.map α ≫ cGfm.hom) ≫ cGfm.inv =
            (cGfpx.hom ≫ cGfpx.inv) ≫ MG.map α ≫
              (cGfm.hom ≫ cGfm.inv) := by
              simp only [Category.assoc]
        _ = MG.map α := by
              rw [cGfpx.hom_inv_id, cGfm.hom_inv_id]
              simpa only [Category.id_comp] using Category.comp_id (MG.map α)
    have hmap :=
      stackificationLiftHomExtensionFiberMap_pullback X G hG F f
        (x := px) (y := (model I).1) α
    have happ :=
      stackificationLiftHomExtension_app_pullbackComparison X G hG F f
        (x := px) (y := (model I).1) αpull
    calc
      MX.map m =
          (stackificationLiftHomExtension X G hG F px (model I).1).app
            (op (Over.mk f)) (MG.map α) := hmap.symm
      _ =
          (stackificationLiftHomExtension X G hG F px (model I).1).app
            (op (Over.mk f)) (cGfpx.hom ≫ αpull ≫ cGfm.inv) := by
            rw [hsrc]
      _ = cFfpx.hom ≫ mpull ≫ cFfm.inv := happ
  have hleft :
      κX.hom ≫ MX.map cFI.hom ≫ cFfpx.hom =
        cFq.hom ≫ (FibredCategoryMor.fiberFunctor F V).map κS.hom := by
    simpa only [κX, MX, cFI, cFfpx, cFq, κS, mapCompAppIso] using
      pullbackComparison_mapComp_hom_cocycle F I.f f q hf x
  have hbase_inv :
      cGfpx.inv ≫ MG.map cGI.inv ≫ κG.inv =
        (FibredCategoryMor.fiberFunctor G V).map κS.inv ≫ cGq.inv := by
    simpa only [κG, MG, cGI, cGfpx, cGq, κS, mapCompAppIso] using
      pullbackComparison_mapComp_inv_cocycle G I.f f q hf x
  have hbase :
      (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫ cGfpx.inv ≫ MG.map cGI.inv =
        cGq.inv ≫ κG.hom := by
    have hcancelS :
        (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫
            (FibredCategoryMor.fiberFunctor G V).map κS.inv =
          𝟙 _ := by
      calc
        (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫
            (FibredCategoryMor.fiberFunctor G V).map κS.inv =
          (FibredCategoryMor.fiberFunctor G V).map (κS.hom ≫ κS.inv) := by
            exact ((FibredCategoryMor.fiberFunctor G V).map_comp κS.hom κS.inv).symm
        _ = (FibredCategoryMor.fiberFunctor G V).map (𝟙 _) := by
            exact congrArg (FibredCategoryMor.fiberFunctor G V).map κS.hom_inv_id
        _ = 𝟙 _ := by rw [Functor.map_id]
    have hstep := congrArg
      (fun t => (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫ t ≫ κG.hom)
      hbase_inv
    apply (Iso.eq_comp_inv κG.symm).2
    calc
      ((FibredCategoryMor.fiberFunctor G V).map κS.hom ≫ cGfpx.inv ≫
            MG.map cGI.inv) ≫ κG.inv =
          (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫
            (cGfpx.inv ≫ MG.map cGI.inv ≫ κG.inv) := by
            simp only [Category.assoc]
      _ =
          (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫
            ((FibredCategoryMor.fiberFunctor G V).map κS.inv ≫ cGq.inv) := by
            rw [hbase_inv]
      _ =
          ((FibredCategoryMor.fiberFunctor G V).map κS.hom ≫
            (FibredCategoryMor.fiberFunctor G V).map κS.inv) ≫ cGq.inv := by
            simp only [Category.assoc]
      _ = cGq.inv := by
            rw [hcancelS]
            simp only [Category.id_comp]
  have hsrc :
      (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫ αpull =
        cGq.inv ≫ e.inv := by
    dsimp only [αpull, α, e, stackificationLiftObjectModelPullbackIso]
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, mapCompAppIso,
      MG, cGfm, eI, cGI, cGfpx]
    rw [Functor.map_comp]
    calc
      (FibredCategoryMor.fiberFunctor G V).map κS.hom ≫
          cGfpx.inv ≫ (MG.map cGI.inv ≫ MG.map eI.inv) ≫ cGfm.hom =
        ((FibredCategoryMor.fiberFunctor G V).map κS.hom ≫
            cGfpx.inv ≫ MG.map cGI.inv) ≫ MG.map eI.inv ≫ cGfm.hom := by
          simp only [Category.assoc]
      _ = (cGq.inv ≫ κG.hom) ≫ MG.map eI.inv ≫ cGfm.hom := by
          rw [hbase]
      _ = cGq.inv ≫ κG.hom ≫ MG.map eI.inv ≫ cGfm.hom := by
          simp only [Category.assoc]
  have hmid :
      (FibredCategoryMor.fiberFunctor F V).map κS.hom ≫ mpull = m' := by
    have htransport :=
      stackificationLiftHomExtensionFiberMap_transport_of_sourceIso X G hG F
        κS (Iso.refl fmodel) αpull
    have htransport' :
        stackificationLiftHomExtensionFiberMap X G hG F qx fmodel
            ((FibredCategoryMor.fiberFunctor G V).map κS.hom ≫ αpull) =
          (FibredCategoryMor.fiberFunctor F V).map κS.hom ≫ mpull := by
      simpa only [Iso.refl_inv, Functor.map_id, Category.comp_id] using htransport
    dsimp only [mpull, m']
    calc
      (FibredCategoryMor.fiberFunctor F V).map κS.hom ≫
          stackificationLiftHomExtensionFiberMap X G hG F fx fmodel αpull =
        stackificationLiftHomExtensionFiberMap X G hG F qx fmodel
          ((FibredCategoryMor.fiberFunctor G V).map κS.hom ≫ αpull) := by
          exact htransport'.symm
      _ =
        stackificationLiftHomExtensionFiberMap X G hG F qx fmodel
          (cGq.inv ≫ e.inv) := by
          exact congrArg (stackificationLiftHomExtensionFiberMap X G hG F qx fmodel) hsrc
  dsimp only [stackificationLiftObjectSourceImageLocalIso]
  change MX.map (cFI.hom ≫ m) ≫ cFfm.hom =
    κX.inv ≫ cFq.hom ≫ m'
  rw [Functor.map_comp]
  calc
    (MX.map cFI.hom ≫ MX.map m) ≫ cFfm.hom =
        MX.map cFI.hom ≫ (cFfpx.hom ≫ mpull ≫ cFfm.inv) ≫ cFfm.hom := by
          rw [hm_pull]
          simp only [Category.assoc]
    _ = MX.map cFI.hom ≫ cFfpx.hom ≫ mpull := by
          calc
            MX.map cFI.hom ≫ (cFfpx.hom ≫ mpull ≫ cFfm.inv) ≫ cFfm.hom =
                (MX.map cFI.hom ≫ cFfpx.hom ≫ mpull ≫ cFfm.inv) ≫
                  cFfm.hom := by
                  simp only [Category.assoc]
            _ = MX.map cFI.hom ≫ cFfpx.hom ≫ mpull := by
                  have hassoc :
                      MX.map cFI.hom ≫ cFfpx.hom ≫ mpull ≫ cFfm.inv =
                        (MX.map cFI.hom ≫ cFfpx.hom ≫ mpull) ≫ cFfm.inv := by
                    simp only [Category.assoc]
                  exact (Iso.eq_comp_inv cFfm).1 hassoc
    _ = κX.inv ≫ (κX.hom ≫ MX.map cFI.hom ≫ cFfpx.hom) ≫ mpull := by
          symm
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = κX.inv ≫ (cFq.hom ≫ (FibredCategoryMor.fiberFunctor F V).map κS.hom) ≫
          mpull := by
          rw [hleft]
    _ = κX.inv ≫ cFq.hom ≫
          ((FibredCategoryMor.fiberFunctor F V).map κS.hom ≫ mpull) := by
          simp only [Category.assoc]
    _ = κX.inv ≫ cFq.hom ≫ m' := by
          rw [hmid]

/-- Helper for Chap08 Lemma 8 8 3: the source-image local identifications are compatible with
the chosen object-descent transition. -/
theorem stackificationLiftObjectSourceImageLocalIso_comm
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (x : S.p.Fiber U)
    (q : V ⟶ U)
    {I₁ I₂ : (stackificationLiftObjectCover (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G U).obj x)).Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageLocalIso X G hG F x I₁).hom ≫
      stackificationLiftObjectTransition X G hG F
        ((FibredCategoryMor.fiberFunctor G U).obj x)
        (stackificationLiftObjectCover (J := J) G hG
          ((FibredCategoryMor.fiberFunctor G U).obj x))
        (stackificationLiftObjectModel (J := J) G hG
          ((FibredCategoryMor.fiberFunctor G U).obj x))
        q f₁ f₂ hf₁ hf₂ =
    ((((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftObjectCover (J := J) G hG
        ((FibredCategoryMor.fiberFunctor G U).obj x)).Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor F U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
      ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageLocalIso X G hG F x I₂).hom := by
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let Scover := stackificationLiftObjectCover (J := J) G hG y
  let model := stackificationLiftObjectModel (J := J) G hG y
  let MX₁ := ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor
  let MX₂ := ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor
  let κX₁ :=
    mapCompAppIso X.p I₁.f f₁ q
      (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)
      ((FibredCategoryMor.fiberFunctor F U).obj x)
  let κX₂ :=
    mapCompAppIso X.p I₂.f f₂ q
      (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)
      ((FibredCategoryMor.fiberFunctor F U).obj x)
  let cFq := FibredCategoryMor.pullbackComparison F q x
  let cFm₁ := FibredCategoryMor.pullbackComparison F f₁ (model I₁).1
  let cFm₂ := FibredCategoryMor.pullbackComparison F f₂ (model I₂).1
  let cGq := FibredCategoryMor.pullbackComparison G q x
  let e₁ :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q I₁ f₁ hf₁
  let e₂ :=
    stackificationLiftObjectModelPullbackIso (J := J) G y Scover model
      q I₂ f₂ hf₂
  let ℓ₁ := stackificationLiftObjectSourceImageLocalIso X G hG F x I₁
  let ℓ₂ := stackificationLiftObjectSourceImageLocalIso X G hG F x I₂
  let m₁ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (q ^*[canonicalPullbackChoice S.p] x)
      (f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1)
      (cGq.inv ≫ e₁.inv)
  let m₂ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (q ^*[canonicalPullbackChoice S.p] x)
      (f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1)
      (cGq.inv ≫ e₂.inv)
  let m₁₂ :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (f₁ ^*[canonicalPullbackChoice S.p] (model I₁).1)
      (f₂ ^*[canonicalPullbackChoice S.p] (model I₂).1)
      (e₁.hom ≫ e₂.inv)
  have hleg₁ :
      MX₁.map ℓ₁.hom ≫ cFm₁.hom =
        κX₁.inv ≫ cFq.hom ≫ m₁ := by
    simpa only [y, Scover, model, MX₁, κX₁, cFq, cFm₁, cGq, e₁, ℓ₁, m₁] using
      stackificationLiftObjectSourceImageLocalIso_coverLeg_normalized
        (J := J) X G hG F x q I₁ f₁ hf₁
  have hleg₂ :
      MX₂.map ℓ₂.hom ≫ cFm₂.hom =
        κX₂.inv ≫ cFq.hom ≫ m₂ := by
    simpa only [y, Scover, model, MX₂, κX₂, cFq, cFm₂, cGq, e₂, ℓ₂, m₂] using
      stackificationLiftObjectSourceImageLocalIso_coverLeg_normalized
        (J := J) X G hG F x q I₂ f₂ hf₂
  have hmid : m₁ ≫ m₁₂ = m₂ := by
    dsimp only [m₁, m₁₂, m₂]
    rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F
      (cGq.inv ≫ e₁.inv) (e₁.hom ≫ e₂.inv)]
    congr 1
    calc
      (cGq.inv ≫ e₁.inv) ≫ e₁.hom ≫ e₂.inv =
          cGq.inv ≫ (e₁.inv ≫ e₁.hom) ≫ e₂.inv := by
            simp only [Category.assoc]
      _ = cGq.inv ≫ e₂.inv := by
            rw [e₁.inv_hom_id]
            simp only [Category.id_comp]
  have hleg₂_solve :
      κX₂.hom ≫ MX₂.map ℓ₂.hom =
        cFq.hom ≫ m₂ ≫ cFm₂.inv := by
    calc
      κX₂.hom ≫ MX₂.map ℓ₂.hom =
          (cFq.hom ≫ m₂) ≫ cFm₂.inv := by
            apply (Iso.eq_comp_inv cFm₂).2
            calc
              (κX₂.hom ≫ MX₂.map ℓ₂.hom) ≫ cFm₂.hom =
                  κX₂.hom ≫ (MX₂.map ℓ₂.hom ≫ cFm₂.hom) := by
                    simp only [Category.assoc]
              _ = κX₂.hom ≫ (κX₂.inv ≫ cFq.hom ≫ m₂) := by
                    simpa only [Category.assoc] using
                      congrArg (fun t => κX₂.hom ≫ t) hleg₂
              _ = (κX₂.hom ≫ κX₂.inv) ≫ cFq.hom ≫ m₂ := by
                    simp only [Category.assoc]
              _ = cFq.hom ≫ m₂ := by
                    rw [κX₂.hom_inv_id]
                    simp only [Category.id_comp]
      _ = cFq.hom ≫ m₂ ≫ cFm₂.inv := by
            simp only [Category.assoc]
  dsimp only [stackificationLiftObjectTransition, Pseudofunctor.toDescentData,
    Pseudofunctor.DescentData.ofObj]
  change MX₁.map ℓ₁.hom ≫ (cFm₁.hom ≫ m₁₂ ≫ cFm₂.inv) =
    (κX₁.inv ≫ κX₂.hom) ≫ MX₂.map ℓ₂.hom
  have hright :
      κX₁.inv ≫ (cFq.hom ≫ m₂ ≫ cFm₂.inv) =
        κX₁.inv ≫ (κX₂.hom ≫ MX₂.map ℓ₂.hom) :=
    congrArg (fun t => κX₁.inv ≫ t) hleg₂_solve.symm
  have hright' :
      κX₁.inv ≫ cFq.hom ≫ m₂ ≫ cFm₂.inv =
        (κX₁.inv ≫ κX₂.hom) ≫ MX₂.map ℓ₂.hom := by
    simpa only [Category.assoc] using hright
  have hmain :
      MX₁.map ℓ₁.hom ≫ (cFm₁.hom ≫ m₁₂ ≫ cFm₂.inv) =
        κX₁.inv ≫ cFq.hom ≫ m₂ ≫ cFm₂.inv := by
    calc
      MX₁.map ℓ₁.hom ≫ (cFm₁.hom ≫ m₁₂ ≫ cFm₂.inv) =
          (MX₁.map ℓ₁.hom ≫ cFm₁.hom) ≫ m₁₂ ≫ cFm₂.inv := by
            simp only [Category.assoc]
      _ = (κX₁.inv ≫ cFq.hom ≫ m₁) ≫ m₁₂ ≫ cFm₂.inv := by
            rw [hleg₁]
            rfl
      _ = κX₁.inv ≫ cFq.hom ≫ (m₁ ≫ m₁₂) ≫ cFm₂.inv := by
            simp only [Category.assoc]
      _ = κX₁.inv ≫ cFq.hom ≫ m₂ ≫ cFm₂.inv := by
            rw [hmid]
  exact hmain.trans hright'

/-- Helper for Chap08 Lemma 8 8 3: for a literal source-image object `G x`, the descent data
attached to `F x` is isomorphic to the object-descent data used to define the glued object. -/
noncomputable def stackificationLiftObjectSourceImageDescentIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U) :
    ((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftObjectCover (J := J) G hG
        ((FibredCategoryMor.fiberFunctor G U).obj x)).Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor F U).obj x) ≅
      stackificationLiftObjectDescentData X G hG F
        ((FibredCategoryMor.fiberFunctor G U).obj x) :=
  -- The local source-image isomorphisms are exactly compatible with the transition morphisms of
  -- the glued-object descent datum, so they assemble into an isomorphism of descent data.
  Pseudofunctor.DescentData.isoMk
    (fun I ↦ stackificationLiftObjectSourceImageLocalIso X G hG F x I)
    (fun {_V} q {_I₁ _I₂} f₁ f₂ hf₁ hf₂ ↦
      stackificationLiftObjectSourceImageLocalIso_comm X G hG F x q f₁ f₂ hf₁ hf₂)

/-- Helper for Chap08 Lemma 8 8 3: the descended object attached to the source-image target
object `G x` is isomorphic to `F x` in the target fiber. -/
theorem stackificationLiftObjectSourceImageGluedIso_nonempty
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U) :
    Nonempty
      (stackificationLiftObjectGlued X G hG F
          ((FibredCategoryMor.fiberFunctor G U).obj x) ≅
        (FibredCategoryMor.fiberFunctor F U).obj x) := by
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let Scover := stackificationLiftObjectCover (J := J) G hG y
  let Φ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Scover.Arrow ↦ I.f)
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance U Scover
  let ddIso : Φ.obj (stackificationLiftObjectGlued X G hG F y) ≅
      Φ.obj ((FibredCategoryMor.fiberFunctor F U).obj x) :=
    stackificationLiftObjectGluedIso X G hG F y ≪≫
      (stackificationLiftObjectSourceImageDescentIso X G hG F x).symm
  -- Full faithfulness of fixed-cover descent reflects the descent-data isomorphism to the fiber.
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful Φ).preimageIso ddIso⟩

/-- Helper for Chap08 Lemma 8 8 3: chosen comparison between the glued descended object over
`G x` and the original object `F x`. -/
noncomputable def stackificationLiftObjectSourceImageGluedIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U) :
    stackificationLiftObjectGlued X G hG F
        ((FibredCategoryMor.fiberFunctor G U).obj x) ≅
      (FibredCategoryMor.fiberFunctor F U).obj x :=
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let Scover := stackificationLiftObjectCover (J := J) G hG y
  let Φ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Scover.Arrow ↦ I.f)
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance U Scover
  let ddIso : Φ.obj (stackificationLiftObjectGlued X G hG F y) ≅
      Φ.obj ((FibredCategoryMor.fiberFunctor F U).obj x) :=
    stackificationLiftObjectGluedIso X G hG F y ≪≫
      (stackificationLiftObjectSourceImageDescentIso X G hG F x).symm
  (Functor.FullyFaithful.ofFullyFaithful Φ).preimageIso ddIso

/-- The canonical source-image comparison has the prescribed component on every branch of the
source-image cover. -/
theorem stackificationLiftObjectSourceImageGluedIso_local_hom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U)
    (I : (stackificationLiftObjectCover (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G U).obj x)).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom =
      (stackificationLiftObjectGluedLocalIso X G hG F
        ((FibredCategoryMor.fiberFunctor G U).obj x) I).hom ≫
      (stackificationLiftObjectSourceImageLocalIso X G hG F x I).inv := by
  dsimp only [stackificationLiftObjectSourceImageGluedIso]
  rw [Functor.FullyFaithful.preimageIso_hom]
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let Scover := stackificationLiftObjectCover (J := J) G hG y
  let Φ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Scover.Arrow ↦ I.f)
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance U Scover
  change (Φ.map ((Functor.FullyFaithful.ofFullyFaithful Φ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- The inverse of the canonical source-image comparison has the prescribed component on every
branch of the source-image cover. -/
theorem stackificationLiftObjectSourceImageGluedIso_local_inv
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (x : S.p.Fiber U)
    (I : (stackificationLiftObjectCover (J := J) G hG
      ((FibredCategoryMor.fiberFunctor G U).obj x)).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
        (stackificationLiftObjectSourceImageGluedIso X G hG F x).inv =
      (stackificationLiftObjectSourceImageLocalIso X G hG F x I).hom ≫
      (stackificationLiftObjectGluedLocalIso X G hG F
        ((FibredCategoryMor.fiberFunctor G U).obj x) I).inv := by
  dsimp only [stackificationLiftObjectSourceImageGluedIso]
  rw [Functor.FullyFaithful.preimageIso_inv]
  let y : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let Scover := stackificationLiftObjectCover (J := J) G hG y
  let Φ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Scover.Arrow ↦ I.f)
  haveI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance U Scover
  change (Φ.map ((Functor.FullyFaithful.ofFullyFaithful Φ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

end

end CategoryTheory
