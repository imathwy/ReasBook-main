import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.BaseChangeData

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- A branch of the pulled-back cover of `y` is also a branch of the canonical cover chosen for
`f ^* y`, by using the pulled-back local source model. -/
noncomputable def stackificationLiftPulledToObjectCover
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    (stackificationLiftObjectCover (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y)).Arrow :=
  ⟨I.Y, I.f, by
    exact ⟨(stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1,
      ⟨(stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).2⟩⟩⟩

/-- Local comparison between the source model chosen by the canonical cover of `f ^* y` and the
explicit source model obtained by pulling back the source model of `y`. -/
noncomputable def stackificationLiftPulledModelComparisonIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    (FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftObjectModel (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y)
          (stackificationLiftPulledToObjectCover (J := J) G hG f y I)).1 ≅
      (FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1 := by
  let xz : S.p.Fiber I.Y :=
    (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y)
      (stackificationLiftPulledToObjectCover (J := J) G hG f y I)).1
  let xp := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
  let ez :=
    (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y)
      (stackificationLiftPulledToObjectCover (J := J) G hG f y I)).2
  let ep := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).2
  let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj xz) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xp) :=
    ez.hom ≫ ep.inv
  let β : ((FibredCategoryMor.fiberFunctor G I.Y).obj xp) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xz) :=
    ep.hom ≫ ez.inv
  let m := stackificationLiftHomExtensionFiberMap X G hG F xz xp α
  let n := stackificationLiftHomExtensionFiberMap X G hG F xp xz β
  refine
    { hom := m
      inv := n
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · have hαβ : α ≫ β = 𝟙 ((FibredCategoryMor.fiberFunctor G I.Y).obj xz) := by
      dsimp only [α, β]
      calc
        (ez.hom ≫ ep.inv) ≫ ep.hom ≫ ez.inv =
            ez.hom ≫ (ep.inv ≫ ep.hom) ≫ ez.inv := by
              simp only [Category.assoc]
        _ = ez.hom ≫ 𝟙 _ ≫ ez.inv := by
              exact congrArg (fun t => ez.hom ≫ t ≫ ez.inv) ep.inv_hom_id
        _ = ez.hom ≫ ez.inv := by
              simp only [Category.id_comp]
        _ = 𝟙 _ := ez.hom_inv_id
    dsimp only [m, n]
    rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F α β]
    rw [hαβ]
    exact stackificationLiftHomExtensionFiberMap_id X G hG F xz
  · have hβα : β ≫ α = 𝟙 ((FibredCategoryMor.fiberFunctor G I.Y).obj xp) := by
      dsimp only [α, β]
      calc
        (ep.hom ≫ ez.inv) ≫ ez.hom ≫ ep.inv =
            ep.hom ≫ (ez.inv ≫ ez.hom) ≫ ep.inv := by
              simp only [Category.assoc]
        _ = ep.hom ≫ 𝟙 _ ≫ ep.inv := by
              exact congrArg (fun t => ep.hom ≫ t ≫ ep.inv) ez.inv_hom_id
        _ = ep.hom ≫ ep.inv := by
              simp only [Category.id_comp]
        _ = 𝟙 _ := ep.hom_inv_id
    dsimp only [m, n]
    rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F β α]
    rw [hβα]
    exact stackificationLiftHomExtensionFiberMap_id X G hG F xp

/-- Local isomorphism from the glued object for `f ^* y`, restricted to a pulled-cover branch,
to the pulled local source model. -/
noncomputable def stackificationLiftPulledLocalIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    (((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)).obj
          (stackificationLiftObjectGlued X G hG F
            (f ^*[canonicalPullbackChoice S'.p] y))).obj I ≅
      (stackificationLiftPulledObjectDescentData X G hG F f y).obj I := by
  let Iz := stackificationLiftPulledToObjectCover (J := J) G hG f y I
  let lp := stackificationLiftObjectGluedLocalIso X G hG F
    (f ^*[canonicalPullbackChoice S'.p] y) Iz
  let em := stackificationLiftPulledModelComparisonIso X G hG F f y I
  let Fp := canonicalFiberPseudofunctor X.p
  let mid := (FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
  exact lp ≪≫ em ≪≫
    ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I.Y)))).app mid).symm

theorem stackificationLiftPulledLocalIso_hom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let Iz := stackificationLiftPulledToObjectCover (J := J) G hG f y I
    let mid := (FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
    (stackificationLiftPulledLocalIso X G hG F f y I).hom =
      (stackificationLiftObjectGluedLocalIso X G hG F
        (f ^*[canonicalPullbackChoice S'.p] y) Iz).hom ≫
        (stackificationLiftPulledModelComparisonIso X G hG F f y I).hom ≫
        ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I.Y)))).app mid).symm.hom := by
  intro Fp Iz mid
  rfl

theorem stackificationLiftPulledLocalIso_inv
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let Iz := stackificationLiftPulledToObjectCover (J := J) G hG f y I
    let mid := (FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
    (stackificationLiftPulledLocalIso X G hG F f y I).inv =
      ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I.Y)))).app mid).hom ≫
        (stackificationLiftPulledModelComparisonIso X G hG F f y I).inv ≫
        (stackificationLiftObjectGluedLocalIso X G hG F
          (f ^*[canonicalPullbackChoice S'.p] y) Iz).inv := by
  intro Fp Iz mid
  dsimp only [stackificationLiftPulledLocalIso]
  simp only [Fp, Iz, mid, Iso.trans_inv, Iso.symm_inv]
  exact Category.assoc _ _ _

theorem stackificationLiftPulledModelComparisonIso_hom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    let Iz := stackificationLiftPulledToObjectCover (J := J) G hG f y I
    let xz := (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y) Iz).1
    let xp := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
    let ez := (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y) Iz).2
    let ep := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).2
    (stackificationLiftPulledModelComparisonIso X G hG F f y I).hom =
      stackificationLiftHomExtensionFiberMap X G hG F xz xp (ez.hom ≫ ep.inv) := by
  intro Iz xz xp ez ep
  rfl

theorem stackificationLiftPulledModelComparisonIso_inv
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    let Iz := stackificationLiftPulledToObjectCover (J := J) G hG f y I
    let xz := (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y) Iz).1
    let xp := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).1
    let ez := (stackificationLiftObjectModel (J := J) G hG
      (f ^*[canonicalPullbackChoice S'.p] y) Iz).2
    let ep := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I).2
    (stackificationLiftPulledModelComparisonIso X G hG F f y I).inv =
      stackificationLiftHomExtensionFiberMap X G hG F xp xz (ep.hom ≫ ez.inv) := by
  intro Iz xz xp ez ep
  rfl

/-- The local model comparison commutes with the transition maps on every common refinement. -/
theorem stackificationLiftPulledModelComparisonIso_comm
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V W : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (q : W ⟶ V)
    {I₁ I₂ : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow}
    (f₁ : W ⟶ I₁.Y) (f₂ : W ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
        (stackificationLiftPulledModelComparisonIso X G hG F f y I₁).hom ≫
      stackificationLiftObjectTransition X G hG F
        (f ^*[canonicalPullbackChoice S'.p] y)
        (stackificationLiftPulledObjectCover (J := J) G hG f y)
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y)
        q f₁ f₂ hf₁ hf₂ =
    stackificationLiftObjectTransition X G hG F
        (f ^*[canonicalPullbackChoice S'.p] y)
        (stackificationLiftObjectCover (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y))
        (stackificationLiftObjectModel (J := J) G hG
          (f ^*[canonicalPullbackChoice S'.p] y))
        q
          (I₁ := stackificationLiftPulledToObjectCover (J := J) G hG f y I₁)
          (I₂ := stackificationLiftPulledToObjectCover (J := J) G hG f y I₂)
          f₁ f₂ hf₁ hf₂ ≫
    ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
        (stackificationLiftPulledModelComparisonIso X G hG F f y I₂).hom := by
  classical
  let z : S'.p.Fiber V := f ^*[canonicalPullbackChoice S'.p] y
  let Iz₁ := stackificationLiftPulledToObjectCover (J := J) G hG f y I₁
  let Iz₂ := stackificationLiftPulledToObjectCover (J := J) G hG f y I₂
  let x₁ : S.p.Fiber I₁.Y := (stackificationLiftObjectModel (J := J) G hG z Iz₁).1
  let x₂ : S.p.Fiber I₂.Y := (stackificationLiftObjectModel (J := J) G hG z Iz₂).1
  let x₁' : S.p.Fiber I₁.Y := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I₁).1
  let x₂' : S.p.Fiber I₂.Y := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I₂).1
  let cy₁ := (stackificationLiftObjectModel (J := J) G hG z Iz₁).2
  let cy₂ := (stackificationLiftObjectModel (J := J) G hG z Iz₂).2
  let cy₁' := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I₁).2
  let cy₂' := (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I₂).2
  let α₁ : ((FibredCategoryMor.fiberFunctor G I₁.Y).obj x₁) ⟶
      ((FibredCategoryMor.fiberFunctor G I₁.Y).obj x₁') :=
    cy₁.hom ≫ cy₁'.inv
  let α₂ : ((FibredCategoryMor.fiberFunctor G I₂.Y).obj x₂) ⟶
      ((FibredCategoryMor.fiberFunctor G I₂.Y).obj x₂') :=
    cy₂.hom ≫ cy₂'.inv
  let m₁ := stackificationLiftHomExtensionFiberMap X G hG F x₁ x₁' α₁
  let m₂ := stackificationLiftHomExtensionFiberMap X G hG F x₂ x₂' α₂
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
  let e₁ := stackificationLiftObjectModelPullbackIso (J := J) G z
    (stackificationLiftObjectCover (J := J) G hG z)
    (stackificationLiftObjectModel (J := J) G hG z) q Iz₁ f₁ hf₁
  let e₂ := stackificationLiftObjectModelPullbackIso (J := J) G z
    (stackificationLiftObjectCover (J := J) G hG z)
    (stackificationLiftObjectModel (J := J) G hG z) q Iz₂ f₂ hf₂
  let e₁' := stackificationLiftObjectModelPullbackIso (J := J) G z
    (stackificationLiftPulledObjectCover (J := J) G hG f y)
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y) q I₁ f₁ hf₁
  let e₂' := stackificationLiftObjectModelPullbackIso (J := J) G z
    (stackificationLiftPulledObjectCover (J := J) G hG f y)
    (stackificationLiftPulledObjectCoverModel (J := J) G hG f y) q I₂ f₂ hf₂
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
      simpa [m₂, α₂, x₂, x₂'] using hmap.symm
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
  have hbranch₁ : δ₁ ≫ e₁'.hom = e₁.hom := by
    dsimp only [δ₁, e₁, e₁', α₁]
    unfold stackificationLiftObjectModelPullbackIso
    let Mf1 := ((canonicalFiberPseudofunctor S'.p).map f₁.op.toLoc).toFunctor
    change
      (cG₁.inv ≫ Mf1.map (cy₁.hom ≫ cy₁'.inv) ≫ cG₁'.hom) ≫
          ((cG₁'.symm ≪≫ Mf1.mapIso cy₁') ≪≫
              (mapCompAppIso S'.p I₁.f f₁ q
                (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).symm).hom =
        ((cG₁.symm ≪≫ Mf1.mapIso cy₁) ≪≫
              (mapCompAppIso S'.p I₁.f f₁ q
                (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).symm).hom
    rw [Mf1.map_comp]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, mapCompAppIso]
    have hcancel :
        Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫ Mf1.map cy₁'.hom =
          𝟙 (Mf1.obj (I₁.f ^*[canonicalPullbackChoice S'.p] z)) := by
      calc
        Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫ Mf1.map cy₁'.hom =
            Mf1.map cy₁'.inv ≫ (cG₁'.hom ≫ cG₁'.inv) ≫ Mf1.map cy₁'.hom := by
              simp only [Category.assoc]
        _ = Mf1.map cy₁'.inv ≫ 𝟙 _ ≫ Mf1.map cy₁'.hom := by
              exact congrArg (fun t => Mf1.map cy₁'.inv ≫ t ≫ Mf1.map cy₁'.hom)
                cG₁'.hom_inv_id
        _ = Mf1.map cy₁'.inv ≫ Mf1.map cy₁'.hom := by
              simp only [Category.id_comp]
        _ = Mf1.map (cy₁'.inv ≫ cy₁'.hom) := by
              exact (Mf1.map_comp cy₁'.inv cy₁'.hom).symm
        _ = Mf1.map (𝟙 _) := by
              exact congrArg Mf1.map cy₁'.inv_hom_id
        _ = 𝟙 _ := by
              rw [Functor.map_id]
    calc
      (cG₁.inv ≫ (Mf1.map cy₁.hom ≫ Mf1.map cy₁'.inv) ≫ cG₁'.hom) ≫
          (cG₁'.inv ≫ Mf1.map cy₁'.hom) ≫
            (mapCompAppIso S'.p I₁.f f₁ q
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).inv =
        cG₁.inv ≫ Mf1.map cy₁.hom ≫
          (Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫ Mf1.map cy₁'.hom) ≫
            (mapCompAppIso S'.p I₁.f f₁ q
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).inv := by
            simp only [Category.assoc]
      _ = cG₁.inv ≫ Mf1.map cy₁.hom ≫
            (mapCompAppIso S'.p I₁.f f₁ q
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).inv := by
            calc
              cG₁.inv ≫ Mf1.map cy₁.hom ≫
                  (Mf1.map cy₁'.inv ≫ cG₁'.hom ≫ cG₁'.inv ≫ Mf1.map cy₁'.hom) ≫
                    (mapCompAppIso S'.p I₁.f f₁ q
                      (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).inv =
                cG₁.inv ≫ Mf1.map cy₁.hom ≫ 𝟙 _ ≫
                    (mapCompAppIso S'.p I₁.f f₁ q
                      (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).inv := by
                  exact congrArg
                    (fun t => cG₁.inv ≫ Mf1.map cy₁.hom ≫ t ≫
                      (mapCompAppIso S'.p I₁.f f₁ q
                        (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).inv)
                    hcancel
              _ = cG₁.inv ≫ Mf1.map cy₁.hom ≫
                    (mapCompAppIso S'.p I₁.f f₁ q
                      (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁) z).inv := by
                  simp only [Category.id_comp]
      _ = (cG₁.inv ≫ Mf1.map cy₁.hom) ≫
            ((canonicalFiberPseudofunctor S'.p).mapComp' I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app z := by
            simp only [Category.assoc, mapCompAppIso]
            rfl
  have hbranch₂ : e₂'.inv = e₂.inv ≫ δ₂ := by
    have hbranch₂_hom : δ₂ ≫ e₂'.hom = e₂.hom := by
      dsimp only [δ₂, e₂, e₂', α₂]
      unfold stackificationLiftObjectModelPullbackIso
      let Mf2 := ((canonicalFiberPseudofunctor S'.p).map f₂.op.toLoc).toFunctor
      change
        (cG₂.inv ≫ Mf2.map (cy₂.hom ≫ cy₂'.inv) ≫ cG₂'.hom) ≫
            ((cG₂'.symm ≪≫ Mf2.mapIso cy₂') ≪≫
                (mapCompAppIso S'.p I₂.f f₂ q
                  (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).symm).hom =
          ((cG₂.symm ≪≫ Mf2.mapIso cy₂) ≪≫
                (mapCompAppIso S'.p I₂.f f₂ q
                  (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).symm).hom
      rw [Mf2.map_comp]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, mapCompAppIso]
      have hcancel :
          Mf2.map cy₂'.inv ≫ cG₂'.hom ≫ cG₂'.inv ≫ Mf2.map cy₂'.hom =
            𝟙 (Mf2.obj (I₂.f ^*[canonicalPullbackChoice S'.p] z)) := by
        calc
          Mf2.map cy₂'.inv ≫ cG₂'.hom ≫ cG₂'.inv ≫ Mf2.map cy₂'.hom =
              Mf2.map cy₂'.inv ≫ (cG₂'.hom ≫ cG₂'.inv) ≫ Mf2.map cy₂'.hom := by
                simp only [Category.assoc]
          _ = Mf2.map cy₂'.inv ≫ 𝟙 _ ≫ Mf2.map cy₂'.hom := by
                exact congrArg (fun t => Mf2.map cy₂'.inv ≫ t ≫ Mf2.map cy₂'.hom)
                  cG₂'.hom_inv_id
          _ = Mf2.map cy₂'.inv ≫ Mf2.map cy₂'.hom := by
                simp only [Category.id_comp]
          _ = Mf2.map (cy₂'.inv ≫ cy₂'.hom) := by
                exact (Mf2.map_comp cy₂'.inv cy₂'.hom).symm
          _ = Mf2.map (𝟙 _) := by
                exact congrArg Mf2.map cy₂'.inv_hom_id
          _ = 𝟙 _ := by
                rw [Functor.map_id]
      calc
        (cG₂.inv ≫ (Mf2.map cy₂.hom ≫ Mf2.map cy₂'.inv) ≫ cG₂'.hom) ≫
            (cG₂'.inv ≫ Mf2.map cy₂'.hom) ≫
              (mapCompAppIso S'.p I₂.f f₂ q
                (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).inv =
          cG₂.inv ≫ Mf2.map cy₂.hom ≫
            (Mf2.map cy₂'.inv ≫ cG₂'.hom ≫ cG₂'.inv ≫ Mf2.map cy₂'.hom) ≫
              (mapCompAppIso S'.p I₂.f f₂ q
                (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).inv := by
              simp only [Category.assoc]
        _ = cG₂.inv ≫ Mf2.map cy₂.hom ≫
              (mapCompAppIso S'.p I₂.f f₂ q
                (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).inv := by
              calc
                cG₂.inv ≫ Mf2.map cy₂.hom ≫
                    (Mf2.map cy₂'.inv ≫ cG₂'.hom ≫ cG₂'.inv ≫ Mf2.map cy₂'.hom) ≫
                      (mapCompAppIso S'.p I₂.f f₂ q
                        (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).inv =
                  cG₂.inv ≫ Mf2.map cy₂.hom ≫ 𝟙 _ ≫
                      (mapCompAppIso S'.p I₂.f f₂ q
                        (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).inv := by
                    exact congrArg
                      (fun t => cG₂.inv ≫ Mf2.map cy₂.hom ≫ t ≫
                        (mapCompAppIso S'.p I₂.f f₂ q
                          (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).inv)
                      hcancel
                _ = cG₂.inv ≫ Mf2.map cy₂.hom ≫
                      (mapCompAppIso S'.p I₂.f f₂ q
                        (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂) z).inv := by
                    simp only [Category.id_comp]
        _ = (cG₂.inv ≫ Mf2.map cy₂.hom) ≫
              ((canonicalFiberPseudofunctor S'.p).mapComp' I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                (FibredCategoryMor.comp_toLoc_eq I₂.f f₂ q hf₂)).inv.toNatTrans.app z := by
              simp only [Category.assoc, mapCompAppIso]
              rfl
    calc
      e₂'.inv = 𝟙 _ ≫ e₂'.inv := by
        rw [Category.id_comp]
      _ = (e₂.inv ≫ e₂.hom) ≫ e₂'.inv := by
        rw [e₂.inv_hom_id]
      _ = (e₂.inv ≫ (δ₂ ≫ e₂'.hom)) ≫ e₂'.inv := by
        exact congrArg (fun t => (e₂.inv ≫ t) ≫ e₂'.inv) hbranch₂_hom.symm
      _ = e₂.inv ≫ δ₂ ≫ e₂'.hom ≫ e₂'.inv := by
        simp only [Category.assoc]
      _ = e₂.inv ≫ δ₂ := by
        rw [e₂'.hom_inv_id]
        simp only [Category.comp_id]
  have hsource_square : δ₁ ≫ β' = β ≫ δ₂ := by
    dsimp only [β, β']
    calc
      δ₁ ≫ e₁'.hom ≫ e₂'.inv =
          e₁.hom ≫ e₂'.inv := by
            rw [← Category.assoc, hbranch₁]
            rfl
      _ = (e₁.hom ≫ e₂.inv) ≫ δ₂ := by
            rw [hbranch₂]
            simp only [Category.assoc]
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
  dsimp only [stackificationLiftPulledModelComparisonIso]
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

end

end CategoryTheory
