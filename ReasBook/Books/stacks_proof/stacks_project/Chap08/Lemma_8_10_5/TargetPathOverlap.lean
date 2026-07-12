import StacksProject_2024.Chap08.Lemma_8_10_5.TargetPathTransport


universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom
open Opposite

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: when a literal-base overlap is the projection of an actual overlap in
`Yₛ`, the simple source-forget overlap map is the direct source-forgotten actual overlap. -/
theorem inherited_basis_simple_forget_to_source_descent_hom_actual
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ g i₂ = q := by cat_disch) :
    inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
        (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂)
        (by rw [← Functor.map_comp, hf₁])
        (by rw [← Functor.map_comp, hf₂]) =
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ := by
  let E := inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y
  let qOver : Over y := Over.mk q
  let qUp := inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) (Yₛ.p.map q)
  let u := (E.unitIso.app qOver).hom
  let l₁ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
    (Yₛ.p.map q) (Yₛ.p.map f₁)
    (by rw [← Functor.map_comp, hf₁])
  let l₂ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
    (Yₛ.p.map q) (Yₛ.p.map f₂)
    (by rw [← Functor.map_comp, hf₂])
  have huq : u.left ≫ qUp.hom = q := by
    simpa [u, qUp, qOver, inherited_basis_target_slice_inverse_obj] using Over.w u
  have hbase :
      ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
          (Over.mk (Yₛ.p.map q))).inv.left =
        Yₛ.p.map u.left := by
    have hfunctor :
        E.functor.map (E.unitIso.hom.app qOver) =
          E.counitIso.inv.app (E.functor.obj qOver) := by
      apply (cancel_mono (E.counitIso.hom.app (E.functor.obj qOver))).1
      simp
    exact (congrArg (fun m ↦ m.left) hfunctor).symm
  have hu₁ : u.left ≫ l₁ = f₁ := by
    let target₁ : Over y := Over.mk (g i₁)
    let m₁ : qOver ⟶ target₁ := Over.homMk f₁ hf₁
    let ui₁ := (E.unitIso.app target₁).hom
    have hcancel_q : u.left ≫ (E.unitIso.app qOver).inv.left = 𝟙 Z := by
      change ((E.unitIso.app qOver).hom ≫ (E.unitIso.app qOver).inv).left = 𝟙 Z
      rw [(E.unitIso.app qOver).hom_inv_id]
      rfl
    have hnat_left' :
        u.left ≫ (E.inverse.map (E.functor.map m₁)).left = f₁ ≫ ui₁.left := by
      have hcancel_q' :
          (E.unitIso.hom.app qOver).left ≫ (E.unitInv.app qOver).left = 𝟙 Z := by
        simpa [u] using hcancel_q
      simp [u, ui₁, m₁]
      calc
        (E.unitIso.hom.app qOver).left ≫ (E.unitInv.app qOver).left ≫ f₁ ≫
            (E.unit.app target₁).left =
          ((E.unitIso.hom.app qOver).left ≫ (E.unitInv.app qOver).left) ≫ f₁ ≫
            (E.unit.app target₁).left := by
            simp only [Category.assoc]
        _ = (𝟙 Z) ≫ f₁ ≫ (E.unit.app target₁).left := by
            rw [hcancel_q']
            rfl
        _ = f₁ ≫ (E.unitIso.hom.app target₁).left := by
            simp
    have hcancel : ui₁.left ≫ (E.unitIso.app target₁).inv.left = 𝟙 (Y i₁) := by
      change ((E.unitIso.app target₁).hom ≫ (E.unitIso.app target₁).inv).left = 𝟙 (Y i₁)
      rw [(E.unitIso.app target₁).hom_inv_id]
      rfl
    change u.left ≫
        ((E.inverse.map (E.functor.map m₁)).left ≫
          (E.unitIso.app target₁).inv.left) = f₁
    rw [← Category.assoc, hnat_left']
    exact
      (Category.assoc f₁ ui₁.left (E.unitIso.inv.app target₁).left).trans (by
        have hcancel' : ui₁.left ≫ (E.unitIso.inv.app target₁).left = 𝟙 (Y i₁) := by
          simpa [ui₁] using hcancel
        change f₁ ≫ (ui₁.left ≫ (E.unitIso.inv.app target₁).left) = f₁
        exact (congrArg (fun t ↦ f₁ ≫ t) hcancel').trans (Category.comp_id f₁))
  have hu₂ : u.left ≫ l₂ = f₂ := by
    let target₂ : Over y := Over.mk (g i₂)
    let m₂ : qOver ⟶ target₂ := Over.homMk f₂ hf₂
    let ui₂ := (E.unitIso.app target₂).hom
    have hcancel_q : u.left ≫ (E.unitIso.app qOver).inv.left = 𝟙 Z := by
      change ((E.unitIso.app qOver).hom ≫ (E.unitIso.app qOver).inv).left = 𝟙 Z
      rw [(E.unitIso.app qOver).hom_inv_id]
      rfl
    have hnat_left' :
        u.left ≫ (E.inverse.map (E.functor.map m₂)).left = f₂ ≫ ui₂.left := by
      have hcancel_q' :
          (E.unitIso.hom.app qOver).left ≫ (E.unitInv.app qOver).left = 𝟙 Z := by
        simpa [u] using hcancel_q
      simp [u, ui₂, m₂]
      calc
        (E.unitIso.hom.app qOver).left ≫ (E.unitInv.app qOver).left ≫ f₂ ≫
            (E.unit.app target₂).left =
          ((E.unitIso.hom.app qOver).left ≫ (E.unitInv.app qOver).left) ≫ f₂ ≫
            (E.unit.app target₂).left := by
            simp only [Category.assoc]
        _ = (𝟙 Z) ≫ f₂ ≫ (E.unit.app target₂).left := by
            rw [hcancel_q']
            rfl
        _ = f₂ ≫ (E.unitIso.hom.app target₂).left := by
            simp
    have hcancel : ui₂.left ≫ (E.unitIso.app target₂).inv.left = 𝟙 (Y i₂) := by
      change ((E.unitIso.app target₂).hom ≫ (E.unitIso.app target₂).inv).left = 𝟙 (Y i₂)
      rw [(E.unitIso.app target₂).hom_inv_id]
      rfl
    change u.left ≫
        ((E.inverse.map (E.functor.map m₂)).left ≫
          (E.unitIso.app target₂).inv.left) = f₂
    rw [← Category.assoc, hnat_left']
    exact
      (Category.assoc f₂ ui₂.left (E.unitIso.inv.app target₂).left).trans (by
        have hcancel' : ui₂.left ≫ (E.unitIso.inv.app target₂).left = 𝟙 (Y i₂) := by
          simpa [ui₂] using hcancel
        change f₂ ≫ (ui₂.left ≫ (E.unitIso.inv.app target₂).left) = f₂
        exact (congrArg (fun t ↦ f₂ ≫ t) hcancel').trans (Category.comp_id f₂))
  have hl₁w : l₁ ≫ g i₁ = qUp.hom := by
    change
      inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
          (Yₛ.p.map q) (Yₛ.p.map f₁)
          (by rw [← Functor.map_comp, hf₁]) ≫
        g i₁ =
      (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) (Yₛ.p.map q)).hom
    exact
      inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
        (Yₛ.p.map q) (Yₛ.p.map f₁)
        (by rw [← Functor.map_comp, hf₁])
  have hl₂w : l₂ ≫ g i₂ = qUp.hom := by
    change
      inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
          (Yₛ.p.map q) (Yₛ.p.map f₂)
          (by rw [← Functor.map_comp, hf₂]) ≫
        g i₂ =
      (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) (Yₛ.p.map q)).hom
    exact
      inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
        (Yₛ.p.map q) (Yₛ.p.map f₂)
        (by rw [← Functor.map_comp, hf₂])
  have hpull :=
    inherited_basis_descent_hom_pullHom_refinement
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D u.left qUp.hom q huq
      l₁ l₂ hl₁w hl₂w
      f₁ f₂ hu₁ hu₂
  rw [inherited_basis_simple_forget_to_source_descent_hom]
  let cInv :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk (Yₛ.p.map q))).inv.left
  let d := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp.hom l₁ l₂ hl₁w hl₂w
  have hu₁base : Yₛ.p.map u.left ≫ Yₛ.p.map l₁ = Yₛ.p.map f₁ := by
    rw [← Functor.map_comp, hu₁]
    rfl
  have hu₂base : Yₛ.p.map u.left ≫ Yₛ.p.map l₂ = Yₛ.p.map f₂ := by
    rw [← Functor.map_comp, hu₂]
    rfl
  have hc₁ : cInv ≫ Yₛ.p.map l₁ = Yₛ.p.map f₁ := by
    change
      ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
        (Over.mk (Yₛ.p.map q))).inv.left ≫ Yₛ.p.map l₁ = Yₛ.p.map f₁
    rw [hbase]
    exact hu₁base
  have hc₂ : cInv ≫ Yₛ.p.map l₂ = Yₛ.p.map f₂ := by
    change
      ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
        (Over.mk (Yₛ.p.map q))).inv.left ≫ Yₛ.p.map l₂ = Yₛ.p.map f₂
    rw [hbase]
    exact hu₂base
  have hpull_base_congr
      {k₁ k₂ : Yₛ.p.obj Z ⟶ Yₛ.p.obj qUp.left} (hk : k₁ = k₂)
      (hk₁₁ : k₁ ≫ Yₛ.p.map l₁ = Yₛ.p.map f₁)
      (hk₁₂ : k₁ ≫ Yₛ.p.map l₂ = Yₛ.p.map f₂)
      (hk₂₁ : k₂ ≫ Yₛ.p.map l₁ = Yₛ.p.map f₁)
      (hk₂₂ : k₂ ≫ Yₛ.p.map l₂ = Yₛ.p.map f₂) :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d k₁
          (Yₛ.p.map f₁) (Yₛ.p.map f₂) hk₁₁ hk₁₂ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom d k₂
          (Yₛ.p.map f₁) (Yₛ.p.map f₂) hk₂₁ hk₂₂ := by
    subst k₂
    rfl
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom d cInv
        (Yₛ.p.map f₁) (Yₛ.p.map f₂) hc₁ hc₂ =
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂
  have hpull_base :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d cInv
          (Yₛ.p.map f₁) (Yₛ.p.map f₂) hc₁ hc₂ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (Yₛ.p.map u.left)
          (Yₛ.p.map f₁) (Yₛ.p.map f₂) hu₁base hu₂base :=
    hpull_base_congr hbase hc₁ hc₂ hu₁base hu₂base
  have hpull_actual :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (Yₛ.p.map u.left)
          (Yₛ.p.map f₁) (Yₛ.p.map f₂) hu₁base hu₂base =
        inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ := by
    simpa [d, qUp, l₁, l₂] using hpull
  exact hpull_base.trans hpull_actual

/-- Helper for Lemma 8.10.5: an actual upstairs target overlap of a `G F` descent datum remains
compatible after postcomposing both local source pullbacks with their local target arrows. -/
theorem inherited_basis_descent_hom_target_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ g i₂ = q := by cat_disch) :
    (SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
        (inherited_basis_descent_hom (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂).1 ≫
      ((SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
          ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
            (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)).hom.1) ≫
      g i₂ =
    ((SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
        ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
          (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)).hom.1) ≫
      g i₁ := by
  let H := SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)
  let δ := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let e₂ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  let loc₁ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)
  let loc₂ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)
  let xPull₁ : (G F).Fiber Z :=
    (((canonicalFiberPseudofunctor (G F)).map f₁.op.toLoc).toFunctor.obj (D.obj i₁))
  let xPull₂ : (G F).Fiber Z :=
    (((canonicalFiberPseudofunctor (G F)).map f₂.op.toLoc).toFunctor.obj (D.obj i₂))
  let locP₁ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F xPull₁
  let locP₂ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F xPull₂
  have hnat := inherited_basis_local_target_iso_naturality
    (J := J) (Yₛ := Yₛ) F δ
  have hnat_val0 := congrArg (fun η => η.1) hnat
  have hnat_val : H.map δ.1 ≫ locP₂.hom.1 = locP₁.hom.1 := by
    change H.map δ.1 ≫ locP₂.hom.1 = locP₁.hom.1
    simpa only [H, δ, locP₁, locP₂, xPull₁, xPull₂, inherited_source_fiber_forget,
      StackInGroupoidsOver.Hom.fiberFunctor] using hnat_val0
  have hpb₂X : e₂.hom.1 ≫
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
          (inherited_source_fiber_obj (F := F) (D.obj i₂)) =
      (canonicalPullbackChoice (G F)).map f₂ (D.obj i₂) := by
    simpa [e₂] using inherited_source_pullback_comparison_hom_postcompose
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  have hpb₁X : e₁.inv.1 ≫
        (canonicalPullbackChoice (G F)).map f₁ (D.obj i₁) =
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
        (inherited_source_fiber_obj (F := F) (D.obj i₁)) := by
    simpa [e₁] using inherited_source_pullback_comparison_inv_postcompose_owner
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  have htarget₂ :
      (G F).map ((canonicalPullbackChoice (G F)).map f₂ (D.obj i₂)) ≫ loc₂.hom.1 =
        locP₂.hom.1 ≫ f₂ := by
    simpa [loc₂, locP₂, xPull₂] using
      inherited_basis_local_target_iso_pullback_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F f₂ (D.obj i₂)
  have htarget₁ :
      (G F).map ((canonicalPullbackChoice (G F)).map f₁ (D.obj i₁)) ≫ loc₁.hom.1 =
        locP₁.hom.1 ≫ f₁ := by
    simpa [loc₁, locP₁, xPull₁] using
      inherited_basis_local_target_iso_pullback_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F f₁ (D.obj i₁)
  change
    H.map (e₁.inv.1 ≫ δ.1 ≫ e₂.hom.1) ≫ (H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
      (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫ loc₂.hom.1) ≫ g i₂ =
    (H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
      (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫ loc₁.hom.1) ≫ g i₁
  calc
    H.map (e₁.inv.1 ≫ δ.1 ≫ e₂.hom.1) ≫ (H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
        (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫ loc₂.hom.1) ≫ g i₂
        = (H.map e₁.inv.1 ≫ H.map δ.1 ≫ H.map e₂.hom.1 ≫ H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
            (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫ loc₂.hom.1) ≫ g i₂ := by
          simp only [Functor.map_comp, Category.assoc]
    _ = (H.map e₁.inv.1 ≫ H.map δ.1 ≫ (G F).map ((canonicalPullbackChoice (G F)).map f₂ (D.obj i₂)) ≫ loc₂.hom.1) ≫ g i₂ := by
          have hm : H.map e₂.hom.1 ≫ H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
              (inherited_source_fiber_obj (F := F) (D.obj i₂))) =
              (G F).map ((canonicalPullbackChoice (G F)).map f₂ (D.obj i₂)) := by
            rw [← Functor.map_comp]
            exact congrArg H.map hpb₂X
          calc
            (H.map e₁.inv.1 ≫ H.map δ.1 ≫ H.map e₂.hom.1 ≫
                  H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
                    (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫ loc₂.hom.1) ≫ g i₂ =
                (H.map e₁.inv.1 ≫ H.map δ.1 ≫
                  (H.map e₂.hom.1 ≫ H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
                    (inherited_source_fiber_obj (F := F) (D.obj i₂)))) ≫ loc₂.hom.1) ≫ g i₂ := by
                  simp only [Category.assoc]
            _ = (H.map e₁.inv.1 ≫ H.map δ.1 ≫
                  (G F).map ((canonicalPullbackChoice (G F)).map f₂ (D.obj i₂)) ≫ loc₂.hom.1) ≫ g i₂ := by
                  exact congrArg (fun t ↦ (H.map e₁.inv.1 ≫ H.map δ.1 ≫ t ≫ loc₂.hom.1) ≫ g i₂) hm
    _ = (H.map e₁.inv.1 ≫ H.map δ.1 ≫ locP₂.hom.1 ≫ f₂) ≫ g i₂ := by
          calc
            (H.map e₁.inv.1 ≫ H.map δ.1 ≫ (G F).map ((canonicalPullbackChoice (G F)).map f₂ (D.obj i₂)) ≫ loc₂.hom.1) ≫ g i₂ =
                (H.map e₁.inv.1 ≫ H.map δ.1 ≫
                  ((G F).map ((canonicalPullbackChoice (G F)).map f₂ (D.obj i₂)) ≫ loc₂.hom.1)) ≫ g i₂ := by
                  simp only [Category.assoc]
            _ = (H.map e₁.inv.1 ≫ H.map δ.1 ≫ (locP₂.hom.1 ≫ f₂)) ≫ g i₂ := by
                  exact congrArg (fun t ↦ (H.map e₁.inv.1 ≫ H.map δ.1 ≫ t) ≫ g i₂) htarget₂
            _ = (H.map e₁.inv.1 ≫ H.map δ.1 ≫ locP₂.hom.1 ≫ f₂) ≫ g i₂ := by
                  simp only [Category.assoc]
    _ = (H.map e₁.inv.1 ≫ locP₁.hom.1 ≫ f₂) ≫ g i₂ := by
          calc
            (H.map e₁.inv.1 ≫ H.map δ.1 ≫ locP₂.hom.1 ≫ f₂) ≫ g i₂ =
                (H.map e₁.inv.1 ≫ (H.map δ.1 ≫ locP₂.hom.1) ≫ f₂) ≫ g i₂ := by
                  simp only [Category.assoc]
            _ = (H.map e₁.inv.1 ≫ locP₁.hom.1 ≫ f₂) ≫ g i₂ := by
                  exact congrArg (fun t ↦ (H.map e₁.inv.1 ≫ t ≫ f₂) ≫ g i₂) hnat_val
    _ = (H.map e₁.inv.1 ≫ locP₁.hom.1) ≫ q := by
          rw [← hf₂]
          simp only [Category.assoc]
          rfl
    _ = (H.map e₁.inv.1 ≫ ((G F).map ((canonicalPullbackChoice (G F)).map f₁ (D.obj i₁)) ≫ loc₁.hom.1)) ≫ g i₁ := by
          rw [← hf₁]
          calc
            (H.map e₁.inv.1 ≫ locP₁.hom.1) ≫ f₁ ≫ g i₁ =
                (H.map e₁.inv.1 ≫ (locP₁.hom.1 ≫ f₁)) ≫ g i₁ := by
                  simp only [Category.assoc]
            _ = (H.map e₁.inv.1 ≫ ((G F).map ((canonicalPullbackChoice (G F)).map f₁ (D.obj i₁)) ≫ loc₁.hom.1)) ≫ g i₁ := by
                  exact congrArg (fun t ↦ (H.map e₁.inv.1 ≫ t) ≫ g i₁) htarget₁.symm
    _ = (H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
            (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫ loc₁.hom.1) ≫ g i₁ := by
          have hm : H.map e₁.inv.1 ≫ (G F).map ((canonicalPullbackChoice (G F)).map f₁ (D.obj i₁)) =
              H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
                (inherited_source_fiber_obj (F := F) (D.obj i₁))) := by
            rw [← Functor.map_comp]
            exact congrArg H.map hpb₁X
          calc
            (H.map e₁.inv.1 ≫ ((G F).map ((canonicalPullbackChoice (G F)).map f₁ (D.obj i₁)) ≫ loc₁.hom.1)) ≫ g i₁ =
                ((H.map e₁.inv.1 ≫ (G F).map ((canonicalPullbackChoice (G F)).map f₁ (D.obj i₁))) ≫ loc₁.hom.1) ≫ g i₁ := by
                  simp only [Category.assoc]
            _ = (H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
                    (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫ loc₁.hom.1) ≫ g i₁ := by
                  exact congrArg (fun t ↦ (t ≫ loc₁.hom.1) ≫ g i₁) hm

/-- Helper for Lemma 8.10.5: the literal-base overlap map in the simple source-forget descent
datum has the corresponding target postcomposition compatibility. -/
theorem inherited_basis_simple_forget_to_source_descent_hom_target_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    (SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
        (inherited_basis_simple_forget_to_source_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂).1 ≫
      ((SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
          ((canonicalPullbackChoice Xₛ.p).map f₂
            (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)).hom.1) ≫
      g i₂ =
    ((SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
        ((canonicalPullbackChoice Xₛ.p).map f₁
          (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)).hom.1) ≫
      g i₁ := by
  let H := SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)
  let cInv :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  let qUp := inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q
  let l₁ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁
  let l₂ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂
  have hc₁ : cInv ≫ Yₛ.p.map l₁ = f₁ := by
    calc
      cInv ≫ Yₛ.p.map l₁ =
          cInv ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q)).hom.left ≫ f₁) := by
              exact congrArg (fun t ↦ cInv ≫ t)
                (inherited_basis_target_slice_inverse_leg_base_w
                  (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
      _ = f₁ := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q f₁
  have hc₂ : cInv ≫ Yₛ.p.map l₂ = f₂ := by
    calc
      cInv ≫ Yₛ.p.map l₂ =
          cInv ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q)).hom.left ≫ f₂) := by
              exact congrArg (fun t ↦ cInv ≫ t)
                (inherited_basis_target_slice_inverse_leg_base_w
                  (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
      _ = f₂ := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q f₂
  let d := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp.hom l₁ l₂
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  let A₁ := ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
    (Yₛ.p.map l₁).op.toLoc cInv.op.toLoc f₁.op.toLoc
    (base_comp_toLoc_eq (f := Yₛ.p.map l₁) (g := cInv) (gf := f₁) hc₁)).hom.toNatTrans.app
      (inherited_source_fiber_obj (F := F) (D.obj i₁))
  let A₂ := ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
    (Yₛ.p.map l₂).op.toLoc cInv.op.toLoc f₂.op.toLoc
    (base_comp_toLoc_eq (f := Yₛ.p.map l₂) (g := cInv) (gf := f₂) hc₂)).inv.toNatTrans.app
      (inherited_source_fiber_obj (F := F) (D.obj i₂))
  let T := ((canonicalFiberPseudofunctor Xₛ.p).map cInv.op.toLoc).toFunctor
  let pb₁ := (canonicalPullbackChoice Xₛ.p).map f₁
    (inherited_source_fiber_obj (F := F) (D.obj i₁))
  let pb₂ := (canonicalPullbackChoice Xₛ.p).map f₂
    (inherited_source_fiber_obj (F := F) (D.obj i₂))
  let pbl₁ := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map l₁)
    (inherited_source_fiber_obj (F := F) (D.obj i₁))
  let pbl₂ := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map l₂)
    (inherited_source_fiber_obj (F := F) (D.obj i₂))
  let pbc₁ := (canonicalPullbackChoice Xₛ.p).map cInv
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map l₁).op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D.obj i₁)))
  let pbc₂ := (canonicalPullbackChoice Xₛ.p).map cInv
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map l₂).op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D.obj i₂)))
  let loc₁ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)
  let loc₂ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)
  have hraw :
      H.map d.1 ≫ (H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ =
        (H.map pbl₁ ≫ loc₁.hom.1) ≫ g i₁ := by
    simpa only [H, d, pbl₁, pbl₂, loc₁, loc₂, qUp, l₁, l₂] using
      inherited_basis_descent_hom_target_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp.hom l₁ l₂
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  have hA₂ : A₂.1 ≫ pb₂ = pbc₂ ≫ pbl₂ := by
    simpa [A₂, pb₂, pbc₂, pbl₂] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := Xₛ.p) (f := Yₛ.p.map l₂) (g := cInv) (gf := f₂) (hgf := hc₂)
        (inherited_source_fiber_obj (F := F) (D.obj i₂))
  have hT : (T.map d).1 ≫ pbc₂ = pbc₁ ≫ d.1 := by
    simpa [T, d, pbc₁, pbc₂] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Xₛ.p) (f := cInv) (φ := d)
  have hA₁ : A₁.1 ≫ pbc₁ ≫ pbl₁ = pb₁ := by
    simpa [A₁, pb₁, pbc₁, pbl₁] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := Xₛ.p) (f := Yₛ.p.map l₁) (g := cInv) (gf := f₁) (hgf := hc₁)
        (inherited_source_fiber_obj (F := F) (D.obj i₁))
  rw [inherited_basis_simple_forget_to_source_descent_hom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  change H.map (A₁.1 ≫ (T.map d).1 ≫ A₂.1) ≫ (H.map pb₂ ≫ loc₂.hom.1) ≫ g i₂ =
    (H.map pb₁ ≫ loc₁.hom.1) ≫ g i₁
  calc
    H.map (A₁.1 ≫ (T.map d).1 ≫ A₂.1) ≫ (H.map pb₂ ≫ loc₂.hom.1) ≫ g i₂
        = (H.map A₁.1 ≫ H.map (T.map d).1 ≫ H.map A₂.1 ≫ H.map pb₂ ≫ loc₂.hom.1) ≫ g i₂ := by
          simp only [Functor.map_comp, Category.assoc]
    _ = (H.map A₁.1 ≫ H.map (T.map d).1 ≫ H.map pbc₂ ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ := by
          have hm : H.map A₂.1 ≫ H.map pb₂ = H.map pbc₂ ≫ H.map pbl₂ := by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg H.map hA₂
          calc
            (H.map A₁.1 ≫ H.map (T.map d).1 ≫ H.map A₂.1 ≫ H.map pb₂ ≫ loc₂.hom.1) ≫ g i₂ =
                (H.map A₁.1 ≫ H.map (T.map d).1 ≫ (H.map A₂.1 ≫ H.map pb₂) ≫ loc₂.hom.1) ≫ g i₂ := by
                  simp only [Category.assoc]
            _ = (H.map A₁.1 ≫ H.map (T.map d).1 ≫ (H.map pbc₂ ≫ H.map pbl₂) ≫ loc₂.hom.1) ≫ g i₂ := by
                  exact congrArg (fun t ↦ (H.map A₁.1 ≫ H.map (T.map d).1 ≫ t ≫ loc₂.hom.1) ≫ g i₂) hm
            _ = (H.map A₁.1 ≫ H.map (T.map d).1 ≫ H.map pbc₂ ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ := by
                  simp only [Category.assoc]
    _ = (H.map A₁.1 ≫ H.map pbc₁ ≫ H.map d.1 ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ := by
          have hm : H.map (T.map d).1 ≫ H.map pbc₂ = H.map pbc₁ ≫ H.map d.1 := by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg H.map hT
          calc
            (H.map A₁.1 ≫ H.map (T.map d).1 ≫ H.map pbc₂ ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ =
                (H.map A₁.1 ≫ (H.map (T.map d).1 ≫ H.map pbc₂) ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ := by
                  simp only [Category.assoc]
            _ = (H.map A₁.1 ≫ (H.map pbc₁ ≫ H.map d.1) ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ := by
                  exact congrArg (fun t ↦ (H.map A₁.1 ≫ t ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂) hm
            _ = (H.map A₁.1 ≫ H.map pbc₁ ≫ H.map d.1 ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ := by
                  simp only [Category.assoc]
    _ = (H.map A₁.1 ≫ H.map pbc₁ ≫ (H.map pbl₁ ≫ loc₁.hom.1)) ≫ g i₁ := by
          calc
            (H.map A₁.1 ≫ H.map pbc₁ ≫ H.map d.1 ≫ H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂ =
                (H.map A₁.1 ≫ H.map pbc₁ ≫ (H.map d.1 ≫ (H.map pbl₂ ≫ loc₂.hom.1) ≫ g i₂)) := by
                  simp only [Category.assoc]
            _ = H.map A₁.1 ≫ H.map pbc₁ ≫ ((H.map pbl₁ ≫ loc₁.hom.1) ≫ g i₁) := by
                  exact congrArg (fun t ↦ H.map A₁.1 ≫ H.map pbc₁ ≫ t) hraw
            _ = (H.map A₁.1 ≫ H.map pbc₁ ≫ (H.map pbl₁ ≫ loc₁.hom.1)) ≫ g i₁ := by
                  simp only [Category.assoc]
    _ = (H.map pb₁ ≫ loc₁.hom.1) ≫ g i₁ := by
          have hm : H.map A₁.1 ≫ H.map pbc₁ ≫ H.map pbl₁ = H.map pb₁ := by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg H.map hA₁
          calc
            (H.map A₁.1 ≫ H.map pbc₁ ≫ (H.map pbl₁ ≫ loc₁.hom.1)) ≫ g i₁ =
                ((H.map A₁.1 ≫ H.map pbc₁ ≫ H.map pbl₁) ≫ loc₁.hom.1) ≫ g i₁ := by
                  simp only [Category.assoc]
            _ = (H.map pb₁ ≫ loc₁.hom.1) ≫ g i₁ := by
                  exact congrArg (fun t ↦ (t ≫ loc₁.hom.1) ≫ g i₁) hm


end

end CategoryTheory
