import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.LiteralBaseDescentLaws

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open FibredCategoryOver
open Functor IsStronglyCartesian
open Opposite
open StackInGroupoidsOver.Hom

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: the simple literal-base overlap map obtained by pulling the
source-forgotten upstairs overlap along the inverse counit of the target slice equivalence. -/
noncomputable def inherited_basis_simple_forget_to_source_descent_hom
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i₁))) ⟶
      (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i₂))) :=
  let cInv :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (inherited_basis_descent_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
      (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
      (inherited_basis_target_slice_inverse_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
      (inherited_basis_target_slice_inverse_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
      (inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
      (inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂))
    cInv f₁ f₂
    (by
      calc
        cInv ≫ Yₛ.p.map
            (inherited_basis_target_slice_inverse_leg
              (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁) =
          cInv ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q)).hom.left ≫ f₁) := by
              exact congrArg (fun t ↦ cInv ≫ t)
                (inherited_basis_target_slice_inverse_leg_base_w
                  (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        _ = f₁ := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q f₁)
    (by
      calc
        cInv ≫ Yₛ.p.map
            (inherited_basis_target_slice_inverse_leg
              (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂) =
          cInv ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q)).hom.left ≫ f₂) := by
              exact congrArg (fun t ↦ cInv ≫ t)
                (inherited_basis_target_slice_inverse_leg_base_w
                  (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
        _ = f₂ := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q f₂)

theorem inherited_basis_simple_forget_to_source_descent_hom_self
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i : ι}
    (f : Z ⟶ Yₛ.p.obj (Y i)) (hf : f ≫ Yₛ.p.map (g i) = q := by cat_disch) :
    inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f f hf hf = 𝟙 _ := by
  let cInv :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  let l := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f hf
  have hc : cInv ≫ Yₛ.p.map l = f := by
    calc
      cInv ≫ Yₛ.p.map l =
          cInv ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
              (Over.mk q)).hom.left ≫ f) := by
            exact congrArg (fun t ↦ cInv ≫ t)
              (inherited_basis_target_slice_inverse_leg_base_w
                (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f hf)
      _ = f := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q f
  rw [inherited_basis_simple_forget_to_source_descent_hom]
  rw [inherited_basis_descent_hom_self_normalize
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) D
    (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f hf)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f hf)]
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (𝟙 (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map l).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i))))
      cInv f f hc hc = 𝟙 _
  have hc_toLoc : (Yₛ.p.map l).op.toLoc ≫ cInv.op.toLoc = f.op.toLoc :=
    base_comp_toLoc_eq (f := Yₛ.p.map l) (g := cInv) (gf := f) hc
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  erw [((canonicalFiberPseudofunctor Xₛ.p).map cInv.op.toLoc).toFunctor.map_id]
  let A := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    (Yₛ.p.map l).op.toLoc cInv.op.toLoc f.op.toLoc hc_toLoc
  change A.hom.toNatTrans.app
      (inherited_source_fiber_obj (F := F) (D.obj i)) ≫
    𝟙 _ ≫ A.inv.toNatTrans.app (inherited_source_fiber_obj (F := F) (D.obj i)) = 𝟙 _
  simp only [Category.id_comp]
  change (A.hom ≫ A.inv).toNatTrans.app
      (inherited_source_fiber_obj (F := F) (D.obj i)) = 𝟙 _
  rw [A.hom_inv_id]
  rfl

theorem inherited_basis_simple_pullHom_comp
    {X₁ X₂ X₃ : C}
    {M₁ : (canonicalFiberPseudofunctor Xₛ.p).obj (.mk (op X₁))}
    {M₂ : (canonicalFiberPseudofunctor Xₛ.p).obj (.mk (op X₂))}
    {M₃ : (canonicalFiberPseudofunctor Xₛ.p).obj (.mk (op X₃))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (φ : ((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : ((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      ((canonicalFiberPseudofunctor Xₛ.p).map f₃.op.toLoc).toFunctor.obj M₃)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch)
    (hgf₃ : g ≫ f₃ = gf₃ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor Xₛ.p) φ g gf₁ gf₂ hgf₁ hgf₂ ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor Xₛ.p) ψ g gf₂ gf₃ hgf₂ hgf₃ =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor Xₛ.p) (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp, Category.assoc]
  let A₂ := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)
  let A₁ := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)
  let A₃ := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    f₃.op.toLoc g.op.toLoc gf₃.op.toLoc (by aesop)
  let mφ := ((canonicalFiberPseudofunctor Xₛ.p).map g.op.toLoc).toFunctor.map φ
  let mψ := ((canonicalFiberPseudofunctor Xₛ.p).map g.op.toLoc).toFunctor.map ψ
  have hA₂ :
      A₂.inv.toNatTrans.app M₂ ≫ A₂.hom.toNatTrans.app M₂ = 𝟙 _ := by
    change (A₂.inv ≫ A₂.hom).toNatTrans.app M₂ = 𝟙 _
    rw [A₂.inv_hom_id]
    rfl
  have hA₂' :
      A₂.inv.toNatTrans.app M₂ ≫ A₂.hom.toNatTrans.app M₂ =
        𝟙 (((canonicalFiberPseudofunctor Xₛ.p).map g.op.toLoc).toFunctor.obj
          (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj M₂)) := by
    simpa [Cat.Hom.comp_toFunctor] using hA₂
  change
    A₁.hom.toNatTrans.app M₁ ≫ mφ ≫ A₂.inv.toNatTrans.app M₂ ≫
      A₂.hom.toNatTrans.app M₂ ≫ mψ ≫ A₃.inv.toNatTrans.app M₃ =
    A₁.hom.toNatTrans.app M₁ ≫ (mφ ≫ mψ) ≫ A₃.inv.toNatTrans.app M₃
  calc
    A₁.hom.toNatTrans.app M₁ ≫ mφ ≫ A₂.inv.toNatTrans.app M₂ ≫
        A₂.hom.toNatTrans.app M₂ ≫ mψ ≫ A₃.inv.toNatTrans.app M₃ =
      A₁.hom.toNatTrans.app M₁ ≫ mφ ≫
        (A₂.inv.toNatTrans.app M₂ ≫ A₂.hom.toNatTrans.app M₂) ≫
          mψ ≫ A₃.inv.toNatTrans.app M₃ := by
          simp only [Category.assoc]
    _ =
      A₁.hom.toNatTrans.app M₁ ≫ mφ ≫ 𝟙 _ ≫
          mψ ≫ A₃.inv.toNatTrans.app M₃ := by
          exact congrArg
            (fun t ↦ A₁.hom.toNatTrans.app M₁ ≫ mφ ≫ t ≫ mψ ≫
              A₃.inv.toNatTrans.app M₃) hA₂'
    _ =
      A₁.hom.toNatTrans.app M₁ ≫ (mφ ≫ mψ) ≫ A₃.inv.toNatTrans.app M₃ := by
          simp only [Category.id_comp, ← Category.assoc]

theorem inherited_basis_simple_pullHom_comm
    {X₁ X₂ : C}
    {M₁ : (canonicalFiberPseudofunctor Xₛ.p).obj (.mk (op X₁))}
    {M₂ : (canonicalFiberPseudofunctor Xₛ.p).obj (.mk (op X₂))}
    {N₁ : (canonicalFiberPseudofunctor Xₛ.p).obj (.mk (op X₁))}
    {N₂ : (canonicalFiberPseudofunctor Xₛ.p).obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (α₁ : M₁ ⟶ N₁) (α₂ : M₂ ⟶ N₂)
    (φ : ((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : ((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj N₁ ⟶
      ((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj N₂)
    (h :
      ((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map α₁ ≫ ψ =
        φ ≫ ((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map α₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((canonicalFiberPseudofunctor Xₛ.p).map gf₁.op.toLoc).toFunctor.map α₁ ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor Xₛ.p) ψ g gf₁ gf₂ hgf₁ hgf₂ =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor Xₛ.p) φ g gf₁ gf₂ hgf₁ hgf₂ ≫
      ((canonicalFiberPseudofunctor Xₛ.p).map gf₂.op.toLoc).toFunctor.map α₂ := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Category.assoc]
  let AM₁ := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)
  let AN₁ := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)
  let AM₂ := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)
  let AN₂ := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
    f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)
  let T := ((canonicalFiberPseudofunctor Xₛ.p).map g.op.toLoc).toFunctor
  have hleft :
      ((canonicalFiberPseudofunctor Xₛ.p).map gf₁.op.toLoc).toFunctor.map α₁ ≫
          AN₁.hom.toNatTrans.app N₁ =
        AM₁.hom.toNatTrans.app M₁ ≫
          T.map (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map α₁) := by
    simpa [AM₁, AN₁, T] using
      ((canonicalFiberPseudofunctor Xₛ.p).mapComp'_hom_naturality
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop) α₁)
  have hright :
      T.map (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map α₂) ≫
          AN₂.inv.toNatTrans.app N₂ =
        AM₂.inv.toNatTrans.app M₂ ≫
          ((canonicalFiberPseudofunctor Xₛ.p).map gf₂.op.toLoc).toFunctor.map α₂ := by
    simpa [AM₂, AN₂, T] using
      ((canonicalFiberPseudofunctor Xₛ.p).mapComp'_inv_naturality
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop) α₂)
  change
    ((canonicalFiberPseudofunctor Xₛ.p).map gf₁.op.toLoc).toFunctor.map α₁ ≫
        AN₁.hom.toNatTrans.app N₁ ≫ T.map ψ ≫ AN₂.inv.toNatTrans.app N₂ =
      AM₁.hom.toNatTrans.app M₁ ≫ T.map φ ≫ AM₂.inv.toNatTrans.app M₂ ≫
        ((canonicalFiberPseudofunctor Xₛ.p).map gf₂.op.toLoc).toFunctor.map α₂
  calc
    ((canonicalFiberPseudofunctor Xₛ.p).map gf₁.op.toLoc).toFunctor.map α₁ ≫
        AN₁.hom.toNatTrans.app N₁ ≫ T.map ψ ≫ AN₂.inv.toNatTrans.app N₂ =
      AM₁.hom.toNatTrans.app M₁ ≫
          T.map (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map α₁) ≫
        T.map ψ ≫ AN₂.inv.toNatTrans.app N₂ := by
          simpa only [← Category.assoc] using
            congrArg (fun t ↦ t ≫ T.map ψ ≫ AN₂.inv.toNatTrans.app N₂) hleft
    _ = AM₁.hom.toNatTrans.app M₁ ≫
          T.map ((((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map α₁ ≫ ψ)) ≫
        AN₂.inv.toNatTrans.app N₂ := by
          simp only [Functor.map_comp]
          cat_disch
    _ = AM₁.hom.toNatTrans.app M₁ ≫
          T.map (φ ≫ ((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map α₂) ≫
        AN₂.inv.toNatTrans.app N₂ := by
          rw [h]
    _ = AM₁.hom.toNatTrans.app M₁ ≫ T.map φ ≫
          T.map (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map α₂) ≫
        AN₂.inv.toNatTrans.app N₂ := by
          simp only [Functor.map_comp]
          cat_disch
    _ = AM₁.hom.toNatTrans.app M₁ ≫ T.map φ ≫ AM₂.inv.toNatTrans.app M₂ ≫
        ((canonicalFiberPseudofunctor Xₛ.p).map gf₂.op.toLoc).toFunctor.map α₂ := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ AM₁.hom.toNatTrans.app M₁ ≫ T.map φ ≫ t) hright

theorem inherited_basis_simple_forget_to_source_descent_hom_pullHom
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z' Z : C} (k : Z' ⟶ Z) (q : Z ⟶ Yₛ.p.obj y) (q' : Z' ⟶ Yₛ.p.obj y)
    (hq : k ≫ q = q')
    {i₁ i₂ : ι} (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch)
    (kf₁ : Z' ⟶ Yₛ.p.obj (Y i₁)) (kf₂ : Z' ⟶ Yₛ.p.obj (Y i₂))
    (hkf₁ : k ≫ f₁ = kf₁ := by cat_disch) (hkf₂ : k ≫ f₂ = kf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (inherited_basis_simple_forget_to_source_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂)
        k kf₁ kf₂ hkf₁ hkf₂ =
      inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q' kf₁ kf₂
        (by rw [← hq, ← hkf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hkf₂, Category.assoc, hf₂]) := by
  let cInv :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  let cInv' :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q')).inv.left
  let r := inherited_basis_target_slice_inverse_refinement
    (J := J) (Yₛ := Yₛ) (y := y) k q q' hq
  have hcomp : cInv' ≫ Yₛ.p.map r.left = k ≫ cInv := by
    have hcancel :
        cInv' ≫
            ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
              (Over.mk q')).hom.left =
          𝟙 Z' := by
      simpa [cInv'] using
        inherited_basis_target_slice_inverse_counit_inv_hom_left
          (J := J) (Yₛ := Yₛ) q'
    have h1 :
        cInv' ≫ Yₛ.p.map r.left =
          cInv' ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q')).hom.left ≫ k ≫
              ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q)).inv.left) :=
      congrArg (fun t ↦ cInv' ≫ t)
        (inherited_basis_target_slice_inverse_refinement_base_w
          (J := J) (Yₛ := Yₛ) (y := y) k q q' hq)
    have h2 :
        cInv' ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q')).hom.left ≫ k ≫
              ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q)).inv.left) =
          (cInv' ≫
            ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
              (Over.mk q')).hom.left) ≫ k ≫ cInv := by
      simp [cInv, Category.assoc]
    have h3 :
        (cInv' ≫
            ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
              (Over.mk q')).hom.left) ≫ k ≫ cInv =
          k ≫ cInv := by
      simpa [Category.assoc] using
        congrArg (fun a ↦ a ≫ k ≫ cInv) hcancel
    exact h1.trans (h2.trans h3)
  have hmid :=
    inherited_basis_forget_to_source_descent_refinement_middle
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D k q q' hq
      f₁ f₂ hf₁ hf₂ kf₁ kf₂ hkf₁ hkf₂
  let qUp := inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q
  let qUp' := inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q'
  let l₁ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁
  let l₂ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂
  let l₁' := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q' kf₁
    (by rw [← hq, ← hkf₁, Category.assoc, hf₁])
  let l₂' := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q' kf₂
    (by rw [← hq, ← hkf₂, Category.assoc, hf₂])
  let d := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp.hom l₁ l₂
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  let d' := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp'.hom l₁' l₂'
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q' kf₁
      (by rw [← hq, ← hkf₁, Category.assoc, hf₁]))
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q' kf₂
      (by rw [← hq, ← hkf₂, Category.assoc, hf₂]))
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
  have hc₁' : cInv' ≫ Yₛ.p.map l₁' = kf₁ := by
    calc
      cInv' ≫ Yₛ.p.map l₁' =
          cInv' ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
              (Over.mk q')).hom.left ≫ kf₁) := by
            exact congrArg (fun t ↦ cInv' ≫ t)
              (inherited_basis_target_slice_inverse_leg_base_w
                (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q' kf₁
                (by rw [← hq, ← hkf₁, Category.assoc, hf₁]))
      _ = kf₁ := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q' kf₁
  have hc₂' : cInv' ≫ Yₛ.p.map l₂' = kf₂ := by
    calc
      cInv' ≫ Yₛ.p.map l₂' =
          cInv' ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
              (Over.mk q')).hom.left ≫ kf₂) := by
            exact congrArg (fun t ↦ cInv' ≫ t)
              (inherited_basis_target_slice_inverse_leg_base_w
                (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q' kf₂
                (by rw [← hq, ← hkf₂, Category.assoc, hf₂]))
      _ = kf₂ := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q' kf₂
  have hr₁ : Yₛ.p.map r.left ≫ Yₛ.p.map l₁ = Yₛ.p.map l₁' := by
    have hleg :=
      inherited_basis_target_slice_inverse_refinement_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
        k q q' hq f₁ hf₁ kf₁ hkf₁
    simpa [r, l₁, l₁', Functor.map_comp] using congrArg Yₛ.p.map hleg
  have hr₂ : Yₛ.p.map r.left ≫ Yₛ.p.map l₂ = Yₛ.p.map l₂' := by
    have hleg :=
      inherited_basis_target_slice_inverse_refinement_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g)
        k q q' hq f₂ hf₂ kf₂ hkf₂
    simpa [r, l₂, l₂', Functor.map_comp] using congrArg Yₛ.p.map hleg
  have hmid' :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (Yₛ.p.map r.left)
          (Yₛ.p.map l₁') (Yₛ.p.map l₂') hr₁ hr₂ =
        d' := by
    simpa [d, d', r, qUp, qUp', l₁, l₂, l₁', l₂'] using hmid
  have hkc₁ : (k ≫ cInv) ≫ Yₛ.p.map l₁ = kf₁ := by
    calc
      (k ≫ cInv) ≫ Yₛ.p.map l₁ = k ≫ (cInv ≫ Yₛ.p.map l₁) := by
        simp [Category.assoc]
      _ = k ≫ f₁ := by
        simpa [Category.assoc] using congrArg (fun t ↦ k ≫ t) hc₁
      _ = kf₁ := hkf₁
  have hkc₂ : (k ≫ cInv) ≫ Yₛ.p.map l₂ = kf₂ := by
    calc
      (k ≫ cInv) ≫ Yₛ.p.map l₂ = k ≫ (cInv ≫ Yₛ.p.map l₂) := by
        simp [Category.assoc]
      _ = k ≫ f₂ := by
        simpa [Category.assoc] using congrArg (fun t ↦ k ≫ t) hc₂
      _ = kf₂ := hkf₂
  have hrc₁ : (cInv' ≫ Yₛ.p.map r.left) ≫ Yₛ.p.map l₁ = kf₁ := by
    calc
      (cInv' ≫ Yₛ.p.map r.left) ≫ Yₛ.p.map l₁ =
          cInv' ≫ (Yₛ.p.map r.left ≫ Yₛ.p.map l₁) := by
        simp [Category.assoc]
      _ = cInv' ≫ Yₛ.p.map l₁' := by
        simpa [Category.assoc] using congrArg (fun t ↦ cInv' ≫ t) hr₁
      _ = kf₁ := hc₁'
  have hrc₂ : (cInv' ≫ Yₛ.p.map r.left) ≫ Yₛ.p.map l₂ = kf₂ := by
    calc
      (cInv' ≫ Yₛ.p.map r.left) ≫ Yₛ.p.map l₂ =
          cInv' ≫ (Yₛ.p.map r.left ≫ Yₛ.p.map l₂) := by
        simp [Category.assoc]
      _ = cInv' ≫ Yₛ.p.map l₂' := by
        simpa [Category.assoc] using congrArg (fun t ↦ cInv' ≫ t) hr₂
      _ = kf₂ := hc₂'
  have hpullL :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom d cInv f₁ f₂ hc₁ hc₂)
          k kf₁ kf₂ hkf₁ hkf₂ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (k ≫ cInv) kf₁ kf₂ hkc₁ hkc₂ := by
    exact
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom
        (F := canonicalFiberPseudofunctor Xₛ.p)
        (φ := d) (g := cInv) (gf₁ := f₁) (gf₂ := f₂)
        (g' := k) (g'f₁ := kf₁) (g'f₂ := kf₂)
        (hgf₁ := hc₁) (hgf₂ := hc₂) (hg'f₁ := hkf₁) (hg'f₂ := hkf₂))
  have hpullR :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (Yₛ.p.map r.left)
            (Yₛ.p.map l₁') (Yₛ.p.map l₂') hr₁ hr₂)
          cInv' kf₁ kf₂ hc₁' hc₂' =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (cInv' ≫ Yₛ.p.map r.left)
          kf₁ kf₂ hrc₁ hrc₂ := by
    exact
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom
        (F := canonicalFiberPseudofunctor Xₛ.p)
        (φ := d) (g := Yₛ.p.map r.left) (gf₁ := Yₛ.p.map l₁')
        (gf₂ := Yₛ.p.map l₂') (g' := cInv') (g'f₁ := kf₁) (g'f₂ := kf₂)
        (hgf₁ := hr₁) (hgf₂ := hr₂) (hg'f₁ := hc₁') (hg'f₂ := hc₂'))
  have hpull_base_congr
      {g₁ g₂ : Z' ⟶ Yₛ.p.obj qUp.left} (hg : g₁ = g₂)
      (hg₁₁ : g₁ ≫ Yₛ.p.map l₁ = kf₁) (hg₁₂ : g₁ ≫ Yₛ.p.map l₂ = kf₂)
      (hg₂₁ : g₂ ≫ Yₛ.p.map l₁ = kf₁) (hg₂₂ : g₂ ≫ Yₛ.p.map l₂ = kf₂) :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d g₁ kf₁ kf₂ hg₁₁ hg₁₂ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom d g₂ kf₁ kf₂ hg₂₁ hg₂₂ := by
    subst g₂
    rfl
  rw [inherited_basis_simple_forget_to_source_descent_hom, inherited_basis_simple_forget_to_source_descent_hom]
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom d cInv f₁ f₂ hc₁ hc₂)
        k kf₁ kf₂ hkf₁ hkf₂ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d' cInv' kf₁ kf₂ hc₁' hc₂'
  calc
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom d cInv f₁ f₂ hc₁ hc₂)
        k kf₁ kf₂ hkf₁ hkf₂ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (k ≫ cInv) kf₁ kf₂ hkc₁ hkc₂ := hpullL
    _ = Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (cInv' ≫ Yₛ.p.map r.left)
          kf₁ kf₂ hrc₁ hrc₂ := by
          exact hpull_base_congr hcomp.symm hkc₁ hkc₂ hrc₁ hrc₂
    _ = Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom d (Yₛ.p.map r.left)
            (Yₛ.p.map l₁') (Yₛ.p.map l₂') hr₁ hr₂)
          cInv' kf₁ kf₂ hc₁' hc₂' := hpullR.symm
    _ = Pseudofunctor.LocallyDiscreteOpToCat.pullHom d' cInv' kf₁ kf₂ hc₁' hc₂' := by
          rw [hmid']
          rfl

theorem inherited_basis_simple_forget_to_source_descent_hom_comp
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ i₃ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (f₃ : Z ⟶ Yₛ.p.obj (Y i₃))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch)
    (hf₃ : f₃ ≫ Yₛ.p.map (g i₃) = q := by cat_disch) :
    inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ ≫
      inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₂ f₃ hf₂ hf₃ =
    inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₃ hf₁ hf₃ := by
  let cInv :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  let qUp := inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q
  let l₁ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁
  let l₂ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂
  let l₃ := inherited_basis_target_slice_inverse_leg
    (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃
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
  have hc₃ : cInv ≫ Yₛ.p.map l₃ = f₃ := by
    calc
      cInv ≫ Yₛ.p.map l₃ =
          cInv ≫
            (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
                (Over.mk q)).hom.left ≫ f₃) := by
              exact congrArg (fun t ↦ cInv ≫ t)
                (inherited_basis_target_slice_inverse_leg_base_w
                  (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
      _ = f₃ := target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q f₃
  let d₁₂ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp.hom l₁ l₂
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  let d₂₃ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp.hom l₂ l₃
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
  let d₁₃ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D qUp.hom l₁ l₃
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
  have hcomp : d₁₂ ≫ d₂₃ = d₁₃ := by
    simpa [d₁₂, d₂₃, d₁₃, qUp, l₁, l₂, l₃] using
      inherited_basis_descent_hom_comp_normalize
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) D qUp.hom l₁ l₂ l₃
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
  rw [inherited_basis_simple_forget_to_source_descent_hom, inherited_basis_simple_forget_to_source_descent_hom, inherited_basis_simple_forget_to_source_descent_hom]
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom d₁₂ cInv f₁ f₂ hc₁ hc₂ ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d₂₃ cInv f₂ f₃ hc₂ hc₃ =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom d₁₃ cInv f₁ f₃ hc₁ hc₃
  rw [inherited_basis_simple_pullHom_comp (J := J) (Xₛ := Xₛ)
    (φ := d₁₂) (ψ := d₂₃) (g := cInv)
    (gf₁ := f₁) (gf₂ := f₂) (gf₃ := f₃)
    (hgf₁ := hc₁) (hgf₂ := hc₂) (hgf₃ := hc₃)]
  rw [hcomp]

theorem inherited_basis_simple_forget_to_source_descent_hom_comm
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    {D₁ D₂ : ((canonicalFiberPseudofunctor (G F)).DescentData g)}
    (φ : D₁ ⟶ D₂)
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁))) ≫
      inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₂ q f₁ f₂ hf₁ hf₂ =
    inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₁ q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂))) := by
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
  let α₁ := (inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁)
  let α₂ := (inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂)
  let d₁ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₁ qUp.hom l₁ l₂
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  let d₂ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₂ qUp.hom l₁ l₂
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  have hmid :
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map l₁).op.toLoc).toFunctor.map α₁) ≫ d₂ =
        d₁ ≫
          (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map l₂).op.toLoc).toFunctor.map α₂) := by
    simpa [α₁, α₂, d₁, d₂, qUp, l₁, l₂] using
      inherited_basis_forget_to_source_descent_literal_comm_middle
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) φ q f₁ f₂ hf₁ hf₂
  rw [inherited_basis_simple_forget_to_source_descent_hom, inherited_basis_simple_forget_to_source_descent_hom]
  change
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map α₁) ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom d₂ cInv f₁ f₂ hc₁ hc₂ =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom d₁ cInv f₁ f₂ hc₁ hc₂ ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map α₂)
  exact inherited_basis_simple_pullHom_comm
    (J := J) (Xₛ := Xₛ) (α₁ := α₁) (α₂ := α₂)
    (φ := d₁) (ψ := d₂) hmid cInv f₁ f₂ hc₁ hc₂

noncomputable def inherited_basis_simple_forget_to_source_descent_obj
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g)) :
    ((canonicalFiberPseudofunctor Xₛ.p).DescentData (fun i ↦ Yₛ.p.map (g i))) where
  obj i := inherited_source_fiber_obj (F := F) (D.obj i)
  hom := fun {Z} q {i₁ i₂} f₁ f₂ hf₁ hf₂ ↦
    inherited_basis_simple_forget_to_source_descent_hom (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂
  pullHom_hom := fun {Z' Z} k q q' hq {i₁ i₂} f₁ f₂ hf₁ hf₂ kf₁ kf₂ hkf₁ hkf₂ ↦
    inherited_basis_simple_forget_to_source_descent_hom_pullHom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D k q q' hq
      f₁ f₂ hf₁ hf₂ kf₁ kf₂ hkf₁ hkf₂
  hom_self := fun {Z} q {i} f hf ↦
    inherited_basis_simple_forget_to_source_descent_hom_self
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f hf
  hom_comp := fun {Z} q {i₁ i₂ i₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
    inherited_basis_simple_forget_to_source_descent_hom_comp
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ f₃ hf₁ hf₂ hf₃

noncomputable def inherited_basis_simple_forget_to_source_descent_functor
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y} :
    ((canonicalFiberPseudofunctor (G F)).DescentData g) ⥤
      ((canonicalFiberPseudofunctor Xₛ.p).DescentData (fun i ↦ Yₛ.p.map (g i))) where
  obj D := inherited_basis_simple_forget_to_source_descent_obj
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
  map {D₁ D₂} φ :=
    { hom i := (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i)
      comm := fun {Z} q {i₁ i₂} f₁ f₂ hf₁ hf₂ ↦
        inherited_basis_simple_forget_to_source_descent_hom_comm
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) φ q f₁ f₂ hf₁ hf₂ }
  map_id D := by
    ext i
    rfl
  map_comp φ ψ := by
    ext i
    rfl


end

end CategoryTheory
