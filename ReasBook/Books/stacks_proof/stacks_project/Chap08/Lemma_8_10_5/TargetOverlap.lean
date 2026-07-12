import StacksProject_2024.Chap08.Lemma_8_10_5.TargetPath

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

/-- Helper for Lemma 8.10.5: the source-side overlap morphism obtained from a fixed `G F`
descent datum becomes the expected equality after postcomposing with the canonical pullback tails
in `Xₛ` and `G F`. -/
theorem inherited_basis_ofObj_descent_hom_source_postcompose
    (F : Xₛ ⟶ Yₛ) [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (A : (G F).Fiber y)
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ g i₂ = q := by cat_disch) :
    (inherited_basis_descent_hom (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
        (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A)
        q f₁ f₂ hf₁ hf₂).1 ≫
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
        (inherited_source_fiber_obj (F := F)
          ((((canonicalFiberPseudofunctor (G F)).map (g i₂).op.toLoc).toFunctor.obj A))) ≫
      (canonicalPullbackChoice (G F)).map (g i₂) A =
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
        (inherited_source_fiber_obj (F := F)
          ((((canonicalFiberPseudofunctor (G F)).map (g i₁).op.toLoc).toFunctor.obj A))) ≫
      (canonicalPullbackChoice (G F)).map (g i₁) A := by
  let D := (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A)
  let e₁ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let e₂ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  let A₁ := (canonicalFiberPseudofunctor (G F)).mapComp'
    (g i₁).op.toLoc f₁.op.toLoc q.op.toLoc
    (by
      simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
        congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hf₁))
  let A₂ := (canonicalFiberPseudofunctor (G F)).mapComp'
    (g i₂).op.toLoc f₂.op.toLoc q.op.toLoc
    (by
      simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
        congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hf₂))
  let pbl₁X := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₁)
    (inherited_source_fiber_obj (F := F) (D.obj i₁))
  let pbl₂X := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f₂)
    (inherited_source_fiber_obj (F := F) (D.obj i₂))
  let pbl₁GF := (canonicalPullbackChoice (G F)).map f₁ (D.obj i₁)
  let pbl₂GF := (canonicalPullbackChoice (G F)).map f₂ (D.obj i₂)
  let pbg₁GF := (canonicalPullbackChoice (G F)).map (g i₁) A
  let pbg₂GF := (canonicalPullbackChoice (G F)).map (g i₂) A
  let pbqGF := (canonicalPullbackChoice (G F)).map q A
  have he₂ : e₂.hom.1 ≫ pbl₂X = pbl₂GF := by
    simpa [e₂, pbl₂X, pbl₂GF, D] using
      inherited_source_pullback_comparison_hom_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  have he₁ : e₁.inv.1 ≫ pbl₁GF = pbl₁X := by
    simpa [e₁, pbl₁X, pbl₁GF, D] using
      inherited_source_pullback_comparison_inv_postcompose_owner
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  have hA₂ : (A₂.hom.toNatTrans.app A).1 ≫ pbl₂GF ≫ pbg₂GF = pbqGF := by
    simpa [A₂, pbl₂GF, pbg₂GF, pbqGF] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := G F) (f := g i₂) (g := f₂) (gf := q) (hgf := hf₂) A
  have hA₁ : (A₁.inv.toNatTrans.app A).1 ≫ pbqGF = pbl₁GF ≫ pbg₁GF := by
    simpa [A₁, pbl₁GF, pbg₁GF, pbqGF] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := G F) (f := g i₁) (g := f₁) (gf := q) (hgf := hf₁) A
  change (e₁.inv ≫
      (inherited_source_fiber_forget (F := F) Z).map
        (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A) ≫
      e₂.hom).1 ≫ pbl₂X ≫ pbg₂GF =
    pbl₁X ≫ pbg₁GF
  have hforget :
      ((inherited_source_fiber_forget (F := F) Z).map
        (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A)).1 =
        (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 := by
    rfl
  have hmidval :
      (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 =
        (A₁.inv.toNatTrans.app A).1 ≫ (A₂.hom.toNatTrans.app A).1 := by
    rfl
  have hcompval :
      (e₁.inv ≫
        (inherited_source_fiber_forget (F := F) Z).map
          (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A) ≫
        e₂.hom).1 =
      e₁.inv.1 ≫
        ((inherited_source_fiber_forget (F := F) Z).map
          (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A)).1 ≫
        e₂.hom.1 := by
    rfl
  calc
    (e₁.inv ≫
        (inherited_source_fiber_forget (F := F) Z).map
          (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A) ≫
        e₂.hom).1 ≫ pbl₂X ≫ pbg₂GF =
      e₁.inv.1 ≫
        ((inherited_source_fiber_forget (F := F) Z).map
          (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A)).1 ≫
          e₂.hom.1 ≫ pbl₂X ≫ pbg₂GF := by
        rw [hcompval]
        simp only [Category.assoc]
    _ =
      e₁.inv.1 ≫
        (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 ≫
          e₂.hom.1 ≫ pbl₂X ≫ pbg₂GF := by
        rw [hforget]
        rfl
    _ = e₁.inv.1 ≫
        (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 ≫
          pbl₂GF ≫ pbg₂GF := by
        calc
          e₁.inv.1 ≫
              (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 ≫
                e₂.hom.1 ≫ pbl₂X ≫ pbg₂GF =
            e₁.inv.1 ≫
              (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 ≫
                (e₂.hom.1 ≫ pbl₂X) ≫ pbg₂GF := by
              simp only [Category.assoc]
          _ = e₁.inv.1 ≫
              (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 ≫
                pbl₂GF ≫ pbg₂GF := by
              exact congrArg
                (fun t ↦ e₁.inv.1 ≫
                  (A₁.inv.toNatTrans.app A ≫ A₂.hom.toNatTrans.app A).1 ≫ t ≫ pbg₂GF) he₂
    _ = e₁.inv.1 ≫
        (A₁.inv.toNatTrans.app A).1 ≫
          ((A₂.hom.toNatTrans.app A).1 ≫ pbl₂GF ≫ pbg₂GF) := by
        rw [hmidval]
        simp only [← Category.assoc]
        rw [Category.assoc e₁.inv.1 (A₁.inv.toNatTrans.app A).1
          (A₂.hom.toNatTrans.app A).1]
        rfl
    _ = e₁.inv.1 ≫ (A₁.inv.toNatTrans.app A).1 ≫ pbqGF := by
        exact congrArg
          (fun t ↦ e₁.inv.1 ≫ (A₁.inv.toNatTrans.app A).1 ≫ t) hA₂
    _ = e₁.inv.1 ≫ ((A₁.inv.toNatTrans.app A).1 ≫ pbqGF) := by
        simp only [Category.assoc]
    _ = e₁.inv.1 ≫ (pbl₁GF ≫ pbg₁GF) := by
        exact congrArg (fun t ↦ e₁.inv.1 ≫ t) hA₁
    _ = (e₁.inv.1 ≫ pbl₁GF) ≫ pbg₁GF := by
        simp only [Category.assoc]
    _ = pbl₁X ≫ pbg₁GF := by
        exact congrArg (fun t ↦ t ≫ pbg₁GF) he₁

/-- Helper for Lemma 8.10.5: the forgotten source overlap map for a fixed object of `G F`
agrees with the simple literal-base overlap morphism. -/
theorem inherited_basis_simple_ofObj_source_overlap_comm
    (F : Xₛ ⟶ Yₛ) [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (A : (G F).Fiber y)
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
        (inherited_source_pullback_comparison (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A).hom) ≫
      (((canonicalFiberPseudofunctor Xₛ.p).toDescentData (fun i ↦ Yₛ.p.map (g i))).obj
        ((inherited_source_fiber_forget (F := F) y).obj A)).hom q f₁ f₂ hf₁ hf₂ =
    inherited_basis_simple_forget_to_source_descent_hom (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
      (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A) q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
        (inherited_source_pullback_comparison (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A).hom) := by
  let sourceA : Xₛ.p.Fiber (Yₛ.p.obj y) := inherited_source_fiber_obj (F := F) A
  let D := (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A)
  let simple_g1 := inherited_source_fiber_obj (F := F) (D.obj i₁)
  let simple_g2 := inherited_source_fiber_obj (F := F) (D.obj i₂)
  let pull_g1 :=
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i₁)).op.toLoc).toFunctor.obj sourceA)
  let pull_g2 :=
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj sourceA)
  let simple_fg1 := (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj simple_g1)
  let pull_fg2 := (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj pull_g2)
  let tail : pull_fg2.1 ⟶ sourceA.1 :=
    (canonicalPullbackChoice Xₛ.p).map f₂ pull_g2 ≫
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA
  have htail : Xₛ.p.IsStronglyCartesian q tail := by
    have h1 : Xₛ.p.IsStronglyCartesian f₂ ((canonicalPullbackChoice Xₛ.p).map f₂ pull_g2) := by
      simpa [pull_g2] using (canonicalPullbackChoice Xₛ.p).isStronglyCartesian f₂ pull_g2
    have h2 : Xₛ.p.IsStronglyCartesian (Yₛ.p.map (g i₂))
        ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA) := by
      simpa [sourceA] using (canonicalPullbackChoice Xₛ.p).isStronglyCartesian
        (Yₛ.p.map (g i₂)) sourceA
    have hcomp : Xₛ.p.IsStronglyCartesian (f₂ ≫ Yₛ.p.map (g i₂))
        (((canonicalPullbackChoice Xₛ.p).map f₂ pull_g2) ≫
          ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA)) := by
      exact @Functor.IsStronglyCartesian.comp C Xₛ.S _ _ Xₛ.p
        Z (Yₛ.p.obj (Y i₂)) (Yₛ.p.obj y)
        pull_fg2.1 pull_g2.1 sourceA.1
        f₂ (Yₛ.p.map (g i₂))
        ((canonicalPullbackChoice Xₛ.p).map f₂ pull_g2)
        ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA)
        h1 h2
    simpa [tail, hf₂] using hcomp
  apply Functor.Fiber.hom_ext
  let lhsFiber : simple_fg1 ⟶ pull_fg2 :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
        (inherited_source_pullback_comparison (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A).hom) ≫
      (((canonicalFiberPseudofunctor Xₛ.p).toDescentData (fun i ↦ Yₛ.p.map (g i))).obj sourceA).hom q f₁ f₂ hf₁ hf₂
  let rhsFiber : simple_fg1 ⟶ pull_fg2 :=
    inherited_basis_simple_forget_to_source_descent_hom (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
      D q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
        (inherited_source_pullback_comparison (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A).hom)
  change lhsFiber.1 = rhsFiber.1
  letI : Xₛ.p.IsStronglyCartesian q tail := htail
  letI : Xₛ.p.IsHomLift (𝟙 Z) lhsFiber.1 := lhsFiber.2
  letI : Xₛ.p.IsHomLift (𝟙 Z) rhsFiber.1 := rhsFiber.2
  let common : simple_fg1.1 ⟶ sourceA.1 :=
    (canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 ≫
      (canonicalPullbackChoice (G F)).map (g i₁) A
  have hLHS : lhsFiber.1 ≫ tail = common := by
    let e1 := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A
    let A1 := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
      (Yₛ.p.map (g i₁)).op.toLoc f₁.op.toLoc q.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) hf₁)
    let A2 := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
      (Yₛ.p.map (g i₂)).op.toLoc f₂.op.toLoc q.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) hf₂)
    have hA2 : (A2.hom.toNatTrans.app sourceA).1 ≫ tail =
        (canonicalPullbackChoice Xₛ.p).map q sourceA := by
      simpa [A2, tail, pull_g2] using
        FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (p := Xₛ.p) (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) (hgf := hf₂)
          sourceA
    have hA1 : (A1.inv.toNatTrans.app sourceA).1 ≫
        (canonicalPullbackChoice Xₛ.p).map q sourceA =
        (canonicalPullbackChoice Xₛ.p).map f₁ pull_g1 ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA := by
      simpa [A1, pull_g1] using
        FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
          (p := Xₛ.p) (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) (hgf := hf₁)
          sourceA
    have hmap_e :
        (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
          (canonicalPullbackChoice Xₛ.p).map f₁ pull_g1 =
        (canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 ≫ e1.hom.1 := by
      simpa [e1, simple_g1, pull_g1] using
        canonical_pullbackFunctor_map_fac_owner
          (p := Xₛ.p) (f := f₁) (φ := e1.hom)
    have he1 : e1.hom.1 ≫
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA =
        (canonicalPullbackChoice (G F)).map (g i₁) A := by
      simpa [e1, sourceA] using
        inherited_source_pullback_comparison_hom_postcompose
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A
    have hlast :
        (canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 ≫
            (e1.hom.1 ≫ (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA) =
          common := by
      simpa only [common, Category.assoc] using
        congrArg
          (fun t ↦ (canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 ≫ t) he1
    have hcalc :
        (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
            (A1.inv.toNatTrans.app sourceA).1 ≫ (A2.hom.toNatTrans.app sourceA).1 ≫ tail =
          common := by
      have hcalcPre :
          (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
              (A1.inv.toNatTrans.app sourceA).1 ≫
                (A2.hom.toNatTrans.app sourceA).1 ≫ tail =
            (canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 ≫
              (e1.hom.1 ≫
                (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA) := by
        calc
          (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
              (A1.inv.toNatTrans.app sourceA).1 ≫
                (A2.hom.toNatTrans.app sourceA).1 ≫ tail =
            (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
              (A1.inv.toNatTrans.app sourceA).1 ≫
                ((A2.hom.toNatTrans.app sourceA).1 ≫ tail) := by
              simp only [Category.assoc]
          _ = (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
              (A1.inv.toNatTrans.app sourceA).1 ≫
                (canonicalPullbackChoice Xₛ.p).map q sourceA := by
              rw [hA2]
          _ = (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
              ((A1.inv.toNatTrans.app sourceA).1 ≫
                (canonicalPullbackChoice Xₛ.p).map q sourceA) := by
              simp only [Category.assoc]
          _ = (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
              ((canonicalPullbackChoice Xₛ.p).map f₁ pull_g1 ≫
                (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA) := by
              exact congrArg
                (fun t ↦
                  (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫ t)
                hA1
          _ = ((((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
              (canonicalPullbackChoice Xₛ.p).map f₁ pull_g1) ≫
              (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA := by
              simp only [Category.assoc]
          _ = ((canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 ≫ e1.hom.1) ≫
              (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA := by
              exact congrArg
                (fun t ↦ t ≫ (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA)
                hmap_e
          _ = (canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 ≫
              (e1.hom.1 ≫
                (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) sourceA) := by
              simp only [Category.assoc]
      exact hcalcPre.trans hlast
    change (((((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom) ≫
        ((((canonicalFiberPseudofunctor Xₛ.p).mapComp'
          (Yₛ.p.map (g i₁)).op.toLoc f₁.op.toLoc q.op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) hf₁)).inv.toNatTrans.app
            sourceA) ≫
        (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
          (Yₛ.p.map (g i₂)).op.toLoc f₂.op.toLoc q.op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) hf₂)).hom.toNatTrans.app
            sourceA))).1 ≫ tail = common)
    have hpack :
        (((((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom) ≫
          (A1.inv.toNatTrans.app sourceA ≫ A2.hom.toNatTrans.app sourceA)).1) =
        (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
          ((A1.inv.toNatTrans.app sourceA).1 ≫ (A2.hom.toNatTrans.app sourceA).1) := by
      rfl
    calc
      (((((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom) ≫
          (A1.inv.toNatTrans.app sourceA ≫ A2.hom.toNatTrans.app sourceA)).1) ≫ tail =
        ((((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
          ((A1.inv.toNatTrans.app sourceA).1 ≫ (A2.hom.toNatTrans.app sourceA).1)) ≫ tail := by
          rw [hpack]
      _ =
        (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map e1.hom).1 ≫
          (A1.inv.toNatTrans.app sourceA).1 ≫ (A2.hom.toNatTrans.app sourceA).1 ≫ tail := by
          simp only [Category.assoc]
      _ = common := hcalc
  have hRHS : rhsFiber.1 ≫ tail = common := by
    let e2 := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A
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
    let A1 := ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      (Yₛ.p.map l₁).op.toLoc cInv.op.toLoc f₁.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map l₁) (g := cInv) (gf := f₁) hc₁)).hom.toNatTrans.app
        simple_g1
    let A2 := ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      (Yₛ.p.map l₂).op.toLoc cInv.op.toLoc f₂.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map l₂) (g := cInv) (gf := f₂) hc₂)).inv.toNatTrans.app
        simple_g2
    let T := ((canonicalFiberPseudofunctor Xₛ.p).map cInv.op.toLoc).toFunctor
    let pb₂ := (canonicalPullbackChoice Xₛ.p).map f₂ simple_g2
    let pbl₁ := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map l₁) simple_g1
    let pbl₂ := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map l₂) simple_g2
    let pbc₁ := (canonicalPullbackChoice Xₛ.p).map cInv
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map l₁).op.toLoc).toFunctor.obj simple_g1)
    let pbc₂ := (canonicalPullbackChoice Xₛ.p).map cInv
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map l₂).op.toLoc).toFunctor.obj simple_g2)
    let pbg₂ := (canonicalPullbackChoice (G F)).map (g i₂) A
    let pbg₁ := (canonicalPullbackChoice (G F)).map (g i₁) A
    have hmap_e2 :
        (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map e2.hom).1 ≫
          (canonicalPullbackChoice Xₛ.p).map f₂ pull_g2 =
        pb₂ ≫ e2.hom.1 := by
      simpa [e2, pb₂, simple_g2, pull_g2] using
        canonical_pullbackFunctor_map_fac_owner
          (p := Xₛ.p) (f := f₂) (φ := e2.hom)
    have he2 : e2.hom.1 ≫
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA =
        pbg₂ := by
      simpa [e2, sourceA, pbg₂] using
        inherited_source_pullback_comparison_hom_postcompose
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A
    have hA2 : A2.1 ≫ pb₂ = pbc₂ ≫ pbl₂ := by
      simpa [A2, pb₂, pbc₂, pbl₂] using
        FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
          (p := Xₛ.p) (f := Yₛ.p.map l₂) (g := cInv) (gf := f₂) (hgf := hc₂)
          simple_g2
    have hT : (T.map d).1 ≫ pbc₂ = pbc₁ ≫ d.1 := by
      simpa [T, d, pbc₁, pbc₂] using
        canonical_pullbackFunctor_map_fac_owner
          (p := Xₛ.p) (f := cInv) (φ := d)
    have hd :
        d.1 ≫ pbl₂ ≫ pbg₂ = pbl₁ ≫ pbg₁ := by
      simpa [D, d, qUp, l₁, l₂, pbl₁, pbl₂, pbg₁, pbg₂] using
        inherited_basis_ofObj_descent_hom_source_postcompose
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F A qUp.hom l₁ l₂
          (inherited_basis_target_slice_inverse_leg_w
            (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
          (inherited_basis_target_slice_inverse_leg_w
            (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
    have hA1 : A1.1 ≫ pbc₁ ≫ pbl₁ =
        (canonicalPullbackChoice Xₛ.p).map f₁ simple_g1 := by
      simpa [A1, pbc₁, pbl₁] using
        FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (p := Xₛ.p) (f := Yₛ.p.map l₁) (g := cInv) (gf := f₁) (hgf := hc₁)
          simple_g1
    change (inherited_basis_simple_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map e2.hom)).1 ≫
        tail = common
    rw [inherited_basis_simple_forget_to_source_descent_hom,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    let mE := (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map e2.hom)
    let g2tail := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA
    have hmap_e2_assoc :
        A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ mE.1 ≫
            (canonicalPullbackChoice Xₛ.p).map f₂ pull_g2 ≫ g2tail =
          A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ pb₂ ≫ e2.hom.1 ≫ g2tail := by
      calc
        A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ mE.1 ≫
            (canonicalPullbackChoice Xₛ.p).map f₂ pull_g2 ≫ g2tail =
          A1.1 ≫ (T.map d).1 ≫ A2.1 ≫
            (mE.1 ≫ (canonicalPullbackChoice Xₛ.p).map f₂ pull_g2) ≫ g2tail := by
            simp only [Category.assoc]
        _ = A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ (pb₂ ≫ e2.hom.1) ≫ g2tail := by
            exact congrArg
              (fun t ↦ A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ t ≫ g2tail)
              (by simpa [mE] using hmap_e2)
        _ = A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ pb₂ ≫ e2.hom.1 ≫ g2tail := by
            simp only [Category.assoc]
    change ((A1 ≫ T.map d ≫ A2) ≫
        mE).1 ≫
        tail = common
    have hpackR :
        (((A1 ≫ T.map d ≫ A2) ≫ mE).1) =
          ((A1.1 ≫ (T.map d).1 ≫ A2.1) ≫ mE.1) := by
      rfl
    have hmain :
        ((A1 ≫ T.map d ≫ A2) ≫ mE).1 ≫ tail =
          A1.1 ≫ (T.map d).1 ≫ (pbc₂ ≫ pbl₂) ≫ pbg₂ := by
      calc
        ((A1 ≫ T.map d ≫ A2) ≫
            mE).1 ≫
            tail =
          A1.1 ≫ (T.map d).1 ≫ A2.1 ≫
            mE.1 ≫
              (canonicalPullbackChoice Xₛ.p).map f₂ pull_g2 ≫
                (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA := by
          rw [hpackR]
          dsimp [tail]
          simp only [Category.assoc]
        _ = A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ pb₂ ≫ e2.hom.1 ≫
                (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) sourceA := by
          simpa [g2tail] using hmap_e2_assoc
        _ = A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ pb₂ ≫ pbg₂ := by
          simpa only [Category.assoc] using
            congrArg
              (fun t ↦ A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ pb₂ ≫ t) he2
        _ = A1.1 ≫ (T.map d).1 ≫ (pbc₂ ≫ pbl₂) ≫ pbg₂ := by
          calc
            A1.1 ≫ (T.map d).1 ≫ A2.1 ≫ pb₂ ≫ pbg₂ =
              A1.1 ≫ (T.map d).1 ≫ (A2.1 ≫ pb₂) ≫ pbg₂ := by
                simp only [Category.assoc]
            _ = A1.1 ≫ (T.map d).1 ≫ (pbc₂ ≫ pbl₂) ≫ pbg₂ := by
                exact congrArg (fun t ↦ A1.1 ≫ (T.map d).1 ≫ t ≫ pbg₂) hA2
    have hfinal :
        A1.1 ≫ (T.map d).1 ≫ (pbc₂ ≫ pbl₂) ≫ pbg₂ = common := by
      calc
        A1.1 ≫ (T.map d).1 ≫ (pbc₂ ≫ pbl₂) ≫ pbg₂ =
            A1.1 ≫ (T.map d).1 ≫ pbc₂ ≫ pbl₂ ≫ pbg₂ := by
          simp only [Category.assoc]
        _ =
          A1.1 ≫ ((T.map d).1 ≫ pbc₂) ≫ pbl₂ ≫ pbg₂ := by
            simp only [Category.assoc]
        _ = A1.1 ≫ (pbc₁ ≫ d.1) ≫ pbl₂ ≫ pbg₂ := by
            exact congrArg (fun t ↦ A1.1 ≫ t ≫ pbl₂ ≫ pbg₂) hT
        _ =
            A1.1 ≫ pbc₁ ≫ d.1 ≫ pbl₂ ≫ pbg₂ := by
          simp only [Category.assoc]
        _ = A1.1 ≫ pbc₁ ≫ pbl₁ ≫ pbg₁ := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ A1.1 ≫ pbc₁ ≫ t) hd
        _ = common := by
          have hlast :
              (A1.1 ≫ pbc₁ ≫ pbl₁) ≫ pbg₁ = common := by
            exact (congrArg (fun t ↦ t ≫ pbg₁) hA1).trans (by rfl)
          simpa only [Category.assoc] using hlast
    exact hmain.trans hfinal
  exact Functor.IsStronglyCartesian.ext Xₛ.p q tail (𝟙 Z) (by
    rw [hLHS, hRHS])

/-- Helper for Lemma 8.10.5: conjugating a morphism of `G F` descent data through the forgotten
source overlap maps preserves the literal-base overlap compatibility. -/
theorem inherited_basis_conjugated_ofObj_source_overlap_comm
    (F : Xₛ ⟶ Yₛ) [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    {A B : (G F).Fiber y}
    (φ :
      (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A) ⟶
        (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj B))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
        (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A).inv) ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁))) ≫
        (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) B).hom) ≫
          (((canonicalFiberPseudofunctor Xₛ.p).toDescentData
              (fun i ↦ Yₛ.p.map (g i))).obj
            ((inherited_source_fiber_forget (F := F) y).obj B)).hom
              q f₁ f₂ hf₁ hf₂ =
    ((((canonicalFiberPseudofunctor Xₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i))).obj
      ((inherited_source_fiber_forget (F := F) y).obj A)).hom
        q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
        (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A).inv) ≫
        (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂))) ≫
          (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
            (inherited_source_pullback_comparison
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) B).hom) := by
  let sourceA : Xₛ.p.Fiber (Yₛ.p.obj y) := inherited_source_fiber_obj (F := F) A
  let sourceB : Xₛ.p.Fiber (Yₛ.p.obj y) := inherited_source_fiber_obj (F := F) B
  let eA₁ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A
  let eA₂ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A
  let eB₁ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) B
  let eB₂ := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) B
  let T₁ := ((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor
  let T₂ := ((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor
  let canA :=
    ((((canonicalFiberPseudofunctor Xₛ.p).toDescentData
      (fun i ↦ Yₛ.p.map (g i))).obj sourceA).hom q f₁ f₂ hf₁ hf₂)
  let canB :=
    ((((canonicalFiberPseudofunctor Xₛ.p).toDescentData
      (fun i ↦ Yₛ.p.map (g i))).obj sourceB).hom q f₁ f₂ hf₁ hf₂)
  let simpleA :=
    inherited_basis_simple_forget_to_source_descent_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
      (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A)
      q f₁ f₂ hf₁ hf₂
  let simpleB :=
    inherited_basis_simple_forget_to_source_descent_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
      (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj B)
      q f₁ f₂ hf₁ hf₂
  let φ₁ := (inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁)
  let φ₂ := (inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂)
  have hA :
      T₁.map eA₁.hom ≫ canA = simpleA ≫ T₂.map eA₂.hom := by
    simpa [sourceA, eA₁, eA₂, canA, simpleA, T₁, T₂] using
      inherited_basis_simple_ofObj_source_overlap_comm
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F A q f₁ f₂ hf₁ hf₂
  have hB :
      T₁.map eB₁.hom ≫ canB = simpleB ≫ T₂.map eB₂.hom := by
    simpa [sourceB, eB₁, eB₂, canB, simpleB, T₁, T₂] using
      inherited_basis_simple_ofObj_source_overlap_comm
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F B q f₁ f₂ hf₁ hf₂
  have hsimple :
      T₁.map φ₁ ≫ simpleB = simpleA ≫ T₂.map φ₂ := by
    simpa [simpleA, simpleB, φ₁, φ₂, T₁, T₂] using
      inherited_basis_simple_forget_to_source_descent_hom_comm
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) φ q f₁ f₂ hf₁ hf₂
  have hAinv :
      T₁.map eA₁.inv ≫ simpleA = canA ≫ T₂.map eA₂.inv := by
    apply (cancel_mono (T₂.map eA₂.hom)).1
    have hcancel₁ : T₁.map eA₁.inv ≫ T₁.map eA₁.hom = 𝟙 _ := by
      simpa [Functor.map_comp] using congrArg (fun t ↦ T₁.map t) eA₁.inv_hom_id
    have hcancel₂ : T₂.map eA₂.inv ≫ T₂.map eA₂.hom = 𝟙 _ := by
      simpa [Functor.map_comp] using congrArg (fun t ↦ T₂.map t) eA₂.inv_hom_id
    have hleft :
        (T₁.map eA₁.inv ≫ simpleA) ≫ T₂.map eA₂.hom = canA := by
      have hpre :
          (T₁.map eA₁.inv ≫ simpleA) ≫ T₂.map eA₂.hom =
            (T₁.map eA₁.inv ≫ T₁.map eA₁.hom) ≫ canA := by
        calc
          (T₁.map eA₁.inv ≫ simpleA) ≫ T₂.map eA₂.hom =
              T₁.map eA₁.inv ≫ (simpleA ≫ T₂.map eA₂.hom) := by
                simp only [Category.assoc]
          _ = T₁.map eA₁.inv ≫ (T₁.map eA₁.hom ≫ canA) := by
                exact congrArg (fun t ↦ T₁.map eA₁.inv ≫ t) hA.symm
          _ = (T₁.map eA₁.inv ≫ T₁.map eA₁.hom) ≫ canA := by
                simp only [Category.assoc]
      exact hpre.trans
        ((congrArg (fun t ↦ t ≫ canA) hcancel₁).trans (Category.id_comp canA))
    have hright :
        (canA ≫ T₂.map eA₂.inv) ≫ T₂.map eA₂.hom = canA := by
      calc
        (canA ≫ T₂.map eA₂.inv) ≫ T₂.map eA₂.hom =
            canA ≫ (T₂.map eA₂.inv ≫ T₂.map eA₂.hom) := by
              simp only [Category.assoc]
        _ = canA := by
              exact (congrArg (fun t ↦ canA ≫ t) hcancel₂).trans (Category.comp_id canA)
    exact hleft.trans hright.symm
  have hpre :
      T₁.map eA₁.inv ≫ T₁.map φ₁ ≫ T₁.map eB₁.hom ≫ canB =
        (T₁.map eA₁.inv ≫ simpleA) ≫ T₂.map φ₂ ≫ T₂.map eB₂.hom := by
    calc
      T₁.map eA₁.inv ≫ T₁.map φ₁ ≫ T₁.map eB₁.hom ≫ canB =
          T₁.map eA₁.inv ≫ T₁.map φ₁ ≫ (T₁.map eB₁.hom ≫ canB) := by
            simp only [Category.assoc]
      _ = T₁.map eA₁.inv ≫ T₁.map φ₁ ≫ (simpleB ≫ T₂.map eB₂.hom) := by
            exact congrArg (fun t ↦ T₁.map eA₁.inv ≫ T₁.map φ₁ ≫ t) hB
      _ = T₁.map eA₁.inv ≫ (T₁.map φ₁ ≫ simpleB) ≫ T₂.map eB₂.hom := by
            simp only [Category.assoc]
      _ = T₁.map eA₁.inv ≫ (simpleA ≫ T₂.map φ₂) ≫ T₂.map eB₂.hom := by
            exact congrArg (fun t ↦ T₁.map eA₁.inv ≫ t ≫ T₂.map eB₂.hom) hsimple
      _ = (T₁.map eA₁.inv ≫ simpleA) ≫ T₂.map φ₂ ≫ T₂.map eB₂.hom := by
            simp only [Category.assoc]
  have hpost :
      (T₁.map eA₁.inv ≫ simpleA) ≫ T₂.map φ₂ ≫ T₂.map eB₂.hom =
        (canA ≫ T₂.map eA₂.inv) ≫ T₂.map φ₂ ≫ T₂.map eB₂.hom := by
    exact
      congrArg (fun t ↦ t ≫ T₂.map φ₂ ≫ T₂.map eB₂.hom) hAinv
  simpa only [Category.assoc] using hpre.trans hpost

/- Route correction: target descent compatibility should be checked after postcomposing with the
cartesian comparison arrow over the overlap.  This avoids reopening the full `TY.preimageIso`
transport when comparing vertical morphisms in a target fiber. -/
/-- Helper for Lemma 8.10.5: the canonical target descent overlap postcomposes to the literal
first pullback tail. -/
theorem canonical_target_descent_hom_postcompose
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    let TY := ((canonicalFiberPseudofunctor Yₛ.p).toDescentData
      (fun i ↦ Yₛ.p.map (g i)))
    let yBase : Yₛ.p.Fiber (Yₛ.p.obj y) := Functor.Fiber.mk (a := y) rfl
    let yPull₁ := (((canonicalFiberPseudofunctor Yₛ.p).map
      (Yₛ.p.map (g i₁)).op.toLoc).toFunctor.obj yBase)
    let yPull₂ := (((canonicalFiberPseudofunctor Yₛ.p).map
      (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj yBase)
    ((TY.obj yBase).hom q f₁ f₂ hf₁ hf₂).1 ≫
        ((canonicalPullbackChoice Yₛ.p).map f₂ yPull₂ ≫
          (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase) =
      (canonicalPullbackChoice Yₛ.p).map f₁ yPull₁ ≫
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yBase := by
  -- The canonical descent hom is an inverse composition comparison followed by a forward one;
  -- each comparison has a named postcomposition formula.
  intro TY yBase yPull₁ yPull₂
  let A₁ := ((canonicalFiberPseudofunctor Yₛ.p).mapComp'
    (Yₛ.p.map (g i₁)).op.toLoc f₁.op.toLoc q.op.toLoc
    (base_comp_toLoc_eq (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) hf₁)).inv.toNatTrans.app yBase
  let A₂ := ((canonicalFiberPseudofunctor Yₛ.p).mapComp'
    (Yₛ.p.map (g i₂)).op.toLoc f₂.op.toLoc q.op.toLoc
    (base_comp_toLoc_eq (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) hf₂)).hom.toNatTrans.app yBase
  have hA₂ : A₂.1 ≫
      (canonicalPullbackChoice Yₛ.p).map f₂ yPull₂ ≫
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase =
      (canonicalPullbackChoice Yₛ.p).map q yBase := by
    simpa [A₂, yPull₂] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := Yₛ.p) (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) (hgf := hf₂) yBase
  have hA₁ : A₁.1 ≫ (canonicalPullbackChoice Yₛ.p).map q yBase =
      (canonicalPullbackChoice Yₛ.p).map f₁ yPull₁ ≫
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yBase := by
    simpa [A₁, yPull₁] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := Yₛ.p) (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) (hgf := hf₁) yBase
  change (A₁.1 ≫ A₂.1) ≫
      ((canonicalPullbackChoice Yₛ.p).map f₂ yPull₂ ≫
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase) =
    (canonicalPullbackChoice Yₛ.p).map f₁ yPull₁ ≫
      (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yBase
  calc
    (A₁.1 ≫ A₂.1) ≫
        ((canonicalPullbackChoice Yₛ.p).map f₂ yPull₂ ≫
          (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase) =
        A₁.1 ≫ (A₂.1 ≫
          (canonicalPullbackChoice Yₛ.p).map f₂ yPull₂ ≫
            (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase) := by
          simp only [Category.assoc]
    _ = A₁.1 ≫ (canonicalPullbackChoice Yₛ.p).map q yBase := by
          rw [hA₂]
    _ = (canonicalPullbackChoice Yₛ.p).map f₁ yPull₁ ≫
          (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yBase := hA₁

end

end CategoryTheory
