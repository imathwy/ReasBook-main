import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.TargetPathTransport


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

/-- Helper for Lemma 8.10.5: the target overlap transport of `F x`, followed by the two
pullback-comparison maps, is the same as first using the left pullback-comparison shell and then
applying `F` to the corresponding source overlap transport. -/
theorem inherited_basis_target_pullbackComparison_prefix
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (x : Xₛ.p.Fiber (Yₛ.p.obj y))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    let H := StackInGroupoidsOver.Hom.toFibredCategoryMor F
    let x₁ :=
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i₁)).op.toLoc).toFunctor.obj x)
    let x₂ :=
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj x)
    let A₁X := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
      (Yₛ.p.map (g i₁)).op.toLoc f₁.op.toLoc q.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) hf₁)
    let A₂X := (canonicalFiberPseudofunctor Xₛ.p).mapComp'
      (Yₛ.p.map (g i₂)).op.toLoc f₂.op.toLoc q.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) hf₂)
    let A₁Y := (canonicalFiberPseudofunctor Yₛ.p).mapComp'
      (Yₛ.p.map (g i₁)).op.toLoc f₁.op.toLoc q.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) hf₁)
    let A₂Y := (canonicalFiberPseudofunctor Yₛ.p).mapComp'
      (Yₛ.p.map (g i₂)).op.toLoc f₂.op.toLoc q.op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) hf₂)
    ((A₁Y.inv.toNatTrans.app ((fiberFunctor F (Yₛ.p.obj y)).obj x)) ≫
        (A₂Y.hom.toNatTrans.app ((fiberFunctor F (Yₛ.p.obj y)).obj x)) ≫
        (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i₂)) x).hom) ≫
        (FibredCategoryMor.pullbackComparison H f₂ x₂).hom) =
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i₁)) x).hom) ≫
        (FibredCategoryMor.pullbackComparison H f₁ x₁).hom ≫
        (fiberFunctor F Z).map (A₁X.inv.toNatTrans.app x ≫ A₂X.hom.toNatTrans.app x)) := by
  intro H x₁ x₂ A₁X A₂X A₁Y A₂Y
  apply Functor.Fiber.hom_ext
  let FY := fiberFunctor F (Yₛ.p.obj y)
  let FZ := fiberFunctor F Z
  let Fx := FY.obj x
  let pcg₁ := FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i₁)) x
  let pcg₂ := FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i₂)) x
  let pcf₁ := FibredCategoryMor.pullbackComparison H f₁ x₁
  let pcf₂ := FibredCategoryMor.pullbackComparison H f₂ x₂
  let sourceCan := A₁X.inv.toNatTrans.app x ≫ A₂X.hom.toNatTrans.app x
  let pbg₂X := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₂)) x
  let pbf₂X := (canonicalPullbackChoice Xₛ.p).map f₂ x₂
  let x₂f := (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj x₂)
  let sourceTail₂ := pbf₂X ≫ pbg₂X
  let targetTail₂ := H.toHom.map sourceTail₂
  have htailX₂ : Xₛ.p.IsStronglyCartesian q sourceTail₂ := by
    have h₁ : Xₛ.p.IsStronglyCartesian f₂ pbf₂X := by
      simpa [pbf₂X, x₂] using
        (canonicalPullbackChoice Xₛ.p).isStronglyCartesian f₂ x₂
    have h₂ : Xₛ.p.IsStronglyCartesian (Yₛ.p.map (g i₂)) pbg₂X := by
      simpa [pbg₂X] using
        (canonicalPullbackChoice Xₛ.p).isStronglyCartesian (Yₛ.p.map (g i₂)) x
    letI : Xₛ.p.IsStronglyCartesian f₂ pbf₂X := h₁
    letI : Xₛ.p.IsStronglyCartesian (Yₛ.p.map (g i₂)) pbg₂X := h₂
    have hcomp : Xₛ.p.IsStronglyCartesian (f₂ ≫ Yₛ.p.map (g i₂)) sourceTail₂ := by
      dsimp [sourceTail₂]
      exact
        @Functor.IsStronglyCartesian.comp _ _ _ _ Xₛ.p
          (R := Z) (S := Yₛ.p.obj (Y i₂)) (T := Yₛ.p.obj y)
          (a := x₂f.1) (b := x₂.1) (c := x.1)
          (f := f₂) (g := Yₛ.p.map (g i₂))
          (φ := pbf₂X) (ψ := pbg₂X) h₁ h₂
    simpa [sourceTail₂, hf₂] using hcomp
  have htailY₂ : Yₛ.p.IsStronglyCartesian q targetTail₂ := by
    exact FibredCategoryMor.map_stronglyCartesian_of_lift H q sourceTail₂ htailX₂
  letI : Yₛ.p.IsStronglyCartesian q targetTail₂ := htailY₂
  let lhsFiber :=
    (A₁Y.inv.toNatTrans.app ((fiberFunctor F (Yₛ.p.obj y)).obj x)) ≫
      (A₂Y.hom.toNatTrans.app ((fiberFunctor F (Yₛ.p.obj y)).obj x)) ≫
      (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom) ≫
      pcf₂.hom
  let rhsFiber :=
    (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom) ≫
      pcf₁.hom ≫ (fiberFunctor F Z).map (A₁X.inv.toNatTrans.app x ≫ A₂X.hom.toNatTrans.app x)
  let lhsOwner := Functor.Fiber.fiberInclusion.map lhsFiber
  let rhsOwner := Functor.Fiber.fiberInclusion.map rhsFiber
  change Functor.Fiber.fiberInclusion.map lhsFiber =
    Functor.Fiber.fiberInclusion.map rhsFiber
  change lhsOwner = rhsOwner
  have hliftL : Yₛ.p.IsHomLift (𝟙 Z) lhsOwner := by
    change Yₛ.p.IsHomLift (𝟙 Z) lhsFiber.1
    exact lhsFiber.2
  have hliftR : Yₛ.p.IsHomLift (𝟙 Z) rhsOwner := by
    change Yₛ.p.IsHomLift (𝟙 Z) rhsFiber.1
    exact rhsFiber.2
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ Yₛ.p _ _ _ _
    q targetTail₂ htailY₂ _ _ (𝟙 Z) lhsOwner rhsOwner hliftL hliftR ?_
  let pbYg₂ := (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) Fx
  let pbYf₂ :=
    (canonicalPullbackChoice Yₛ.p).map f₂
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj Fx)
  let pbYg₁ := (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) Fx
  let pbYf₁ :=
    (canonicalPullbackChoice Yₛ.p).map f₁
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i₁)).op.toLoc).toFunctor.obj Fx)
  let pbYq := (canonicalPullbackChoice Yₛ.p).map q Fx
  let pbf₁X := (canonicalPullbackChoice Xₛ.p).map f₁ x₁
  let pbg₁X := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i₁)) x
  let pbqX := (canonicalPullbackChoice Xₛ.p).map q x
  have hpcf₂ :
      pcf₂.hom.1 ≫ H.toHom.map pbf₂X =
        (canonicalPullbackChoice Yₛ.p).map f₂
          ((fiberFunctor F (Yₛ.p.obj (Y i₂))).obj x₂) := by
    simpa only [pcf₂, pbf₂X, H] using
      FibredCategoryMor.pullbackComparison_hom_postcompose H f₂ x₂
  have hmap_pcg₂ :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₂
          ((fiberFunctor F (Yₛ.p.obj (Y i₂))).obj x₂) =
      pbYf₂ ≫ pcg₂.hom.1 := by
    simpa only [pcg₂, pbYf₂, Fx, x₂] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := f₂) (φ := pcg₂.hom)
  have hpcg₂ :
      pcg₂.hom.1 ≫ H.toHom.map pbg₂X = pbYg₂ := by
    simpa only [pcg₂, pbg₂X, pbYg₂, H, Fx] using
      FibredCategoryMor.pullbackComparison_hom_postcompose H (Yₛ.p.map (g i₂)) x
  have hA₂Y : (A₂Y.hom.toNatTrans.app Fx).1 ≫ pbYf₂ ≫ pbYg₂ = pbYq := by
    simpa [A₂Y, pbYf₂, pbYg₂, pbYq, Fx] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := Yₛ.p) (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) (hgf := hf₂)
        Fx
  have hA₁Y : (A₁Y.inv.toNatTrans.app Fx).1 ≫ pbYq = pbYf₁ ≫ pbYg₁ := by
    simpa [A₁Y, pbYf₁, pbYg₁, pbYq, Fx] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := Yₛ.p) (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) (hgf := hf₁)
        Fx
  have hpcf₁ :
      pcf₁.hom.1 ≫ H.toHom.map pbf₁X =
        (canonicalPullbackChoice Yₛ.p).map f₁
          ((fiberFunctor F (Yₛ.p.obj (Y i₁))).obj x₁) := by
    simpa only [pcf₁, pbf₁X, H] using
      FibredCategoryMor.pullbackComparison_hom_postcompose H f₁ x₁
  have hmap_pcg₁ :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom)).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₁
          ((fiberFunctor F (Yₛ.p.obj (Y i₁))).obj x₁) =
      pbYf₁ ≫ pcg₁.hom.1 := by
    simpa only [pcg₁, pbYf₁, Fx, x₁] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := f₁) (φ := pcg₁.hom)
  have hpcg₁ :
      pcg₁.hom.1 ≫ H.toHom.map pbg₁X = pbYg₁ := by
    simpa only [pcg₁, pbg₁X, pbYg₁, H, Fx] using
      FibredCategoryMor.pullbackComparison_hom_postcompose H (Yₛ.p.map (g i₁)) x
  have hA₂X : (A₂X.hom.toNatTrans.app x).1 ≫ pbf₂X ≫ pbg₂X = pbqX := by
    simpa [A₂X, pbf₂X, pbg₂X, pbqX] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := Xₛ.p) (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) (hgf := hf₂)
        x
  have hA₁X : (A₁X.inv.toNatTrans.app x).1 ≫ pbqX = pbf₁X ≫ pbg₁X := by
    simpa [A₁X, pbf₁X, pbg₁X, pbqX] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := Xₛ.p) (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) (hgf := hf₁)
        x
  have hsourceTail :
      (FZ.map sourceCan).1 ≫ targetTail₂ =
        H.toHom.map (pbf₁X ≫ pbg₁X) := by
    change H.toHom.map sourceCan.1 ≫ H.toHom.map sourceTail₂ =
      H.toHom.map (pbf₁X ≫ pbg₁X)
    rw [← H.toHom.map_comp]
    have hs : sourceCan.1 ≫ sourceTail₂ = pbf₁X ≫ pbg₁X := by
      change ((A₁X.inv.toNatTrans.app x).1 ≫ (A₂X.hom.toNatTrans.app x).1) ≫
          (pbf₂X ≫ pbg₂X) = pbf₁X ≫ pbg₁X
      calc
        ((A₁X.inv.toNatTrans.app x).1 ≫ (A₂X.hom.toNatTrans.app x).1) ≫
            (pbf₂X ≫ pbg₂X) =
          (A₁X.inv.toNatTrans.app x).1 ≫
            ((A₂X.hom.toNatTrans.app x).1 ≫ pbf₂X ≫ pbg₂X) := by
          simp only [Category.assoc]
        _ = (A₁X.inv.toNatTrans.app x).1 ≫ pbqX := by
          exact congrArg (fun t ↦ (A₁X.inv.toNatTrans.app x).1 ≫ t) hA₂X
        _ = pbf₁X ≫ pbg₁X := hA₁X
    rw [hs]
    rfl
  have htargetTail₂ : targetTail₂ = H.toHom.map pbf₂X ≫ H.toHom.map pbg₂X := by
    change H.toHom.map sourceTail₂ = H.toHom.map pbf₂X ≫ H.toHom.map pbg₂X
    change H.toHom.map (pbf₂X ≫ pbg₂X) = H.toHom.map pbf₂X ≫ H.toHom.map pbg₂X
    rw [H.toHom.map_comp]
  have hleftPost : lhsOwner ≫ targetTail₂ = pbYf₁ ≫ pbYg₁ := by
    change
      ((A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
          pcf₂.hom.1) ≫ targetTail₂ = pbYf₁ ≫ pbYg₁
    have hpre :
        ((A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
            ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
            pcf₂.hom.1) ≫ targetTail₂ =
          (A₁Y.inv.toNatTrans.app Fx).1 ≫ pbYq := by
      calc
      ((A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
          pcf₂.hom.1) ≫ targetTail₂
          =
        (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
          pcf₂.hom.1 ≫ H.toHom.map pbf₂X ≫ H.toHom.map pbg₂X := by
        rw [htargetTail₂]
        simp only [Category.assoc]
        rfl
      _ =
        (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
          (pcf₂.hom.1 ≫ H.toHom.map pbf₂X) ≫ H.toHom.map pbg₂X := by
        simp only [Category.assoc]
      _ =
        (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
          ((canonicalPullbackChoice Yₛ.p).map f₂
            ((fiberFunctor F (Yₛ.p.obj (Y i₂))).obj x₂)) ≫ H.toHom.map pbg₂X := by
        exact congrArg
          (fun t ↦ (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
            ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
            t ≫ H.toHom.map pbg₂X)
          hpcf₂
      _ =
        (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          (((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)).1 ≫
            ((canonicalPullbackChoice Yₛ.p).map f₂
              ((fiberFunctor F (Yₛ.p.obj (Y i₂))).obj x₂))) ≫ H.toHom.map pbg₂X := by
        simp only [Category.assoc]
      _ =
        (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          (pbYf₂ ≫ pcg₂.hom.1) ≫ H.toHom.map pbg₂X := by
        exact congrArg
          (fun t ↦ (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
            t ≫ H.toHom.map pbg₂X)
          hmap_pcg₂
      _ =
        (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          pbYf₂ ≫ pcg₂.hom.1 ≫ H.toHom.map pbg₂X := by
        simp only [Category.assoc]
      _ =
        (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
          pbYf₂ ≫ pbYg₂ := by
        simpa only [Category.assoc] using
          congrArg
            (fun t ↦ (A₁Y.inv.toNatTrans.app Fx).1 ≫ (A₂Y.hom.toNatTrans.app Fx).1 ≫
              pbYf₂ ≫ t)
            hpcg₂
      _ = (A₁Y.inv.toNatTrans.app Fx).1 ≫ pbYq := by
        simpa only [Category.assoc] using
          congrArg (fun t ↦ (A₁Y.inv.toNatTrans.app Fx).1 ≫ t) hA₂Y
    exact hpre.trans hA₁Y
  have hrightPost : rhsOwner ≫ targetTail₂ = pbYf₁ ≫ pbYg₁ := by
    change
      (((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom)).1 ≫
          pcf₁.hom.1 ≫ (FZ.map sourceCan).1) ≫ targetTail₂ =
        pbYf₁ ≫ pbYg₁
    have hpre :
        (((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom)).1 ≫
            pcf₁.hom.1 ≫ (FZ.map sourceCan).1) ≫ targetTail₂ =
          pbYf₁ ≫ (pcg₁.hom.1 ≫ H.toHom.map pbg₁X) := by
      calc
      (((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom)).1 ≫
          pcf₁.hom.1 ≫ (FZ.map sourceCan).1) ≫ targetTail₂ =
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
          pcf₁.hom.1) ≫ ((FZ.map sourceCan).1 ≫ targetTail₂) := by
        simp only [Category.assoc]
      _ =
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
          pcf₁.hom.1) ≫ H.toHom.map (pbf₁X ≫ pbg₁X) := by
        exact congrArg
          (fun t ↦
            ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
              pcf₁.hom.1) ≫ t)
          hsourceTail
      _ =
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
          pcf₁.hom.1) ≫ (H.toHom.map pbf₁X ≫ H.toHom.map pbg₁X) := by
        rw [H.toHom.map_comp]
        rfl
      _ =
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
          pcf₁.hom.1) ≫ H.toHom.map pbf₁X ≫ H.toHom.map pbg₁X := by
        simp only [Category.assoc]
      _ =
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
          (pcf₁.hom.1 ≫ H.toHom.map pbf₁X)) ≫ H.toHom.map pbg₁X := by
        simp only [Category.assoc]
      _ =
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
          ((canonicalPullbackChoice Yₛ.p).map f₁
            ((fiberFunctor F (Yₛ.p.obj (Y i₁))).obj x₁))) ≫ H.toHom.map pbg₁X := by
        exact congrArg
          (fun t ↦
            ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom).1 ≫
              t) ≫ H.toHom.map pbg₁X)
          hpcf₁
      _ = (pbYf₁ ≫ pcg₁.hom.1) ≫ H.toHom.map pbg₁X := by
        exact congrArg (fun t ↦ t ≫ H.toHom.map pbg₁X) hmap_pcg₁
      _ = pbYf₁ ≫ (pcg₁.hom.1 ≫ H.toHom.map pbg₁X) := by
        simp only [Category.assoc]
    exact hpre.trans (congrArg (fun t ↦ pbYf₁ ≫ t) hpcg₁)
  exact hleftPost.trans hrightPost.symm

/-- Helper for Lemma 8.10.5: after postcomposing with the chosen right target tail, the local
target identification and target-leg comparison on the left overlap reduce to the literal local
target arrow followed by the cover leg. -/
theorem inherited_basis_target_leg_tail_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    let yFiber : Yₛ.p.Fiber (Yₛ.p.obj y) := Functor.Fiber.mk (a := y) rfl
    let y₂Pull :=
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj
        yFiber)
    let tail₂a := (canonicalPullbackChoice Yₛ.p).map f₂ y₂Pull
    let tail₂b := (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yFiber
    let tail₂ := tail₂a ≫ tail₂b
    ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map
          (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)).hom) ≫
        (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map
          (inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (g i₁)).inv) ≫
        (((canonicalFiberPseudofunctor Yₛ.p).mapComp'
          (Yₛ.p.map (g i₁)).op.toLoc f₁.op.toLoc q.op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) hf₁)).inv.toNatTrans.app
            yFiber) ≫
        (((canonicalFiberPseudofunctor Yₛ.p).mapComp'
          (Yₛ.p.map (g i₂)).op.toLoc f₂.op.toLoc q.op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) hf₂)).hom.toNatTrans.app
            yFiber)).1 ≫ tail₂ =
      ((canonicalPullbackChoice Yₛ.p).map f₁
          ((fiberFunctor F (Yₛ.p.obj (Y i₁))).obj
            (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)).hom.1) ≫
        g i₁ := by
  intro yFiber y₂Pull tail₂a tail₂b tail₂
  let A₁ := (canonicalFiberPseudofunctor Yₛ.p).mapComp'
    (Yₛ.p.map (g i₁)).op.toLoc f₁.op.toLoc q.op.toLoc
    (base_comp_toLoc_eq (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) hf₁)
  let A₂ := (canonicalFiberPseudofunctor Yₛ.p).mapComp'
    (Yₛ.p.map (g i₂)).op.toLoc f₂.op.toLoc q.op.toLoc
    (base_comp_toLoc_eq (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) hf₂)
  let loc₁ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)
  let leg₁ := inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (g i₁)
  let y₁Pull :=
    (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i₁)).op.toLoc).toFunctor.obj
      yFiber)
  let local₁ : Yₛ.p.Fiber (Yₛ.p.obj (Y i₁)) := Functor.Fiber.mk (a := Y i₁) rfl
  have hA₂ : (A₂.hom.toNatTrans.app yFiber).1 ≫ tail₂ =
      (canonicalPullbackChoice Yₛ.p).map q yFiber := by
    simpa [A₂, y₂Pull, tail₂] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := Yₛ.p) (f := Yₛ.p.map (g i₂)) (g := f₂) (gf := q) (hgf := hf₂)
        yFiber
  have hA₁ : (A₁.inv.toNatTrans.app yFiber).1 ≫
      (canonicalPullbackChoice Yₛ.p).map q yFiber =
      (canonicalPullbackChoice Yₛ.p).map f₁ y₁Pull ≫
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yFiber := by
    simpa [A₁, y₁Pull] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := Yₛ.p) (f := Yₛ.p.map (g i₁)) (g := f₁) (gf := q) (hgf := hf₁)
        yFiber
  have hmap_leg :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv)).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₁ y₁Pull =
      (canonicalPullbackChoice Yₛ.p).map f₁ local₁ ≫ leg₁.inv.1 := by
    simpa [leg₁, y₁Pull, local₁] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := f₁) (φ := leg₁.inv)
  have hleg :
      leg₁.inv.1 ≫ (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yFiber =
        g i₁ := by
    simpa [leg₁, yFiber] using
      inherited_basis_target_pullback_leg_iso_symm_hom_postcompose
        (J := J) (Yₛ := Yₛ) (g i₁)
  have hmap_loc :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom)).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₁ local₁ =
      (canonicalPullbackChoice Yₛ.p).map f₁
          ((fiberFunctor F (Yₛ.p.obj (Y i₁))).obj
            (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫
        loc₁.hom.1 := by
    simpa [loc₁, local₁] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := f₁) (φ := loc₁.hom)
  have hfinal :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₁ local₁) ≫ g i₁ =
      ((canonicalPullbackChoice Yₛ.p).map f₁
          ((fiberFunctor F (Yₛ.p.obj (Y i₁))).obj
            (inherited_source_fiber_obj (F := F) (D.obj i₁))) ≫
        loc₁.hom.1) ≫ g i₁ := by
    exact congrArg (fun t ↦ t ≫ g i₁) hmap_loc
  have hpre :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom) ≫
        (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv) ≫
        A₁.inv.toNatTrans.app yFiber ≫ A₂.hom.toNatTrans.app yFiber).1 ≫ tail₂
      =
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₁ local₁) ≫ g i₁ := by
    calc
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom) ≫
          (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv) ≫
          A₁.inv.toNatTrans.app yFiber ≫ A₂.hom.toNatTrans.app yFiber).1 ≫ tail₂
        =
          ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
            (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv).1 ≫
            (A₁.inv.toNatTrans.app yFiber).1 ≫
            (A₂.hom.toNatTrans.app yFiber).1) ≫ tail₂ := by
        rfl
    _ =
      (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv).1 ≫
        (A₁.inv.toNatTrans.app yFiber).1 ≫
        ((canonicalPullbackChoice Yₛ.p).map q yFiber) := by
      simpa only [Category.assoc] using
        congrArg
          (fun t ↦
            (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
              (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv).1 ≫
              (A₁.inv.toNatTrans.app yFiber).1 ≫ t)
          hA₂
    _ =
      (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv).1 ≫
        ((canonicalPullbackChoice Yₛ.p).map f₁ y₁Pull ≫
          (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yFiber) := by
      exact congrArg
        (fun t ↦
          (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
            (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv).1 ≫ t)
        hA₁
    _ =
      (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv).1 ≫
          (canonicalPullbackChoice Yₛ.p).map f₁ y₁Pull) ≫
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yFiber := by
      simp only [Category.assoc]
    _ =
      (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        ((canonicalPullbackChoice Yₛ.p).map f₁ local₁ ≫ leg₁.inv.1) ≫
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yFiber := by
      exact congrArg
        (fun t ↦
          (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫ t ≫
            (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yFiber)
        hmap_leg
    _ =
      (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₁ local₁ ≫
        (leg₁.inv.1 ≫ (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₁)) yFiber) := by
      simp only [Category.assoc]
    _ =
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₁ local₁) ≫ g i₁ := by
      simpa only [Category.assoc] using
        congrArg
          (fun t ↦
            (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom).1 ≫
              (canonicalPullbackChoice Yₛ.p).map f₁ local₁ ≫ t)
          hleg
  exact hpre.trans hfinal

/-- Helper for Lemma 8.10.5: the right local target identification and target-leg comparison
postcompose with the chosen right target tail to the literal local target arrow followed by the
cover leg. -/
theorem inherited_basis_target_leg_direct_tail_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} {i₂ : ι}
    (f₂ : Z ⟶ Yₛ.p.obj (Y i₂)) :
    let yFiber : Yₛ.p.Fiber (Yₛ.p.obj y) := Functor.Fiber.mk (a := y) rfl
    let y₂Pull :=
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj
        yFiber)
    let tail₂a := (canonicalPullbackChoice Yₛ.p).map f₂ y₂Pull
    let tail₂b := (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yFiber
    let tail₂ := tail₂a ≫ tail₂b
    ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map
          (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)).hom) ≫
        (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map
          (inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (g i₂)).inv)).1 ≫
      tail₂ =
      ((canonicalPullbackChoice Yₛ.p).map f₂
          ((fiberFunctor F (Yₛ.p.obj (Y i₂))).obj
            (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)).hom.1) ≫
        g i₂ := by
  intro yFiber y₂Pull tail₂a tail₂b tail₂
  let loc₂ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)
  let leg₂ := inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (g i₂)
  let local₂ : Yₛ.p.Fiber (Yₛ.p.obj (Y i₂)) := Functor.Fiber.mk (a := Y i₂) rfl
  have hmap_leg :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv)).1 ≫
        tail₂a =
      (canonicalPullbackChoice Yₛ.p).map f₂ local₂ ≫ leg₂.inv.1 := by
    simpa [leg₂, y₂Pull, tail₂a, local₂] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := f₂) (φ := leg₂.inv)
  have hleg :
      leg₂.inv.1 ≫ tail₂b = g i₂ := by
    simpa [leg₂, yFiber, tail₂b] using
      inherited_basis_target_pullback_leg_iso_symm_hom_postcompose
        (J := J) (Yₛ := Yₛ) (g i₂)
  have hmap_loc :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom)).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₂ local₂ =
      (canonicalPullbackChoice Yₛ.p).map f₂
          ((fiberFunctor F (Yₛ.p.obj (Y i₂))).obj
            (inherited_source_fiber_obj (F := F) (D.obj i₂))) ≫
        loc₂.hom.1 := by
    simpa [loc₂, local₂] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := f₂) (φ := loc₂.hom)
  have hpre :
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom) ≫
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv)).1 ≫
        tail₂ =
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
        (canonicalPullbackChoice Yₛ.p).map f₂ local₂) ≫ g i₂ := by
    calc
      ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom) ≫
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv)).1 ≫
        tail₂ =
        (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv).1 ≫
            tail₂a ≫ tail₂b := by
          change
            ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
                (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv).1) ≫
              (tail₂a ≫ tail₂b) =
            (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
              (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv).1 ≫
                tail₂a ≫ tail₂b
          simp only [Category.assoc]
    _ =
        (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
          ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv).1 ≫
            tail₂a) ≫ tail₂b := by
          simp only [Category.assoc]
    _ =
        (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
          (((canonicalPullbackChoice Yₛ.p).map f₂ local₂ ≫ leg₂.inv.1) ≫ tail₂b) := by
          exact congrArg
            (fun t ↦
              (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
                t ≫ tail₂b)
            hmap_leg
    _ =
        (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
          ((canonicalPullbackChoice Yₛ.p).map f₂ local₂ ≫ leg₂.inv.1) ≫ tail₂b := by
          simp only [Category.assoc]
    _ =
        (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
          (canonicalPullbackChoice Yₛ.p).map f₂ local₂ ≫
            (leg₂.inv.1 ≫ tail₂b) := by
          simp only [Category.assoc]
    _ =
        ((((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom).1 ≫
          (canonicalPullbackChoice Yₛ.p).map f₂ local₂) ≫ g i₂ := by
          rw [hleg]
          simp only [Category.assoc]
          rfl
  exact hpre.trans (congrArg (fun t ↦ t ≫ g i₂) hmap_loc)

end

end CategoryTheory
