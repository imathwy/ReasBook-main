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

/-- Helper for Lemma 8.10.5: in a fiber category, the underlying arrow of the equality isomorphism
coming from a component equality is the corresponding `eqToHom`. -/
private theorem fiber_eqToIso_hom_val
    {U : C} {x y : Yₛ.p.Fiber U} (h : x.1 = y.1) :
    ((eqToIso (C := Yₛ.p.Fiber U) (Subtype.ext h : x = y)).hom).1 = eqToHom h := by
  cases x with
  | mk xv xp =>
  cases y with
  | mk yv yp =>
  cases h
  rfl

/-- Helper for Lemma 8.10.5: a source morphism whose local pullbacks are the source-forgets of a
target descent morphism is automatically compatible with the tautological target identifications. -/
theorem inherited_basis_target_identity_of_source_descent_lift
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y))
    {A B : (G F).Fiber y}
    (φ :
      (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A) ⟶
        (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj B))
    (αX :
      (inherited_source_fiber_forget (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y).obj A ⟶
        (inherited_source_fiber_forget (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y).obj B)
    (hαX :
      ∀ i,
        (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map αX) =
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A).inv ≫
            (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i) ≫
              (inherited_source_pullback_comparison
                (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) B).hom) :
    (fiberFunctor F (Yₛ.p.obj y)).map αX ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F B).hom =
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A).hom := by
  let TY :=
    ((canonicalFiberPseudofunctor Yₛ.p).toDescentData
      (fun i ↦ Yₛ.p.map (g i)))
  have hstackFor :
      (canonicalFiberPseudofunctor Yₛ.p).IsStackFor
        (Presieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i))) := by
    simpa [TY, Sieve.ofArrows] using
      (canonicalFiberPseudofunctor Yₛ.p).isStackFor'
        (Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)))
        hbaseCover
  have hTY : TY.IsEquivalence :=
    (canonicalFiberPseudofunctor Yₛ.p).isStackFor_ofArrows_iff
      (fun i ↦ Yₛ.p.map (g i)) |>.1 hstackFor
  letI : TY.IsEquivalence := hTY
  letI : Functor.Faithful TY := by infer_instance
  apply TY.map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  let locA := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A
  let locB := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F B
  let Apull : (G F).Fiber (Y i) :=
    ((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj A
  let Bpull : (G F).Fiber (Y i) :=
    ((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj B
  let locAp := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F Apull
  let locBp := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F Bpull
  let eA :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A
  let eB :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) B
  let pcA := FibredCategoryMor.pullbackComparison
      (StackInGroupoidsOver.Hom.toFibredCategoryMor F) (Yₛ.p.map (g i))
      ((inherited_source_fiber_forget (F := F) y).obj A)
  let pcB := FibredCategoryMor.pullbackComparison
      (StackInGroupoidsOver.Hom.toFibredCategoryMor F) (Yₛ.p.map (g i))
      ((inherited_source_fiber_forget (F := F) y).obj B)
  have hnat :=
    FibredCategoryMor.pullbackComparison_naturality_over_vertical
      (StackInGroupoidsOver.Hom.toFibredCategoryMor F) (Yₛ.p.map (g i)) αX
  have hloc := inherited_basis_local_target_iso_naturality
    (J := J) (Yₛ := Yₛ) F (φ.hom i)
  have hlocal := congrArg (fun η ↦ (fiberFunctor F (Yₛ.p.obj (Y i))).map η) (hαX i)
  let mapY := ((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor
  let mapX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor
  let FYi := fiberFunctor F (Yₛ.p.obj (Y i))
  let forgetφ := (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i)
  let leg := inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (f := g i)
  have hAmap :
      mapY.map locA.hom =
        pcA.hom ≫ FYi.map eA.inv ≫ locAp.hom ≫ leg.symm.hom := by
    exact
      inherited_basis_target_map_local_target_iso
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F (g i) A
  have hBmap :
      mapY.map locB.hom =
        pcB.hom ≫ FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom := by
    exact
      inherited_basis_target_map_local_target_iso
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F (g i) B
  have hlocal' :
      FYi.map (mapX.map αX) =
        FYi.map eA.inv ≫ FYi.map forgetφ ≫ FYi.map eB.hom := by
    calc
      FYi.map (mapX.map αX) =
          FYi.map (eA.inv ≫ forgetφ ≫ eB.hom) := by
            simpa only [mapX, FYi, eA, eB, forgetφ] using hlocal
      _ = FYi.map eA.inv ≫ FYi.map forgetφ ≫ FYi.map eB.hom := by
            rw [Functor.map_comp, Functor.map_comp]
  have hloc' :
      FYi.map forgetφ ≫ locBp.hom = locAp.hom := by
    simpa [FYi, forgetφ, locAp, locBp, Apull, Bpull] using hloc
  have heBcancel :
      FYi.map eB.hom ≫ FYi.map eB.inv = 𝟙 _ := by
    rw [← Functor.map_comp, eB.hom_inv_id, Functor.map_id]
  change mapY.map ((fiberFunctor F (Yₛ.p.obj y)).map αX ≫ locB.hom) = mapY.map locA.hom
  have hcalc :
      mapY.map ((fiberFunctor F (Yₛ.p.obj y)).map αX ≫ locB.hom) =
        pcA.hom ≫ FYi.map eA.inv ≫ locAp.hom ≫ leg.symm.hom := by
    calc
    mapY.map ((fiberFunctor F (Yₛ.p.obj y)).map αX ≫ locB.hom) =
        mapY.map ((fiberFunctor F (Yₛ.p.obj y)).map αX) ≫ mapY.map locB.hom := by
          rw [Functor.map_comp]
    _ =
        mapY.map ((fiberFunctor F (Yₛ.p.obj y)).map αX) ≫
          (pcB.hom ≫ FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom) := by
          exact
            congrArg
              (fun t ↦ mapY.map ((fiberFunctor F (Yₛ.p.obj y)).map αX) ≫ t)
              hBmap
    _ =
        (pcA.hom ≫ FYi.map (mapX.map αX)) ≫
          FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom := by
          have hnat' :=
            congrArg (fun t ↦ t ≫ FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom) hnat
          simpa only [mapY, mapX, FYi, pcA, pcB,
            StackInGroupoidsOver.Hom.fiberFunctor, ← Category.assoc] using hnat'
    _ =
        pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫ FYi.map eB.hom ≫
          FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom := by
          calc
            (pcA.hom ≫ FYi.map (mapX.map αX)) ≫
                FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom =
              pcA.hom ≫
                (FYi.map (mapX.map αX) ≫ FYi.map eB.inv ≫
                  locBp.hom ≫ leg.symm.hom) := by
                simp only [Category.assoc]
            _ =
              pcA.hom ≫
                ((FYi.map eA.inv ≫ FYi.map forgetφ ≫ FYi.map eB.hom) ≫
                  FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom) := by
                exact congrArg
                  (fun t ↦ pcA.hom ≫
                    (t ≫ FYi.map eB.inv ≫ locBp.hom ≫ leg.symm.hom))
                  hlocal'
            _ =
              pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
                FYi.map eB.hom ≫ FYi.map eB.inv ≫ locBp.hom ≫
                  leg.symm.hom := by
                simp only [Category.assoc]
    _ =
        pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
          𝟙 _ ≫ locBp.hom ≫ leg.symm.hom := by
          calc
            pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
                FYi.map eB.hom ≫ FYi.map eB.inv ≫
                  locBp.hom ≫ leg.symm.hom =
              pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
                (FYi.map eB.hom ≫ FYi.map eB.inv) ≫
                  locBp.hom ≫ leg.symm.hom := by
                simp only [Category.assoc]
            _ =
              pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
                𝟙 _ ≫ locBp.hom ≫ leg.symm.hom := by
                have hcancel :=
                  congrArg
                    (fun t ↦ pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫ t ≫
                      locBp.hom ≫ leg.symm.hom)
                    heBcancel
                have hparen :
                    pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
                        (FYi.map eB.hom ≫ FYi.map eB.inv) ≫
                          locBp.hom ≫ leg.symm.hom =
                      pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
                        𝟙 (FYi.obj (inherited_source_fiber_obj (F := F) Bpull)) ≫
                          locBp.hom ≫ leg.symm.hom := by
                  simpa only [Bpull] using hcancel
                exact hparen
    _ =
        pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
          locBp.hom ≫ leg.symm.hom := by
          simp only [Category.id_comp]
    _ =
        pcA.hom ≫ FYi.map eA.inv ≫ locAp.hom ≫ leg.symm.hom := by
          calc
            pcA.hom ≫ FYi.map eA.inv ≫ FYi.map forgetφ ≫
                locBp.hom ≫ leg.symm.hom =
              pcA.hom ≫ FYi.map eA.inv ≫
                (FYi.map forgetφ ≫ locBp.hom) ≫ leg.symm.hom := by
                simp only [Category.assoc]
            _ =
              pcA.hom ≫ FYi.map eA.inv ≫ locAp.hom ≫ leg.symm.hom := by
                exact congrArg
                  (fun t ↦ pcA.hom ≫ FYi.map eA.inv ≫ t ≫ leg.symm.hom)
                  hloc'
  exact hcalc.trans hAmap.symm

/-- Helper for Lemma 8.10.5: a source-fiber morphism whose image preserves the tautological
target identifications lifts uniquely to the corresponding `G F`-fiber morphism. -/
theorem inherited_basis_lift_source_hom_of_target_identity
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {y : Yₛ.S} {A B : (G F).Fiber y}
    (αX :
      (inherited_source_fiber_forget (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y).obj A ⟶
        (inherited_source_fiber_forget (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y).obj B)
    (h :
      (fiberFunctor F (Yₛ.p.obj y)).map αX ≫
          (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F B).hom =
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A).hom) :
    ∃ α : A ⟶ B,
      (inherited_source_fiber_forget (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y).map α = αX := by
  let locA := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A
  let locB := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F B
  have hval0 := congrArg (fun η ↦ η.1) h
  have hlocA :
      locA.hom.1 = eqToHom A.2 := by
    change ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj y))
      (Subtype.ext A.2 : (fiberFunctor F (Yₛ.p.obj y)).obj
        (inherited_source_fiber_obj (F := F) A) =
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)))).hom).1 = eqToHom A.2
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) A.2
  have hlocB :
      locB.hom.1 = eqToHom B.2 := by
    change ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj y))
      (Subtype.ext B.2 : (fiberFunctor F (Yₛ.p.obj y)).obj
        (inherited_source_fiber_obj (F := F) B) =
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)))).hom).1 = eqToHom B.2
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) B.2
  have htarget :
      (G F).map αX.1 ≫ eqToHom B.2 = eqToHom A.2 := by
    have hval : ((fiberFunctor F (Yₛ.p.obj y)).map αX).1 ≫ locB.hom.1 = locA.hom.1 := by
      simpa using hval0
    change (G F).map αX.1 ≫ eqToHom B.2 = eqToHom A.2
    simpa [locA, locB, hlocA, hlocB, StackInGroupoidsOver.Hom.fiberFunctor] using hval
  have hGF :
      (G F).map αX.1 =
        eqToHom A.2 ≫ 𝟙 y ≫ eqToHom B.2.symm := by
    apply (cancel_mono (eqToHom B.2)).1
    calc
      (G F).map αX.1 ≫ eqToHom B.2 =
          eqToHom A.2 := htarget
      _ = (eqToHom A.2 ≫ 𝟙 y ≫ eqToHom B.2.symm) ≫ eqToHom B.2 := by
          simp only [Category.assoc]
          rw [eqToHom_trans]
          rw [show B.2.symm.trans B.2 = rfl by apply Subsingleton.elim]
          simp
  have hLift : (G F).IsHomLift (𝟙 y) αX.1 := by
    refine IsHomLift.of_fac' (G F) (𝟙 y) αX.1 A.2 B.2 ?_
    exact hGF
  let α : A ⟶ B := Functor.Fiber.homMk (G F) y αX.1
  refine ⟨α, ?_⟩
  apply Functor.Fiber.hom_ext
  rfl

/-- Helper for Lemma 8.10.5: the local component morphism from the reconstructed descent
datum to `D` is the unique lift of the source counit component; its source-forget value is
recorded explicitly for the final descent-square check. -/
theorem inherited_basis_reconstructed_component_hom_exists
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    (x : Xₛ.p.Fiber (Yₛ.p.obj y))
    (ε :
      ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i))).obj x ≅
      (inherited_basis_simple_forget_to_source_descent_functor
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (Y := Y) (g := g) F).obj D)
    (tc :
      (fiberFunctor F (Yₛ.p.obj y)).obj x ≅
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)))
    (htcLocal :
      ∀ i,
        (((fiberFunctor F (Yₛ.p.obj (Y i))).map (ε.hom.hom i)).1 ≫
            (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i)).hom.1) ≫
          g i =
        (SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
            ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i)) x) ≫
          tc.hom.1)
    (i : ι) :
    let xGF : (G F).Fiber ((G F).obj x.1) := Functor.Fiber.mk (a := x.1) rfl
    let A : (G F).Fiber y :=
      (((canonicalFiberPseudofunctor (G F)).map tc.inv.1.op.toLoc).toFunctor.obj xGF)
    let αX := inherited_basis_reconstructed_source_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F x tc
    let eA :=
      inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A
    let sourceMap :=
      ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor
    ∃ αi :
        (((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj A) ⟶
          D.obj i,
      (inherited_source_fiber_forget (F := F) (Y i)).map αi =
        eA.hom ≫ sourceMap.map αX ≫ ε.hom.hom i := by
  intro xGF A αX eA sourceMap
  let H := StackInGroupoidsOver.Hom.toFibredCategoryMor F
  let FYi := fiberFunctor F (Yₛ.p.obj (Y i))
  let locD := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i)
  let locA := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A
  let Apull : (G F).Fiber (Y i) :=
    (((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj A)
  let locAp := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F Apull
  let pbgX := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i)) x
  let sourceA := inherited_source_fiber_obj (F := F) A
  let pbgA_X := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i)) sourceA
  let pbgA := (canonicalPullbackChoice (G F)).map (g i) A
  let pb := (canonicalPullbackChoice (G F)).map tc.inv.1 xGF
  let αXi := eA.hom ≫ sourceMap.map αX ≫ ε.hom.hom i
  have htargeti :
      FYi.map αXi ≫ locD.hom = locAp.hom := by
    apply Functor.Fiber.hom_ext
    have htail : Yₛ.p.IsStronglyCartesian (Yₛ.p.map (g i)) (g i) := by
      exact (inferInstance : IsFibredInGroupoids Yₛ.p).isStronglyCartesian_map (g i)
    letI : Yₛ.p.IsStronglyCartesian (Yₛ.p.map (g i)) (g i) := htail
    refine
      @Functor.IsStronglyCartesian.ext _ _ _ _ Yₛ.p _ _ _ _
        (Yₛ.p.map (g i)) (g i) htail _ _ (𝟙 (Yₛ.p.obj (Y i)))
        (FYi.map αXi ≫ locD.hom).1 locAp.hom.1
        (by exact (FYi.map αXi ≫ locD.hom).2) locAp.hom.2 ?_
    have htcLocal' :
        ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1) ≫ g i =
          H.toHom.map pbgX ≫ tc.hom.1 := by
      simpa only [FYi, locD, H, pbgX] using htcLocal i
    have hnatX :
        (sourceMap.map αX).1 ≫ pbgX = pbgA_X ≫ αX.1 := by
      simpa [sourceMap, pbgX, pbgA_X, αX] using
        (canonical_pullbackFunctor_map_fac_owner
          (p := Xₛ.p) (Yₛ.p.map (g i)) αX)
    have heApost :
        eA.hom.1 ≫ pbgA_X = pbgA := by
      simpa [eA, pbgA_X, pbgA] using
        inherited_source_pullback_comparison_hom_postcompose
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A
    have hαX_val : αX.1 = pb := by
      rfl
    have hsourcePost :
        (eA.hom.1 ≫ (sourceMap.map αX).1) ≫ pbgX = pbgA ≫ pb := by
      have hpre :
          (eA.hom.1 ≫ (sourceMap.map αX).1) ≫ pbgX = pbgA ≫ αX.1 := by
        calc
          (eA.hom.1 ≫ (sourceMap.map αX).1) ≫ pbgX =
              eA.hom.1 ≫ ((sourceMap.map αX).1 ≫ pbgX) := by
                simp only [Category.assoc]
          _ = eA.hom.1 ≫ (pbgA_X ≫ αX.1) := by
                exact congrArg (fun t ↦ eA.hom.1 ≫ t) hnatX
          _ = (eA.hom.1 ≫ pbgA_X) ≫ αX.1 := by
                simp only [Category.assoc]
          _ = pbgA ≫ αX.1 := by
                exact congrArg (fun t ↦ t ≫ αX.1) heApost
      exact hpre.trans (congrArg (fun t ↦ pbgA ≫ t) hαX_val)
    have hpbGF : (G F).IsHomLift tc.inv.1 pb := by
      simpa [pb, xGF] using
        ((canonicalPullbackChoice (G F)).isStronglyCartesian tc.inv.1 xGF).toIsHomLift
    have hpbTarget :
        (G F).map pb ≫ tc.hom.1 = locA.hom.1 := by
      exact
        inherited_basis_target_lift_postcompose_with
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
          (A := A) (x := x) (tc := tc) (locA := locA) rfl hpbGF
    have hlocApPost :
        (G F).map pbgA ≫ locA.hom.1 = locAp.hom.1 ≫ g i := by
      exact
        inherited_basis_local_target_iso_pullback_postcompose_with
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
          (f := g i) (x := A) (locX := locA) (locPull := locAp) rfl rfl
    have hmapαXi :
        (FYi.map αXi).1 =
          H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            (FYi.map (ε.hom.hom i)).1 := by
      change
        (FYi.map (eA.hom ≫ sourceMap.map αX ≫ ε.hom.hom i)).1 =
          H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            (FYi.map (ε.hom.hom i)).1
      rw [Functor.map_comp, Functor.map_comp]
      change
        (FYi.map eA.hom).1 ≫
            ((FYi.map (sourceMap.map αX)).1 ≫ (FYi.map (ε.hom.hom i)).1) =
          H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            (FYi.map (ε.hom.hom i)).1
      have hfirst :
          (FYi.map eA.hom).1 ≫ (FYi.map (sourceMap.map αX)).1 =
            H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) := by
        change
          H.toHom.map eA.hom.1 ≫ H.toHom.map (sourceMap.map αX).1 =
            H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1)
        rw [Functor.map_comp]
      calc
        (FYi.map eA.hom).1 ≫
            ((FYi.map (sourceMap.map αX)).1 ≫ (FYi.map (ε.hom.hom i)).1) =
          ((FYi.map eA.hom).1 ≫ (FYi.map (sourceMap.map αX)).1) ≫
            (FYi.map (ε.hom.hom i)).1 := by
            simp only [Category.assoc]
        _ =
          H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            (FYi.map (ε.hom.hom i)).1 := by
            exact congrArg (fun t ↦ t ≫ (FYi.map (ε.hom.hom i)).1) hfirst
    change ((FYi.map αXi ≫ locD.hom).1) ≫ g i = locAp.hom.1 ≫ g i
    have hstart :
        ((FYi.map αXi ≫ locD.hom).1) ≫ g i =
          (H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i := by
      calc
        ((FYi.map αXi ≫ locD.hom).1) ≫ g i =
            (((FYi.map αXi).1 ≫ locD.hom.1) ≫ g i) := by
              rfl
        _ = ((H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
              (FYi.map (ε.hom.hom i)).1) ≫ locD.hom.1) ≫ g i := by
              exact congrArg (fun t ↦ ((t ≫ locD.hom.1) ≫ g i)) hmapαXi
        _ = (H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
              ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i := by
              simp only [Category.assoc]
    have htargetStep :
        (H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i =
          H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            (H.toHom.map pbgX ≫ tc.hom.1) := by
      have hassoc :
          (H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
              ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i =
            H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
              (((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1) ≫ g i) := by
        simp only [Category.assoc]
      have htarget :=
        congrArg (fun t ↦ H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫ t)
          htcLocal'
      exact hassoc.trans htarget
    have hmapStep :
        H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            (H.toHom.map pbgX ≫ tc.hom.1) =
          H.toHom.map ((eA.hom.1 ≫ (sourceMap.map αX).1) ≫ pbgX) ≫
            tc.hom.1 := by
      have hmap :
          H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            H.toHom.map pbgX =
          H.toHom.map ((eA.hom.1 ≫ (sourceMap.map αX).1) ≫ pbgX) := by
        rw [← Functor.map_comp]
      calc
        H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            (H.toHom.map pbgX ≫ tc.hom.1) =
          (H.toHom.map (eA.hom.1 ≫ (sourceMap.map αX).1) ≫
            H.toHom.map pbgX) ≫ tc.hom.1 := by
            simp only [Category.assoc]
        _ = H.toHom.map ((eA.hom.1 ≫ (sourceMap.map αX).1) ≫ pbgX) ≫
            tc.hom.1 := by
            exact congrArg (fun t ↦ t ≫ tc.hom.1) hmap
    have hsourceStep :
        H.toHom.map ((eA.hom.1 ≫ (sourceMap.map αX).1) ≫ pbgX) ≫
            tc.hom.1 =
          H.toHom.map (pbgA ≫ pb) ≫ tc.hom.1 := by
      exact congrArg (fun t ↦ H.toHom.map t ≫ tc.hom.1) hsourcePost
    have hfoldMap :
        H.toHom.map (pbgA ≫ pb) ≫ tc.hom.1 =
          (G F).map pbgA ≫ ((G F).map pb ≫ tc.hom.1) := by
      change (G F).map (pbgA ≫ pb) ≫ tc.hom.1 =
        (G F).map pbgA ≫ ((G F).map pb ≫ tc.hom.1)
      rw [Functor.map_comp]
      simp only [Category.assoc]
    have hpbStep :
        (G F).map pbgA ≫ ((G F).map pb ≫ tc.hom.1) =
          (G F).map pbgA ≫ locA.hom.1 := by
      exact congrArg (fun t ↦ (G F).map pbgA ≫ t) hpbTarget
    exact
      hstart.trans
        (htargetStep.trans
          (hmapStep.trans
            (hsourceStep.trans (hfoldMap.trans (hpbStep.trans hlocApPost)))))
  rcases inherited_basis_lift_source_hom_of_target_identity
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F αXi htargeti with
    ⟨αi, hαi⟩
  exact ⟨αi, hαi⟩


end

end CategoryTheory
