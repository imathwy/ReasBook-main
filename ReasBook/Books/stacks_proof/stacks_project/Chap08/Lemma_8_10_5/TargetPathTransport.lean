import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.TargetTransfer


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

private theorem fiber_eqToIso_hom_val
    {U : C} {x y : Yₛ.p.Fiber U} (h : x.1 = y.1) :
    ((eqToIso (C := Yₛ.p.Fiber U) (Subtype.ext h : x = y)).hom).1 = eqToHom h := by
  cases x with
  | mk xv xp =>
  cases y with
  | mk yv yp =>
  cases h
  rfl

/-- Helper for Lemma 8.10.5: applying `G F` to the chosen pullback arrow and then using the
tautological local target identification is the same as first identifying the pulled-back local
target and then following the original target arrow. -/
theorem inherited_basis_local_target_iso_pullback_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi z : Yₛ.S} (f : z ⟶ yi) (x : (G F).Fiber yi) :
    (G F).map ((canonicalPullbackChoice (G F)).map f x) ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F x).hom.1 =
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F
          (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)).hom.1 ≫ f := by
  let xPull : (G F).Fiber z :=
    (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let pb := (canonicalPullbackChoice (G F)).map f x
  have hpb : (G F).map pb = eqToHom xPull.2 ≫ f ≫ eqToHom x.2.symm := by
    letI : (G F).IsHomLift f pb := by
      simpa [pb] using ((canonicalPullbackChoice (G F)).isStronglyCartesian f x).toIsHomLift
    simpa [pb, xPull] using (IsHomLift.fac' (G F) f pb)
  have hlocx :
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F x).hom.1 = eqToHom x.2 := by
    change ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj yi))
      (Subtype.ext x.2 : (fiberFunctor F (Yₛ.p.obj yi)).obj
        (inherited_source_fiber_obj (F := F) x) =
        (Functor.Fiber.mk (a := yi) rfl : Yₛ.p.Fiber (Yₛ.p.obj yi)))).hom).1 = eqToHom x.2
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) x.2
  have hlocp :
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F xPull).hom.1 =
        eqToHom xPull.2 := by
    change ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj z))
      (Subtype.ext xPull.2 : (fiberFunctor F (Yₛ.p.obj z)).obj
        (inherited_source_fiber_obj (F := F) xPull) =
        (Functor.Fiber.mk (a := z) rfl : Yₛ.p.Fiber (Yₛ.p.obj z)))).hom).1 = eqToHom xPull.2
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) xPull.2
  rw [hpb, hlocx, hlocp]
  calc
    (eqToHom xPull.2 ≫ f ≫ eqToHom x.2.symm) ≫ eqToHom x.2 =
        eqToHom xPull.2 ≫ f ≫ (eqToHom x.2.symm ≫ eqToHom x.2) := by
          simp only [Category.assoc]
    _ = eqToHom xPull.2 ≫ f ≫ eqToHom (x.2.symm.trans x.2) := by
          rw [eqToHom_trans]
    _ = eqToHom xPull.2 ≫ f := by
          rw [show x.2.symm.trans x.2 = rfl by apply Subsingleton.elim]
          simp

/-- Helper for Lemma 8.10.5: supplied-local-iso wrapper for
`inherited_basis_local_target_iso_pullback_postcompose`, avoiding large local unfoldings at call
sites. -/
theorem inherited_basis_local_target_iso_pullback_postcompose_with
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi z : Yₛ.S} (f : z ⟶ yi) (x : (G F).Fiber yi)
    (locX :
      (fiberFunctor F (Yₛ.p.obj yi)).obj (inherited_source_fiber_obj (F := F) x) ≅
        (Functor.Fiber.mk (a := yi) rfl : Yₛ.p.Fiber (Yₛ.p.obj yi)))
    (locPull :
      (fiberFunctor F (Yₛ.p.obj z)).obj (inherited_source_fiber_obj (F := F)
          (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)) ≅
        (Functor.Fiber.mk (a := z) rfl : Yₛ.p.Fiber (Yₛ.p.obj z)))
    (hlocX : locX = inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F x)
    (hlocPull :
      locPull =
        inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F
          (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)) :
    (G F).map ((canonicalPullbackChoice (G F)).map f x) ≫ locX.hom.1 =
      locPull.hom.1 ≫ f := by
  rw [hlocX, hlocPull]
  exact
    inherited_basis_local_target_iso_pullback_postcompose
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F f x

/-- Helper for Lemma 8.10.5: any lift of the inverse target comparison becomes the local target
identification after composing with the comparison back to `y`. -/
theorem inherited_basis_target_lift_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {y : Yₛ.S} {A : (G F).Fiber y} {x : Xₛ.p.Fiber (Yₛ.p.obj y)}
    (tc :
      (fiberFunctor F (Yₛ.p.obj y)).obj x ≅
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)))
    {pb : A.1 ⟶ x.1} (hpb : (G F).IsHomLift tc.inv.1 pb) :
    (G F).map pb ≫ tc.hom.1 =
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A).hom.1 := by
  letI : (G F).IsHomLift tc.inv.1 pb := hpb
  have hfac0 := IsHomLift.fac' (G F) tc.inv.1 pb
  have hdom :
      IsHomLift.domain_eq (G F) tc.inv.1 pb = A.2 := by
    apply Subsingleton.elim
  have hcodId :
      eqToHom (IsHomLift.codomain_eq (G F) tc.inv.1 pb).symm =
        𝟙 ((fiberFunctor F (Yₛ.p.obj y)).obj x).1 := by
    rw [show IsHomLift.codomain_eq (G F) tc.inv.1 pb = rfl by
      apply Subsingleton.elim]
    rfl
  have hfac :
      (G F).map pb = eqToHom A.2 ≫ tc.inv.1 := by
    rw [hdom] at hfac0
    have htail :
        eqToHom A.2 ≫ tc.inv.1 ≫
            eqToHom (IsHomLift.codomain_eq (G F) tc.inv.1 pb).symm =
          eqToHom A.2 ≫ tc.inv.1 := by
      rw [hcodId]
      simpa only [Category.assoc] using Category.comp_id (eqToHom A.2 ≫ tc.inv.1)
    exact hfac0.trans htail
  have hlocA :
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A).hom.1 =
        eqToHom A.2 := by
    change
      ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj y))
        (Subtype.ext A.2 :
          (fiberFunctor F (Yₛ.p.obj y)).obj
            (inherited_source_fiber_obj (F := F) A) =
          (Functor.Fiber.mk (a := y) rfl :
            Yₛ.p.Fiber (Yₛ.p.obj y)))).hom).1 = eqToHom A.2
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) A.2
  have htcCancel : tc.inv.1 ≫ tc.hom.1 = 𝟙 y := by
    exact congrArg Subtype.val tc.inv_hom_id
  have h1 :
      (G F).map pb ≫ tc.hom.1 =
        (eqToHom A.2 ≫ tc.inv.1) ≫ tc.hom.1 :=
    congrArg (fun t ↦ t ≫ tc.hom.1) hfac
  have h2 :
      (eqToHom A.2 ≫ tc.inv.1) ≫ tc.hom.1 =
        eqToHom A.2 := by
    have h21 :
        (eqToHom A.2 ≫ tc.inv.1) ≫ tc.hom.1 =
          eqToHom A.2 ≫ (tc.inv.1 ≫ tc.hom.1) := by
      exact Category.assoc (eqToHom A.2) tc.inv.1 tc.hom.1
    have h22 :
        eqToHom A.2 ≫ (tc.inv.1 ≫ tc.hom.1) =
          eqToHom A.2 ≫ 𝟙 y :=
      congrArg (fun t ↦ eqToHom A.2 ≫ t) htcCancel
    have h23 : eqToHom A.2 ≫ 𝟙 y = eqToHom A.2 :=
      Category.comp_id (eqToHom A.2)
    exact h21.trans (h22.trans h23)
  exact h1.trans (h2.trans hlocA.symm)

/-- Helper for Lemma 8.10.5: same as `inherited_basis_target_lift_postcompose`, but with the
local target isomorphism supplied by the caller to avoid unfolding large local `let`s. -/
theorem inherited_basis_target_lift_postcompose_with
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {y : Yₛ.S} {A : (G F).Fiber y} {x : Xₛ.p.Fiber (Yₛ.p.obj y)}
    (tc :
      (fiberFunctor F (Yₛ.p.obj y)).obj x ≅
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)))
    (locA :
      (fiberFunctor F (Yₛ.p.obj y)).obj (inherited_source_fiber_obj (F := F) A) ≅
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)))
    (hlocA : locA = inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A)
    {pb : A.1 ⟶ x.1} (hpb : (G F).IsHomLift tc.inv.1 pb) :
    (G F).map pb ≫ tc.hom.1 = locA.hom.1 := by
  rw [hlocA]
  exact
    inherited_basis_target_lift_postcompose
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
      (A := A) (x := x) (tc := tc) (pb := pb) hpb

/-- Helper for Lemma 8.10.5: the reconstructed object is chosen as the pullback of the glued
source object along the inverse target comparison, so its chosen pullback arrow becomes the local
target identification after composing with the comparison back to `y`. -/
theorem inherited_basis_reconstructed_target_pullback_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {y : Yₛ.S} (x : Xₛ.p.Fiber (Yₛ.p.obj y))
    (tc :
      (fiberFunctor F (Yₛ.p.obj y)).obj x ≅
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y))) :
    let xGF : (G F).Fiber ((G F).obj x.1) := Functor.Fiber.mk (a := x.1) rfl
    let A : (G F).Fiber y :=
      (((canonicalFiberPseudofunctor (G F)).map tc.inv.1.op.toLoc).toFunctor.obj xGF)
    let pb := (canonicalPullbackChoice (G F)).map tc.inv.1 xGF
    (G F).map pb ≫ tc.hom.1 =
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A).hom.1 := by
  intro xGF A pb
  letI : (G F).IsHomLift tc.inv.1 pb := by
    simpa [pb, xGF] using
      ((canonicalPullbackChoice (G F)).isStronglyCartesian tc.inv.1 xGF).toIsHomLift
  have hfac0 := IsHomLift.fac' (G F) tc.inv.1 pb
  have hdom :
      IsHomLift.domain_eq (G F) tc.inv.1 pb = A.2 := by
    apply Subsingleton.elim
  have hcod :
      IsHomLift.codomain_eq (G F) tc.inv.1 pb = xGF.2 := by
    apply Subsingleton.elim
  have hcodId :
      eqToHom (IsHomLift.codomain_eq (G F) tc.inv.1 pb).symm =
        𝟙 ((fiberFunctor F (Yₛ.p.obj y)).obj x).1 := by
    rw [hcod]
    change eqToHom rfl = 𝟙 ((fiberFunctor F (Yₛ.p.obj y)).obj x).1
    rfl
  have hfac :
      (G F).map pb = eqToHom A.2 ≫ tc.inv.1 := by
    rw [hdom] at hfac0
    have htail :
        eqToHom A.2 ≫ tc.inv.1 ≫
            eqToHom (IsHomLift.codomain_eq (G F) tc.inv.1 pb).symm =
      eqToHom A.2 ≫ tc.inv.1 := by
      rw [hcodId]
      simpa only [Category.assoc] using Category.comp_id (eqToHom A.2 ≫ tc.inv.1)
    exact hfac0.trans htail
  have hlocA :
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A).hom.1 =
        eqToHom A.2 := by
    change
      ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj y))
        (Subtype.ext A.2 :
          (fiberFunctor F (Yₛ.p.obj y)).obj
            (inherited_source_fiber_obj (F := F) A) =
          (Functor.Fiber.mk (a := y) rfl :
            Yₛ.p.Fiber (Yₛ.p.obj y)))).hom).1 = eqToHom A.2
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) A.2
  have htcCancel : tc.inv.1 ≫ tc.hom.1 = 𝟙 y := by
    exact congrArg Subtype.val tc.inv_hom_id
  have h1 :
      (G F).map pb ≫ tc.hom.1 =
        (eqToHom A.2 ≫ tc.inv.1) ≫ tc.hom.1 :=
    congrArg (fun t ↦ t ≫ tc.hom.1) hfac
  have h2 :
      (eqToHom A.2 ≫ tc.inv.1) ≫ tc.hom.1 =
        eqToHom A.2 := by
    have h21 :
        (eqToHom A.2 ≫ tc.inv.1) ≫ tc.hom.1 =
          eqToHom A.2 ≫ (tc.inv.1 ≫ tc.hom.1) := by
      exact Category.assoc (eqToHom A.2) tc.inv.1 tc.hom.1
    have h22 :
        eqToHom A.2 ≫ (tc.inv.1 ≫ tc.hom.1) =
          eqToHom A.2 ≫ 𝟙 y :=
      congrArg (fun t ↦ eqToHom A.2 ≫ t) htcCancel
    have h23 : eqToHom A.2 ≫ 𝟙 y = eqToHom A.2 :=
      Category.comp_id (eqToHom A.2)
    exact h21.trans (h22.trans h23)
  exact h1.trans (h2.trans hlocA.symm)

/-- Helper for Lemma 8.10.5: the chosen pullback used to reconstruct the object over `y`
is vertical after forgetting to the source stack, hence gives the source morphism from the
reconstructed source object to the glued source object. -/
noncomputable def inherited_basis_reconstructed_source_hom
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {y : Yₛ.S} (x : Xₛ.p.Fiber (Yₛ.p.obj y))
    (tc :
      (fiberFunctor F (Yₛ.p.obj y)).obj x ≅
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y))) :
    let xGF : (G F).Fiber ((G F).obj x.1) := Functor.Fiber.mk (a := x.1) rfl
    let A : (G F).Fiber y :=
      (((canonicalFiberPseudofunctor (G F)).map tc.inv.1.op.toLoc).toFunctor.obj xGF)
    (inherited_source_fiber_obj (F := F) A) ⟶ x := by
  intro xGF A
  let pb := (canonicalPullbackChoice (G F)).map tc.inv.1 xGF
  have hpbSource :
      Xₛ.p.IsHomLift (Yₛ.p.map tc.inv.1) pb := by
    exact
      (inherited_source_pullback_lift_isStronglyCartesian
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) tc.inv.1 xGF).toIsHomLift
  have hcodY : Yₛ.p.obj ((G F).obj x.1) = Yₛ.p.obj y := by
    have hcomm :
        Yₛ.p.obj ((G F).obj x.1) = Xₛ.p.obj x.1 := by
      exact
        congrArg (fun H ↦ H.obj x.1) (StackInGroupoidsOver.Hom.comm F)
    exact hcomm.trans x.2
  have hpbSource' :
      Xₛ.p.IsHomLift (Yₛ.p.map tc.inv.1 ≫ eqToHom hcodY) pb := by
    letI : Xₛ.p.IsHomLift (Yₛ.p.map tc.inv.1) pb := hpbSource
    infer_instance
  have htcMap : Yₛ.p.map tc.inv.1 ≫ eqToHom hcodY = 𝟙 (Yₛ.p.obj y) := by
    letI : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y)) tc.inv.1 := tc.inv.2
    have hdom :
        IsHomLift.domain_eq Yₛ.p (𝟙 (Yₛ.p.obj y)) tc.inv.1 = rfl := by
      apply Subsingleton.elim
    have hcod :
        IsHomLift.codomain_eq Yₛ.p (𝟙 (Yₛ.p.obj y)) tc.inv.1 = hcodY := by
      apply Subsingleton.elim
    have hleft :
        eqToHom (IsHomLift.domain_eq Yₛ.p (𝟙 (Yₛ.p.obj y)) tc.inv.1).symm =
          𝟙 (Yₛ.p.obj y) := by
      rw [show (IsHomLift.domain_eq Yₛ.p (𝟙 (Yₛ.p.obj y)) tc.inv.1).symm = rfl by
        apply Subsingleton.elim]
      rfl
    have hfac := (IsHomLift.fac Yₛ.p (𝟙 (Yₛ.p.obj y)) tc.inv.1).symm
    rw [hdom, hcod] at hfac
    rw [hleft] at hfac
    have hfac' :
        (𝟙 (Yₛ.p.obj y) ≫ Yₛ.p.map tc.inv.1) ≫ eqToHom hcodY =
          𝟙 (Yₛ.p.obj y) := by
      simpa only [Category.assoc] using hfac
    have hid :
        𝟙 (Yₛ.p.obj y) ≫ Yₛ.p.map tc.inv.1 = Yₛ.p.map tc.inv.1 :=
      Category.id_comp (Yₛ.p.map tc.inv.1)
    exact (congrArg (fun t ↦ t ≫ eqToHom hcodY) hid).symm.trans hfac'
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y)) pb := by
    simpa [htcMap] using hpbSource'
  exact Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj y) pb

/-- Helper for Lemma 8.10.5: the inverse target-leg comparison postcomposes with the chosen
pullback arrow to the original target leg. -/
theorem inherited_basis_target_pullback_leg_iso_symm_hom_postcompose
    {y yi : Yₛ.S} (g : yi ⟶ y) :
    ((inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (f := g)).symm).hom.1 ≫
      (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
        (Functor.Fiber.mk (a := y) rfl) = g := by
  letI : Yₛ.p.IsStronglyCartesian (Yₛ.p.map g)
      ((canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
        (Functor.Fiber.mk (a := y) rfl)) :=
    (canonicalPullbackChoice Yₛ.p).isStronglyCartesian (Yₛ.p.map g)
      (Functor.Fiber.mk (a := y) rfl)
  let ψ : yi ⟶ y := g
  have hψ : Yₛ.p.IsStronglyCartesian (Yₛ.p.map g) ψ := by
    dsimp [ψ]
    exact (inferInstance : IsFibredInGroupoids Yₛ.p).isStronglyCartesian_map g
  letI : Yₛ.p.IsStronglyCartesian (Yₛ.p.map g) g :=
    (inferInstance : IsFibredInGroupoids Yₛ.p).isStronglyCartesian_map g
  haveI : Yₛ.p.IsHomLift (Yₛ.p.map g) ψ := hψ.toIsHomLift
  haveI : Yₛ.p.IsHomLift ((Iso.refl (Yₛ.p.obj yi)).hom ≫ Yₛ.p.map g) ψ := by
    simpa using hψ.toIsHomLift
  letI : Yₛ.p.IsHomLift (Yₛ.p.map g) g :=
    ((inferInstance : IsFibredInGroupoids Yₛ.p).isStronglyCartesian_map g).toIsHomLift
  letI : Yₛ.p.IsHomLift ((Iso.refl (Yₛ.p.obj yi)).hom ≫ Yₛ.p.map g) g := by
    simp
  rw [inherited_basis_target_pullback_leg_iso]
  exact
    @Functor.IsStronglyCartesian.fac _ _ _ _ Yₛ.p
      _ _ _ _ (Yₛ.p.map g)
      ((canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
        (Functor.Fiber.mk (a := y) rfl))
      (by
        exact (canonicalPullbackChoice Yₛ.p).isStronglyCartesian (Yₛ.p.map g)
          (Functor.Fiber.mk (a := y) rfl))
      _ _ ((Iso.refl (Yₛ.p.obj yi)).hom) (Yₛ.p.map g)
      (show Yₛ.p.map g = (Iso.refl (Yₛ.p.obj yi)).hom ≫ Yₛ.p.map g by simp)
      g
      (by
        exact ((inferInstance : IsFibredInGroupoids Yₛ.p).isStronglyCartesian_map g).toIsHomLift)

/-- Helper for Lemma 8.10.5: when the global target comparison is obtained as the preimage of
the componentwise target descent isomorphism, its restriction along the `i`-th cover leg is the
local target comparison component after postcomposition with that leg. -/
theorem inherited_basis_target_preimageIso_component_postcompose
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
    [Functor.Full
      ((canonicalFiberPseudofunctor Yₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i)))]
    [Functor.Faithful
      ((canonicalFiberPseudofunctor Yₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i)))]
    (descentIso :
      let TY :=
        ((canonicalFiberPseudofunctor Yₛ.p).toDescentData
          (fun i ↦ Yₛ.p.map (g i)))
      TY.obj ((fiberFunctor F (Yₛ.p.obj y)).obj x) ≅
        TY.obj (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)))
    (hdescentIso :
      ∀ i,
        let H := StackInGroupoidsOver.Hom.toFibredCategoryMor F
        let pcg := FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i)) x
        let εi : (((canonicalFiberPseudofunctor Xₛ.p).toDescentData
              (fun i ↦ Yₛ.p.map (g i))).obj x).obj i ≅
            ((inherited_basis_simple_forget_to_source_descent_functor
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (Y := Y) (g := g) F).obj D).obj i :=
          { hom := ε.hom.hom i
            inv := ε.inv.hom i
            hom_inv_id := congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ i)
              ε.hom_inv_id
            inv_hom_id := congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ i)
              ε.inv_hom_id }
        descentIso.hom.hom i =
          (pcg ≪≫
            (fiberFunctor F (Yₛ.p.obj (Y i))).mapIso εi ≪≫
              inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i) ≪≫
                (inherited_basis_target_pullback_leg_iso
                  (J := J) (Yₛ := Yₛ) (g i)).symm).hom)
    (i : ι) :
    let TY :=
      ((canonicalFiberPseudofunctor Yₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i)))
    let e := TY.preimageIso descentIso
    (((fiberFunctor F (Yₛ.p.obj (Y i))).map (ε.hom.hom i)).1 ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i)).hom.1) ≫
      g i =
    (SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
        ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i)) x) ≫
      e.hom.1 := by
  intro TY e
  let H := StackInGroupoidsOver.Hom.toFibredCategoryMor F
  let FY := fiberFunctor F (Yₛ.p.obj y)
  let FYi := fiberFunctor F (Yₛ.p.obj (Y i))
  let yBase : Yₛ.p.Fiber (Yₛ.p.obj y) := Functor.Fiber.mk (a := y) rfl
  let Fx := FY.obj x
  let pcg := FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i)) x
  let locD := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i)
  let leg := inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (g i)
  let pbgX := (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i)) x
  let pbFx := (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i)) Fx
  let pbBase := (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i)) yBase
  have hpreimage :
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map
          e.hom) =
        descentIso.hom.hom i := by
    exact congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η i)
      (TY.map_preimage descentIso.hom)
  have hleft :
      ((((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map
          e.hom)).1 ≫ pbBase =
        pbFx ≫ e.hom.1 := by
    simpa [pbBase, pbFx, Fx] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := Yₛ.p.map (g i)) (φ := e.hom)
  have hpcg :
      pcg.hom.1 ≫ H.toHom.map pbgX = pbFx := by
    simpa only [pcg, pbgX, pbFx, H, Fx] using
      FibredCategoryMor.pullbackComparison_hom_postcompose H (Yₛ.p.map (g i)) x
  have hleg :
      leg.symm.hom.1 ≫ pbBase = g i := by
    simpa [leg, pbBase, yBase] using
      inherited_basis_target_pullback_leg_iso_symm_hom_postcompose
        (J := J) (Yₛ := Yₛ) (g i)
  have hcomponent :
      (descentIso.hom.hom i).1 ≫ pbBase =
        (pcg.hom.1 ≫ ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i := by
    have hdesc := hdescentIso i
    rw [hdesc]
    have hraw :
        ((pcg.hom ≫ FYi.map (ε.hom.hom i) ≫ locD.hom ≫
            leg.symm.hom).1) ≫ pbBase =
          (pcg.hom.1 ≫ ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i := by
      change
        (pcg.hom.1 ≫ (FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1 ≫
            leg.symm.hom.1) ≫ pbBase =
          (pcg.hom.1 ≫ ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i
      calc
        (pcg.hom.1 ≫ (FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1 ≫
            leg.symm.hom.1) ≫ pbBase =
          (pcg.hom.1 ≫ ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫
            (leg.symm.hom.1 ≫ pbBase) := by
            simp only [Category.assoc]
        _ = (pcg.hom.1 ≫ ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i := by
            rw [hleg]
            rfl
    simpa only [pcg, FYi, locD, leg, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using hraw
  have hpost :
      pcg.hom.1 ≫ (H.toHom.map pbgX ≫ e.hom.1) =
        pcg.hom.1 ≫ (((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1) ≫ g i) := by
    have h1 :
        pcg.hom.1 ≫ (H.toHom.map pbgX ≫ e.hom.1) =
          (pcg.hom.1 ≫ H.toHom.map pbgX) ≫ e.hom.1 := by
      simp only [Category.assoc]
    have h2 :
        (pcg.hom.1 ≫ H.toHom.map pbgX) ≫ e.hom.1 =
          pbFx ≫ e.hom.1 :=
      congrArg (fun t ↦ t ≫ e.hom.1) hpcg
    have h3 :
        pbFx ≫ e.hom.1 =
          ((((canonicalFiberPseudofunctor Yₛ.p).map
              (Yₛ.p.map (g i)).op.toLoc).toFunctor.map e.hom)).1 ≫ pbBase :=
      hleft.symm
    have h4 :
        ((((canonicalFiberPseudofunctor Yₛ.p).map
              (Yₛ.p.map (g i)).op.toLoc).toFunctor.map e.hom)).1 ≫ pbBase =
          (descentIso.hom.hom i).1 ≫ pbBase :=
      congrArg (fun t ↦ t.1 ≫ pbBase) hpreimage
    have h6 :
        (pcg.hom.1 ≫ ((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1)) ≫ g i =
          pcg.hom.1 ≫ (((FYi.map (ε.hom.hom i)).1 ≫ locD.hom.1) ≫ g i) := by
      simp only [Category.assoc]
    exact h1.trans (h2.trans (h3.trans (h4.trans (hcomponent.trans h6))))
  haveI : IsIso pcg.hom.1 := by
    refine ⟨⟨pcg.inv.1, ?_, ?_⟩⟩
    · simpa only using congrArg (fun η ↦ η.1) pcg.hom_inv_id
    · simpa only using congrArg (fun η ↦ η.1) pcg.inv_hom_id
  apply (cancel_epi pcg.hom.1).1
  exact hpost.symm

/-- Helper for Lemma 8.10.5: pulling back the tautological local target isomorphism is the same
as first passing through the fibred-functor pullback comparison, then through the inherited-source
comparison, and finally through the local target and target-leg comparisons. -/
theorem inherited_basis_target_map_local_target_iso
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {y yi : Yₛ.S} (g : yi ⟶ y) (A : (G F).Fiber y) :
    (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map g).op.toLoc).toFunctor.map
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A).hom) =
      (FibredCategoryMor.pullbackComparison
        (StackInGroupoidsOver.Hom.toFibredCategoryMor F) (Yₛ.p.map g)
        ((inherited_source_fiber_forget (F := F) y).obj A)).hom ≫
        (fiberFunctor F (Yₛ.p.obj yi)).map
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) g A).inv ≫
        (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F
          ((((canonicalFiberPseudofunctor (G F)).map g.op.toLoc).toFunctor.obj A))).hom ≫
        ((inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (f := g)).symm).hom := by
  apply Functor.Fiber.hom_ext
  let sourceA := (inherited_source_fiber_forget (F := F) y).obj A
  let Apull : (G F).Fiber yi :=
    ((canonicalFiberPseudofunctor (G F)).map g.op.toLoc).toFunctor.obj A
  let locA := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F A
  let locAp := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F Apull
  let eA := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) g A
  let pcA := FibredCategoryMor.pullbackComparison
    (StackInGroupoidsOver.Hom.toFibredCategoryMor F) (Yₛ.p.map g) sourceA
  let leg := inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (f := g)
  let H := SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)
  let L :
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map g).op.toLoc).toFunctor.obj
          ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA)) ⟶
        (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map g).op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y))) :=
    (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map g).op.toLoc).toFunctor.map locA.hom)
  let R :
      (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map g).op.toLoc).toFunctor.obj
          ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA)) ⟶
        (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map g).op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y))) :=
    pcA.hom ≫ (fiberFunctor F (Yₛ.p.obj yi)).map eA.inv ≫ locAp.hom ≫ leg.symm.hom
  change L.1 = R.1
  let pbY :=
    (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
      (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y))
  have hpbY : Yₛ.p.IsStronglyCartesian (Yₛ.p.map g) pbY := by
    simpa [pbY] using
      (canonicalPullbackChoice Yₛ.p).isStronglyCartesian (Yₛ.p.map g)
        (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y))
  have hLlift : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj yi)) L.1 := L.2
  have hRlift : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj yi)) R.1 := R.2
  have hLpost :
      L.1 ≫ pbY =
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
            ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA) ≫ locA.hom.1 := by
    simpa [L, pbY, locA, sourceA] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Yₛ.p) (f := Yₛ.p.map g) (φ := locA.hom)
  have hleg : leg.symm.hom.1 ≫ pbY = g := by
    simpa [leg, pbY] using
      inherited_basis_target_pullback_leg_iso_symm_hom_postcompose
        (J := J) (Yₛ := Yₛ) g
  have htarget :
      (G F).map ((canonicalPullbackChoice (G F)).map g A) ≫ locA.hom.1 =
        locAp.hom.1 ≫ g := by
    simpa [Apull, locA, locAp] using
      inherited_basis_local_target_iso_pullback_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F g A
  have heAinv :
      eA.inv.1 ≫ (canonicalPullbackChoice (G F)).map g A =
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA := by
    simpa [eA, sourceA] using
      inherited_source_pullback_comparison_inv_postcompose_owner
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) g A
  have hpc :
      pcA.hom.1 ≫
          H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA) =
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
          ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA) := by
    change
      (FibredCategoryMor.pullbackComparison
          (StackInGroupoidsOver.Hom.toFibredCategoryMor F) (Yₛ.p.map g) sourceA).hom.1 ≫
          H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA) =
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
          ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA)
    exact
      FibredCategoryMor.pullbackComparison_hom_postcompose
        (StackInGroupoidsOver.Hom.toFibredCategoryMor F) (Yₛ.p.map g) sourceA
  have hRpost :
      R.1 ≫ pbY =
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
            ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA) ≫ locA.hom.1 := by
    change
      (pcA.hom.1 ≫ H.map eA.inv.1 ≫ locAp.hom.1 ≫ leg.symm.hom.1) ≫ pbY =
        (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
            ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA) ≫ locA.hom.1
    have h1 :
        (pcA.hom.1 ≫ H.map eA.inv.1 ≫ locAp.hom.1 ≫ leg.symm.hom.1) ≫ pbY =
          pcA.hom.1 ≫ H.map eA.inv.1 ≫ locAp.hom.1 ≫ g := by
      calc
        (pcA.hom.1 ≫ H.map eA.inv.1 ≫ locAp.hom.1 ≫ leg.symm.hom.1) ≫ pbY =
            pcA.hom.1 ≫ H.map eA.inv.1 ≫ locAp.hom.1 ≫
              (leg.symm.hom.1 ≫ pbY) := by
              simp only [Category.assoc]
        _ = pcA.hom.1 ≫ H.map eA.inv.1 ≫ locAp.hom.1 ≫ g := by
              rw [hleg]
              rfl
    have h2 :
        pcA.hom.1 ≫ H.map eA.inv.1 ≫ locAp.hom.1 ≫ g =
          pcA.hom.1 ≫ H.map eA.inv.1 ≫
            (G F).map ((canonicalPullbackChoice (G F)).map g A) ≫ locA.hom.1 := by
      have hmid :=
        congrArg (fun t ↦ pcA.hom.1 ≫ H.map eA.inv.1 ≫ t) htarget.symm
      simpa only [Category.assoc] using hmid
    have h3 :
        pcA.hom.1 ≫ H.map eA.inv.1 ≫
            (G F).map ((canonicalPullbackChoice (G F)).map g A) ≫ locA.hom.1 =
          pcA.hom.1 ≫
            H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA) ≫ locA.hom.1 := by
      change
        pcA.hom.1 ≫ H.map eA.inv.1 ≫
            H.map ((canonicalPullbackChoice (G F)).map g A) ≫ locA.hom.1 =
          pcA.hom.1 ≫
            H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA) ≫ locA.hom.1
      have hmap :
          H.map eA.inv.1 ≫ H.map ((canonicalPullbackChoice (G F)).map g A) =
            H.map (eA.inv.1 ≫ (canonicalPullbackChoice (G F)).map g A) := by
        rw [Functor.map_comp]
      have hcomp :
          H.map (eA.inv.1 ≫ (canonicalPullbackChoice (G F)).map g A) =
            H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA) := by
        rw [heAinv]
        rfl
      have hmapcomp := hmap.trans hcomp
      have hmapcomp' :
          H.map eA.inv.1 ≫ H.map ((canonicalPullbackChoice (G F)).map g A) ≫
              locA.hom.1 =
            H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA) ≫
              locA.hom.1 := by
        simpa using (reassoc_of% hmapcomp) locA.hom.1
      exact congrArg (fun t ↦ pcA.hom.1 ≫ t) hmapcomp'
    have h4 :
        pcA.hom.1 ≫
            H.map ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map g) sourceA) ≫ locA.hom.1 =
          (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map g)
            ((fiberFunctor F (Yₛ.p.obj y)).obj sourceA) ≫ locA.hom.1 := by
      rw [reassoc_of% hpc]
      rfl
    exact h1.trans (h2.trans (h3.trans h4))
  letI : Yₛ.p.IsStronglyCartesian (Yₛ.p.map g) pbY := hpbY
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Yₛ.p _ _ _ _
      (Yₛ.p.map g) pbY inferInstance _ _ (𝟙 (Yₛ.p.obj yi))
      L.1 R.1 hLlift hRlift <| by
        exact hLpost.trans hRpost.symm


end

end CategoryTheory
