import StacksProject_2024.Chap08.Lemma_8_10_5.SimpleLiteralForget

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

/-- Helper for Lemma 8.10.5: source stackness gives full faithfulness of the canonical source
descent functor for any displayed family whose projected arrows cover downstairs. -/
theorem inherited_basis_source_toDescentData_fullyFaithful
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y)) :
    Nonempty
      (((canonicalFiberPseudofunctor Xₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i))).FullyFaithful) := by
  let Φ :=
    ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
      (fun i ↦ Yₛ.p.map (g i)))
  have hstackFor :
      (canonicalFiberPseudofunctor Xₛ.p).IsStackFor
        (Presieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i))) := by
    simpa [Φ, Sieve.ofArrows] using
      (canonicalFiberPseudofunctor Xₛ.p).isStackFor'
        (Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)))
        hbaseCover
  have hEquiv : Φ.IsEquivalence :=
    (canonicalFiberPseudofunctor Xₛ.p).isStackFor_ofArrows_iff
      (fun i ↦ Yₛ.p.map (g i)) |>.1 hstackFor
  letI : Φ.IsEquivalence := hEquiv
  exact ⟨Functor.FullyFaithful.ofFullyFaithful Φ⟩

/-- Helper for Lemma 8.10.5: fullness of the canonical source descent functor on a projected
downstairs cover. -/
theorem inherited_basis_source_toDescentData_full
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y)) :
    Functor.Full
      ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i))) := by
  rcases inherited_basis_source_toDescentData_fullyFaithful
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) hbaseCover with ⟨hff⟩
  exact hff.full

/-- Helper for Lemma 8.10.5: faithfulness of the canonical source descent functor on a projected
downstairs cover. -/
theorem inherited_basis_source_toDescentData_faithful
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y)) :
    Functor.Faithful
      ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i))) := by
  rcases inherited_basis_source_toDescentData_fullyFaithful
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) hbaseCover with ⟨hff⟩
  exact hff.faithful

/-- Helper for Lemma 8.10.5: forgetting the target label from a `G F`-fiber is faithful. -/
theorem inherited_source_fiber_forget_faithful
    (F : Xₛ ⟶ Yₛ) {y : Yₛ.S} :
    Functor.Faithful (inherited_source_fiber_forget (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y) := by
  constructor
  intro a b φ ψ h
  apply Functor.Fiber.hom_ext
  exact congrArg (fun η ↦ η.1) h

/-- Helper for Lemma 8.10.5: target descent is faithful over any fixed family whose projection is
a downstairs cover. The proof reflects equality through the source-forget descent functor. -/
theorem inherited_basis_target_toDescentData_faithful
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y)) :
    Functor.Faithful
      ((canonicalFiberPseudofunctor (G F)).toDescentData g) := by
  let TG := ((canonicalFiberPseudofunctor (G F)).toDescentData g)
  let SX :=
    ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
      (fun i ↦ Yₛ.p.map (g i)))
  have hSXFaithful : Functor.Faithful SX :=
    inherited_basis_source_toDescentData_faithful
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) hbaseCover
  letI : Functor.Faithful SX := hSXFaithful
  have hForgetFaithful :
      Functor.Faithful
        (inherited_source_fiber_forget
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y) :=
    inherited_source_fiber_forget_faithful (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
  letI : Functor.Faithful
      (inherited_source_fiber_forget
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y) := hForgetFaithful
  constructor
  intro A B φ ψ hφψ
  apply (inherited_source_fiber_forget
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F y).map_injective
  apply SX.map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  let eA :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A
  let eB :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) B
  let eA' :
      (inherited_source_fiber_forget (F := F) (Y i)).obj
          ((((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj A)) ≅
        (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.obj
          ((inherited_source_fiber_forget (F := F) y).obj A)) := eA
  let eB' :
      (inherited_source_fiber_forget (F := F) (Y i)).obj
          ((((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj B)) ≅
        (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.obj
          ((inherited_source_fiber_forget (F := F) y).obj B)) := eB
  have hlocalGF :
      (inherited_source_fiber_forget (F := F) (Y i)).map
          ((((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.map φ)) =
        (inherited_source_fiber_forget (F := F) (Y i)).map
          ((((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.map ψ)) := by
    have hi := congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η i) hφψ
    simpa [TG] using
      congrArg
        (fun η ↦
          (inherited_source_fiber_forget (F := F) (Y i)).map η)
        hi
  have hnatφ :=
    inherited_source_pullback_comparison_naturality_over_vertical
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) φ
  have hnatψ :=
    inherited_source_pullback_comparison_naturality_over_vertical
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) ψ
  change
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map
      (((inherited_source_fiber_forget (F := F) y).map φ :
        inherited_source_fiber_obj (F := F) A ⟶ inherited_source_fiber_obj (F := F) B))) =
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map
      (((inherited_source_fiber_forget (F := F) y).map ψ :
        inherited_source_fiber_obj (F := F) A ⟶ inherited_source_fiber_obj (F := F) B)))
  apply (cancel_epi eA'.hom).1
  calc
    eA'.hom ≫
        (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) y).map φ)) =
        (inherited_source_fiber_forget (F := F) (Y i)).map
            ((((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.map φ)) ≫
          eB'.hom := by
            simpa [SX, eA, eB, eA', eB'] using hnatφ.symm
    _ =
        (inherited_source_fiber_forget (F := F) (Y i)).map
            ((((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.map ψ)) ≫
          eB'.hom := by
            rw [hlocalGF]
    _ = eA'.hom ≫
        (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) y).map ψ)) := by
            simpa [SX, eA, eB, eA', eB'] using hnatψ

private theorem fiber_eqToIso_hom_val
    {U : C} {x y : Yₛ.p.Fiber U} (h : x.1 = y.1) :
    ((eqToIso (C := Yₛ.p.Fiber U) (Subtype.ext h : x = y)).hom).1 = eqToHom h := by
  cases x with
  | mk xv xp =>
  cases y with
  | mk yv yp =>
  cases h
  rfl

/-- Helper for Lemma 8.10.5: the tautological local target isomorphism is natural for vertical
morphisms in a `G F`-fiber. -/
theorem inherited_basis_local_target_iso_naturality
    (F : Xₛ ⟶ Yₛ) [IsFibredInGroupoids (G F)]
    {z : Yₛ.S} {x y : (G F).Fiber z} (φ : x ⟶ y) :
    (fiberFunctor F (Yₛ.p.obj z)).map ((inherited_source_fiber_forget (F := F) z).map φ) ≫
      (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F y).hom =
    (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F x).hom := by
  apply Functor.Fiber.hom_ext
  dsimp [inherited_source_fiber_forget]
  simp [Functor.Fiber.fiberInclusion, StackInGroupoidsOver.Hom.fiberFunctor]
  let Lx : Yₛ.p.Fiber (Yₛ.p.obj z) :=
    (fiberFunctor F (Yₛ.p.obj z)).obj
      (inherited_source_fiber_obj (F := F) x)
  let Ly : Yₛ.p.Fiber (Yₛ.p.obj z) :=
    (fiberFunctor F (Yₛ.p.obj z)).obj
      (inherited_source_fiber_obj (F := F) y)
  let R : Yₛ.p.Fiber (Yₛ.p.obj z) := Functor.Fiber.mk (a := z) rfl
  have hxval : Lx.1 = R.1 := x.2
  have hyval : Ly.1 = R.1 := y.2
  have hxiso :
      ((inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F x).hom).1 =
        eqToHom hxval := by
    change ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj z)) (Subtype.ext hxval : Lx = R)).hom).1 =
      eqToHom hxval
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) hxval
  have hyiso :
      ((inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F y).hom).1 =
        eqToHom hyval := by
    change ((eqToIso (C := Yₛ.p.Fiber (Yₛ.p.obj z)) (Subtype.ext hyval : Ly = R)).hom).1 =
      eqToHom hyval
    exact fiber_eqToIso_hom_val (Yₛ := Yₛ) hyval
  rw [hxiso, hyiso]
  change (G F).map φ.1 ≫ eqToHom hyval = eqToHom hxval
  letI : (G F).IsHomLift (𝟙 z) φ.1 := φ.2
  have hφ := (IsHomLift.fac' (G F) (𝟙 z) φ.1)
  rw [hφ]
  simp only [Category.id_comp, Category.assoc]
  rw [eqToHom_trans_assoc]
  rw [eqToHom_trans]
  let hdom := IsHomLift.domain_eq (G F) (𝟙 z) φ.1
  let hcod := IsHomLift.codomain_eq (G F) (𝟙 z) φ.1
  change eqToHom (hdom.trans (hcod.symm.trans hyval)) = eqToHom hxval
  rw [show hdom.trans (hcod.symm.trans hyval) = hxval by apply Subsingleton.elim]
  rfl

end

end CategoryTheory
