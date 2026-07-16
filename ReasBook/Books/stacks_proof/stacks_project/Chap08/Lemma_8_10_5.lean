import stacks_proof.stacks_project.Chap04.Lemma_4_35_17
import stacks_proof.stacks_project.Chap04.Lemma_4_2_18
import stacks_proof.stacks_project.Chap04.Definition_4_2_17
import stacks_proof.stacks_project.Chap04.Definition_4_35_1
import stacks_proof.stacks_project.Chap04.Lemma_4_33_3
import stacks_proof.stacks_project.Chap04.Lemma_4_33_7
import stacks_proof.stacks_project.Chap04.Lemma_4_33_8
import stacks_proof.stacks_project.Chap07.Definition_7_13_1
import stacks_proof.stacks_project.Chap08.Definition_8_2_2
import stacks_proof.stacks_project.Chap08.Definition_8_3_5
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Lemma_8_5_3_PullbackNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_4_2
import stacks_proof.stacks_project.Chap08.Lemma_8_4_4
import stacks_proof.stacks_project.Chap08.Lemma_8_10_1
import stacks_proof.stacks_project.Chap08.Lemma_8_10_4
import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.LiteralBaseDescentLaws
import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.Reconstruction
import Mathlib.Tactic.StacksAttribute

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryOver
open FibredCategoryMor
open Functor IsStronglyCartesian
open Opposite
open StackInGroupoidsOver.Hom

local notation "inheritedTopology" => FibredCategoryOver.inheritedTopologyLocal

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver.{uC, vC, uX, vX} J}

/- Route correction: the stale local shadow block for the target-side gluing and reconstruction
API has been removed. The aggregate file now imports the theorem-local support index and reduces
the inherited stack criterion to the fixed-family descent equivalence below. -/
/-- Helper for Lemma 8.10.5: a fixed displayed family over the target whose projection is a
`J`-cover has effective descent for the canonical fiber pseudofunctor of `G F`. -/
private theorem inherited_basis_fixed_family_toDescentData_isEquivalence
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y)) :
    ((canonicalFiberPseudofunctor (G F)).toDescentData g).IsEquivalence := by
  let TG := ((canonicalFiberPseudofunctor (G F)).toDescentData g)
  have hInheritedCover :
      Sieve.ofArrows Y g ∈ inheritedTopology J Yₛ y :=
    inherited_basis_family_mem_inheritedTopology_of_baseCover
      (J := J) (Yₛ := Yₛ) hbaseCover
  have hCompositeStack : IsStackOnSite J ((G F) ⋙ Yₛ.p) := by
    -- The composite projection is the source-stack projection by the based-functor
    -- compatibility of `F`.
    rw [StackInGroupoidsOver.Hom.comm F]
    infer_instance
  letI : IsStackOnSite J ((G F) ⋙ Yₛ.p) := hCompositeStack
  have hCompositeStackFor :
      (canonicalFiberPseudofunctor ((G F) ⋙ Yₛ.p)).IsStackFor
        ((Sieve.ofArrows Y g).functorPushforward Yₛ.p).arrows :=
    inherited_basis_composite_stackFor_of_baseCover
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F hbaseCover
  have hCompositeFull :
      Functor.Full
        ((canonicalFiberPseudofunctor ((G F) ⋙ Yₛ.p)).toDescentData
          (fun i ↦ Yₛ.p.map (g i))) :=
    inherited_basis_composite_toDescentData_full_of_baseCover
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F hbaseCover
  have hFaithful : Functor.Faithful TG := by
    -- The target-transfer support proves faithfulness by reflecting descent morphisms through
    -- the source-forget descent functor and the source stack descent equivalence.
    simpa [TG] using
      inherited_basis_target_toDescentData_faithful
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F hbaseCover
  letI : Functor.Faithful TG := hFaithful
  have hFull : Functor.Full TG := by
    let SX :=
      ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i)))
    have hSXFull : Functor.Full SX :=
      inherited_basis_source_toDescentData_full
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) hbaseCover
    letI : Functor.Full SX := hSXFull
    constructor
    intro A B φ
    let αXDesc : SX.obj ((inherited_source_fiber_forget (F := F) y).obj A) ⟶
        SX.obj ((inherited_source_fiber_forget (F := F) y).obj B) :=
      { hom := fun i ↦
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A).inv ≫
            (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i) ≫
              (inherited_source_pullback_comparison
                (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) B).hom
        comm := by
          intro Z q i₁ i₂ f₁ f₂ hf₁ hf₂
          simpa [SX, TG, Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
            Functor.map_comp, Category.assoc] using
            inherited_basis_conjugated_ofObj_source_overlap_comm
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
              (A := A) (B := B) φ q f₁ f₂ hf₁ hf₂ }
    let αX := SX.preimage αXDesc
    have hαX :
        ∀ i,
          (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor.map αX) =
            (inherited_source_pullback_comparison
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A).inv ≫
              (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i) ≫
                (inherited_source_pullback_comparison
                  (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) B).hom := by
      intro i
      dsimp [αX]
      exact congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η i)
        (SX.map_preimage αXDesc)
    have htarget :=
      inherited_basis_target_identity_of_source_descent_lift
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F hbaseCover φ αX hαX
    rcases inherited_basis_lift_source_hom_of_target_identity
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F αX htarget with ⟨α, hα⟩
    refine ⟨α, ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    let eA :=
      inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A
    let eB :=
      inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) B
    let sourceMap :=
      ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i)).op.toLoc).toFunctor
    let targetMap :=
      ((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor
    have hForgetFaithful :
        Functor.Faithful (inherited_source_fiber_forget (F := F) (Y i)) :=
      inherited_source_fiber_forget_faithful (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
    letI : Functor.Faithful (inherited_source_fiber_forget (F := F) (Y i)) :=
      hForgetFaithful
    apply (inherited_source_fiber_forget (F := F) (Y i)).map_injective
    change
      (inherited_source_fiber_forget (F := F) (Y i)).map (targetMap.map α) =
        (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i)
    apply (cancel_mono eB.hom).1
    have hnatStep :
        (inherited_source_fiber_forget (F := F) (Y i)).map (targetMap.map α) ≫ eB.hom =
          eA.hom ≫ sourceMap.map ((inherited_source_fiber_forget (F := F) y).map α) := by
      simpa [eA, eB, sourceMap, targetMap] using
        inherited_source_pullback_comparison_naturality_over_vertical
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) α
    have hsourceStep :
        eA.hom ≫ sourceMap.map ((inherited_source_fiber_forget (F := F) y).map α) =
          eA.hom ≫ sourceMap.map αX := by
      rw [hα]
    have hdescStep :
        eA.hom ≫ sourceMap.map αX =
          eA.hom ≫ (eA.inv ≫
            (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i) ≫ eB.hom) := by
      exact congrArg (fun t ↦ eA.hom ≫ t) (hαX i)
    have hcancelStep :
        eA.hom ≫ (eA.inv ≫
            (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i) ≫ eB.hom) =
          (inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i) ≫ eB.hom := by
      rw [← Category.assoc eA.hom eA.inv
        ((inherited_source_fiber_forget (F := F) (Y i)).map (φ.hom i) ≫ eB.hom)]
      rw [eA.hom_inv_id]
      exact Category.id_comp _
    exact hnatStep.trans (hsourceStep.trans (hdescStep.trans hcancelStep))
  letI : Functor.Full TG := hFull
  let forgetToX :=
    inherited_basis_simple_forget_to_source_descent_functor
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (Y := Y) (g := g) F
  let eX :=
    inherited_basis_source_descent_equivalence
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (Y := Y) (g := g) hbaseCover
  let gluedSourceObject :
      ((canonicalFiberPseudofunctor (G F)).DescentData g) →
        Xₛ.p.Fiber (Yₛ.p.obj y) :=
    fun D ↦ eX.inverse.obj (forgetToX.obj D)
  have sourceCounit :
      ∀ D : ((canonicalFiberPseudofunctor (G F)).DescentData g),
        eX.functor.obj (gluedSourceObject D) ≅ forgetToX.obj D := by
    intro D
    exact eX.counitIso.app (forgetToX.obj D)
  have targetComparisonData :
      ∀ D : ((canonicalFiberPseudofunctor (G F)).DescentData g),
        { e : (fiberFunctor F (Yₛ.p.obj y)).obj (gluedSourceObject D) ≅
            (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)) //
          ∀ i,
            (((fiberFunctor F (Yₛ.p.obj (Y i))).map ((sourceCounit D).hom.hom i)).1 ≫
                (inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F
                  (D.obj i)).hom.1) ≫
              g i =
            (SubTwoCategory.Hom.toHom (StackInGroupoidsOver.Hom.toFibredCategoryMor F)).map
                ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map (g i))
                  (gluedSourceObject D)) ≫
              e.hom.1 } := by
    intro D
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
    letI : Functor.Full TY := inferInstance
    letI : Functor.Faithful TY := inferInstance
    let x := gluedSourceObject D
    let ε := sourceCounit D
    let descentIso :
        TY.obj ((fiberFunctor F (Yₛ.p.obj y)).obj x) ≅
          TY.obj (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)) := by
      refine Pseudofunctor.DescentData.isoMk (fun i ↦ ?_) ?_
      · let εi : (eX.functor.obj x).obj i ≅ (forgetToX.obj D).obj i :=
          { hom := ε.hom.hom i
            inv := ε.inv.hom i
            hom_inv_id := by
              exact congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ i)
                ε.hom_inv_id
            inv_hom_id := by
              exact congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ i)
                ε.inv_hom_id }
        exact
          (FibredCategoryMor.pullbackComparison
              (StackInGroupoidsOver.Hom.toFibredCategoryMor F)
              (Yₛ.p.map (g i)) x) ≪≫
            (fiberFunctor F (Yₛ.p.obj (Y i))).mapIso εi ≪≫
              inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i) ≪≫
                (inherited_basis_target_pullback_leg_iso
                  (J := J) (Yₛ := Yₛ) (g i)).symm
      · -- The component isomorphisms are compatible because the source counit is a descent
        -- morphism and the local target identifications of `D` commute with its overlaps.
        intro Z q i₁ i₂ f₁ f₂ hf₁ hf₂
        let yBase : Yₛ.p.Fiber (Yₛ.p.obj y) := Functor.Fiber.mk (a := y) rfl
        let yPull₂ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map
            (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj yBase)
        let yPullf₂ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.obj yPull₂)
        let tail : yPullf₂.1 ⟶ y :=
          (canonicalPullbackChoice Yₛ.p).map f₂ yPull₂ ≫
            (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase
        have htail : Yₛ.p.IsStronglyCartesian q tail := by
          have h1 :
              Yₛ.p.IsStronglyCartesian f₂
                ((canonicalPullbackChoice Yₛ.p).map f₂ yPull₂) := by
            simpa [yPull₂] using
              (canonicalPullbackChoice Yₛ.p).isStronglyCartesian f₂ yPull₂
          have h2 :
              Yₛ.p.IsStronglyCartesian (Yₛ.p.map (g i₂))
                ((canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase) := by
            simpa [yBase] using
              (canonicalPullbackChoice Yₛ.p).isStronglyCartesian
                (Yₛ.p.map (g i₂)) yBase
          have hcomp : Yₛ.p.IsStronglyCartesian (f₂ ≫ Yₛ.p.map (g i₂)) tail := by
            exact @Functor.IsStronglyCartesian.comp C Yₛ.S _ _ Yₛ.p
              Z (Yₛ.p.obj (Y i₂)) (Yₛ.p.obj y)
              yPullf₂.1 yPull₂.1 y
              f₂ (Yₛ.p.map (g i₂))
              ((canonicalPullbackChoice Yₛ.p).map f₂ yPull₂)
              ((canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map (g i₂)) yBase)
              h1 h2
          simpa [tail, hf₂] using hcomp
        letI : Yₛ.p.IsStronglyCartesian q tail := htail
        apply target_fiber_hom_ext_of_cartesian_postcompose
          (J := J) (Yₛ := Yₛ) (tail := tail) q
        have hcanonicalTail :=
          canonical_target_descent_hom_postcompose
            (J := J) (Yₛ := Yₛ) (Y := Y) (g := g) q f₁ f₂ hf₁ hf₂
        have hsourceCounit := ε.hom.comm q f₁ f₂ hf₁ hf₂
        have htargetDescent :=
          inherited_basis_simple_forget_to_source_descent_hom_target_postcompose
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂
        let H := StackInGroupoidsOver.Hom.toFibredCategoryMor F
        let FZ := fiberFunctor F Z
        let FY₁ := fiberFunctor F (Yₛ.p.obj (Y i₁))
        let FY₂ := fiberFunctor F (Yₛ.p.obj (Y i₂))
        let x₁ :=
          (((canonicalFiberPseudofunctor Xₛ.p).map
            (Yₛ.p.map (g i₁)).op.toLoc).toFunctor.obj x)
        let x₂ :=
          (((canonicalFiberPseudofunctor Xₛ.p).map
            (Yₛ.p.map (g i₂)).op.toLoc).toFunctor.obj x)
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
        let pcg₁ := FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i₁)) x
        let pcg₂ := FibredCategoryMor.pullbackComparison H (Yₛ.p.map (g i₂)) x
        let pcf₁ := FibredCategoryMor.pullbackComparison H f₁ x₁
        let pcf₂ := FibredCategoryMor.pullbackComparison H f₂ x₂
        let d₁ := inherited_source_fiber_obj (F := F) (D.obj i₁)
        let d₂ := inherited_source_fiber_obj (F := F) (D.obj i₂)
        let pcfD₁ := FibredCategoryMor.pullbackComparison H f₁ d₁
        let pcfD₂ := FibredCategoryMor.pullbackComparison H f₂ d₂
        let pbD₁ := (canonicalPullbackChoice Xₛ.p).map f₁ d₁
        let pbD₂ := (canonicalPullbackChoice Xₛ.p).map f₂ d₂
        let loc₁ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₁)
        let loc₂ := inherited_basis_local_target_iso (J := J) (Yₛ := Yₛ) F (D.obj i₂)
        let ε₁ := ε.hom.hom i₁
        let ε₂ := ε.hom.hom i₂
        let mapXε₁ :=
          (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map ε₁)
        let mapXε₂ :=
          (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map ε₂)
        let simple :=
          inherited_basis_simple_forget_to_source_descent_hom
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂
        let sourceCan := A₁X.inv.toNatTrans.app x ≫ A₂X.hom.toNatTrans.app x
        have hεF :=
          congrArg (fun η ↦ FZ.map η) hsourceCounit
        have hεFv :
            (FZ.map mapXε₁).1 ≫ (FZ.map simple).1 =
              (FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1 := by
          have hbase :
              FZ.map (mapXε₁ ≫ simple) = FZ.map (sourceCan ≫ mapXε₂) := by
            simpa only [FZ, mapXε₁, mapXε₂, simple, sourceCan, A₁X, A₂X] using hεF
          have h := congrArg (fun η ↦ η.1) hbase
          calc
            (FZ.map mapXε₁).1 ≫ (FZ.map simple).1 =
                (FZ.map (mapXε₁ ≫ simple)).1 := by
                  rw [Functor.map_comp]
                  rfl
            _ = (FZ.map (sourceCan ≫ mapXε₂)).1 := h
            _ = (FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1 := by
                  rw [Functor.map_comp]
                  rfl
        have hpost' :
            (H.toHom.map simple.1 ≫ (H.toHom.map pbD₂ ≫ loc₂.hom.1)) ≫ g i₂ =
              (H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫ g i₁ := by
          simpa only [H, simple, pbD₁, pbD₂, loc₁, loc₂, Category.assoc] using
            htargetDescent
        let Fx := (fiberFunctor F (Yₛ.p.obj y)).obj x
        let leg₁ := inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (g i₁)
        let leg₂ := inherited_basis_target_pullback_leg_iso (J := J) (Yₛ := Yₛ) (g i₂)
        let mapPcg₁ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map pcg₁.hom)
        let mapPcg₂ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map pcg₂.hom)
        let mapEps₁ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map (FY₁.map ε₁))
        let mapEps₂ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map (FY₂.map ε₂))
        let mapLoc₁ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map loc₁.hom)
        let mapLoc₂ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map loc₂.hom)
        let mapLeg₁ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₁.op.toLoc).toFunctor.map leg₁.inv)
        let mapLeg₂ :=
          (((canonicalFiberPseudofunctor Yₛ.p).map f₂.op.toLoc).toFunctor.map leg₂.inv)
        let targetCan :=
          A₁Y.inv.toNatTrans.app Fx ≫ A₂Y.hom.toNatTrans.app Fx
        let baseCan :=
          A₁Y.inv.toNatTrans.app yBase ≫ A₂Y.hom.toNatTrans.app yBase
        let leftFiber := mapPcg₁ ≫ mapEps₁ ≫ mapLoc₁ ≫ mapLeg₁ ≫ baseCan
        let rightFiber := targetCan ≫ mapPcg₂ ≫ mapEps₂ ≫ mapLoc₂ ≫ mapLeg₂
        let pbY₁ := (canonicalPullbackChoice Yₛ.p).map f₁ (FY₁.obj d₁)
        let pbY₂ := (canonicalPullbackChoice Yₛ.p).map f₂ (FY₂.obj d₂)
        have hleftTail :
            (mapLoc₁ ≫ mapLeg₁ ≫ baseCan).1 ≫ tail =
              (pbY₁ ≫ loc₁.hom.1) ≫ g i₁ := by
          simpa only [mapLoc₁, mapLeg₁, baseCan, TY, yBase, yPull₂, tail, A₁Y, A₂Y,
            loc₁, leg₁, pbY₁, FY₁, d₁, Pseudofunctor.toDescentData_obj,
            Pseudofunctor.DescentData.ofObj_hom, Category.assoc] using
            inherited_basis_target_leg_tail_postcompose
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂
        have hrightTail :
            (mapLoc₂ ≫ mapLeg₂).1 ≫ tail =
              (pbY₂ ≫ loc₂.hom.1) ≫ g i₂ := by
          simpa only [mapLoc₂, mapLeg₂, yBase, yPull₂, tail, loc₂, leg₂, pbY₂, FY₂, d₂,
            Category.assoc] using
            inherited_basis_target_leg_direct_tail_postcompose
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D f₂
        have hprefix :
            targetCan ≫ mapPcg₂ ≫ pcf₂.hom =
              mapPcg₁ ≫ pcf₁.hom ≫ FZ.map sourceCan := by
          calc
            targetCan ≫ mapPcg₂ ≫ pcf₂.hom =
                A₁Y.inv.toNatTrans.app Fx ≫ A₂Y.hom.toNatTrans.app Fx ≫ mapPcg₂ ≫
                  pcf₂.hom := by
                    simp only [targetCan, Category.assoc]
            _ = mapPcg₁ ≫ pcf₁.hom ≫ FZ.map sourceCan := by
              simpa only [mapPcg₁, mapPcg₂, H, FZ, x₁, x₂, A₁X, A₂X, A₁Y, A₂Y,
                pcg₁, pcg₂, pcf₁, pcf₂, sourceCan, Fx] using
                inherited_basis_target_pullbackComparison_prefix
                  (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F x q f₁ f₂ hf₁ hf₂
        have hpcfD₁ :
            pcfD₁.hom.1 ≫ H.toHom.map pbD₁ = pbY₁ := by
          simpa only [pcfD₁, H, pbD₁, pbY₁, FY₁, d₁] using
            FibredCategoryMor.pullbackComparison_hom_postcompose H f₁ d₁
        have hpcfD₂ :
            pcfD₂.hom.1 ≫ H.toHom.map pbD₂ = pbY₂ := by
          simpa only [pcfD₂, H, pbD₂, pbY₂, FY₂, d₂] using
            FibredCategoryMor.pullbackComparison_hom_postcompose H f₂ d₂
        have hnat₁ :
            mapEps₁.1 ≫ pcfD₁.hom.1 =
              pcf₁.hom.1 ≫ (FZ.map mapXε₁).1 := by
          have h :=
            FibredCategoryMor.pullbackComparison_naturality_over_vertical H f₁ ε₁
          have h' :
              mapEps₁ ≫ pcfD₁.hom =
                pcf₁.hom ≫ FZ.map mapXε₁ := by
            simpa only [mapEps₁, H, FY₁, FZ, x₁, d₁, ε₁, mapXε₁, pcf₁, pcfD₁] using h
          exact congrArg (fun η ↦ η.1) h'
        have hnat₂ :
            mapEps₂.1 ≫ pcfD₂.hom.1 =
              pcf₂.hom.1 ≫ (FZ.map mapXε₂).1 := by
          have h :=
            FibredCategoryMor.pullbackComparison_naturality_over_vertical H f₂ ε₂
          have h' :
              mapEps₂ ≫ pcfD₂.hom =
                pcf₂.hom ≫ FZ.map mapXε₂ := by
            simpa only [mapEps₂, H, FY₂, FZ, x₂, d₂, ε₂, mapXε₂, pcf₂, pcfD₂] using h
          exact congrArg (fun η ↦ η.1) h'
        have fiber_comp {U : C} {A B C' : Yₛ.p.Fiber U}
            (a : A ⟶ B) (b : B ⟶ C') :
            (a ≫ b).1 = a.1 ≫ b.1 := rfl
        have fiber_map_comp {U : C} {A B C' : Yₛ.p.Fiber U}
            (a : A ⟶ B) (b : B ⟶ C') :
            Functor.Fiber.fiberInclusion.map (a ≫ b) =
              Functor.Fiber.fiberInclusion.map a ≫ Functor.Fiber.fiberInclusion.map b := rfl
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, TY,
          Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
          Functor.map_comp, Category.assoc] at ⊢
        change leftFiber.1 ≫ tail = rightFiber.1 ≫ tail
        have hεFv' :
            (FZ.map mapXε₁).1 ≫ H.toHom.map simple.1 =
              (FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1 := by
          simpa only [FZ, H, simple] using hεFv
        have hprefixv :
            (targetCan ≫ mapPcg₂ ≫ pcf₂.hom).1 =
              (mapPcg₁ ≫ pcf₁.hom ≫ FZ.map sourceCan).1 :=
          congrArg (fun η ↦ η.1) hprefix
        have reassoc6 {A B C' D' E' F' G' : Yₛ.S}
            (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D') (d : D' ⟶ E')
            (e : E' ⟶ F') (f : F' ⟶ G') :
            a ≫ ((b ≫ c) ≫ d) ≫ e ≫ f =
              (a ≫ b ≫ c ≫ d ≫ e) ≫ f := by
          simp only [Category.assoc]
        have reassoc7 {A B C' D' E' F' G' H' : Yₛ.S}
            (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D') (d : D' ⟶ E')
            (e : E' ⟶ F') (f : F' ⟶ G') (h : G' ⟶ H') :
            (a ≫ b ≫ c) ≫ d ≫ e ≫ f ≫ h =
              (a ≫ b ≫ c ≫ d ≫ e ≫ f) ≫ h := by
          simp only [Category.assoc]
        have hleftReduce :
            leftFiber.1 ≫ tail =
              (mapPcg₁.1 ≫ pcf₁.hom.1 ≫ (FZ.map mapXε₁).1 ≫
                H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫ g i₁ := by
          calc
            leftFiber.1 ≫ tail =
                (mapPcg₁.1 ≫ mapEps₁.1 ≫ (mapLoc₁ ≫ mapLeg₁ ≫ baseCan).1) ≫
                  tail := by
                    rfl
            _ = mapPcg₁.1 ≫ mapEps₁.1 ≫
                  ((mapLoc₁ ≫ mapLeg₁ ≫ baseCan).1 ≫ tail) := by
                    simp only [Category.assoc]
            _ = mapPcg₁.1 ≫ mapEps₁.1 ≫ ((pbY₁ ≫ loc₁.hom.1) ≫ g i₁) := by
                    simpa only [Category.assoc] using
                      congrArg (fun t ↦ mapPcg₁.1 ≫ mapEps₁.1 ≫ t) hleftTail
            _ = mapPcg₁.1 ≫ (mapEps₁.1 ≫ pbY₁) ≫ loc₁.hom.1 ≫ g i₁ := by
                    simp only [Category.assoc]
            _ = mapPcg₁.1 ≫ ((mapEps₁.1 ≫ pcfD₁.hom.1) ≫ H.toHom.map pbD₁) ≫
                  loc₁.hom.1 ≫ g i₁ := by
                    calc
                      mapPcg₁.1 ≫ (mapEps₁.1 ≫ pbY₁) ≫ loc₁.hom.1 ≫ g i₁ =
                          mapPcg₁.1 ≫ (mapEps₁.1 ≫
                            (pcfD₁.hom.1 ≫ H.toHom.map pbD₁)) ≫ loc₁.hom.1 ≫ g i₁ := by
                            exact congrArg
                              (fun t ↦ mapPcg₁.1 ≫ (mapEps₁.1 ≫ t) ≫
                                loc₁.hom.1 ≫ g i₁)
                              hpcfD₁.symm
                      _ = mapPcg₁.1 ≫
                            ((mapEps₁.1 ≫ pcfD₁.hom.1) ≫ H.toHom.map pbD₁) ≫
                            loc₁.hom.1 ≫ g i₁ := by
                            exact congrArg
                              (fun t ↦ mapPcg₁.1 ≫ t ≫ loc₁.hom.1 ≫ g i₁)
                              (Category.assoc mapEps₁.1 pcfD₁.hom.1
                                (H.toHom.map pbD₁)).symm
            _ = (mapPcg₁.1 ≫ pcf₁.hom.1 ≫ (FZ.map mapXε₁).1 ≫
                  H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫ g i₁ := by
                    exact
                      (congrArg
                        (fun t ↦ mapPcg₁.1 ≫ (t ≫ H.toHom.map pbD₁) ≫
                          loc₁.hom.1 ≫ g i₁)
                        hnat₁).trans
                        (reassoc6 mapPcg₁.1 pcf₁.hom.1 (FZ.map mapXε₁).1
                          (H.toHom.map pbD₁) loc₁.hom.1 (g i₁))
        have hrightFiber_assoc :
            rightFiber.1 =
              (targetCan ≫ mapPcg₂).1 ≫ mapEps₂.1 ≫ (mapLoc₂ ≫ mapLeg₂).1 := by
          change
            targetCan.1 ≫
                (mapPcg₂.1 ≫ (mapEps₂.1 ≫ (mapLoc₂ ≫ mapLeg₂).1)) =
              (targetCan.1 ≫ mapPcg₂.1) ≫ mapEps₂.1 ≫ (mapLoc₂ ≫ mapLeg₂).1
          rw [← Category.assoc targetCan.1 mapPcg₂.1
            (mapEps₂.1 ≫ (mapLoc₂ ≫ mapLeg₂).1)]
        have hrightReduce :
            rightFiber.1 ≫ tail =
              ((mapPcg₁ ≫ pcf₁.hom ≫ FZ.map sourceCan).1 ≫
                (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫ g i₂ := by
          have hprefixPost :
              ((targetCan ≫ mapPcg₂ ≫ pcf₂.hom).1 ≫
                (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                g i₂ =
              ((mapPcg₁ ≫ pcf₁.hom ≫ FZ.map sourceCan).1 ≫
                (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                g i₂ := by
            exact congrArg
              (fun t ↦ (t ≫ (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫
                loc₂.hom.1) ≫ g i₂)
              hprefixv
          have hrightTarget :
              rightFiber.1 ≫ tail =
                ((targetCan ≫ mapPcg₂ ≫ pcf₂.hom).1 ≫
                  (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                  g i₂ := by
            calc
              rightFiber.1 ≫ tail =
                  ((targetCan ≫ mapPcg₂).1 ≫ mapEps₂.1 ≫
                    (mapLoc₂ ≫ mapLeg₂).1) ≫ tail := by
                      exact congrArg (fun t ↦ t ≫ tail) hrightFiber_assoc
              _ = (targetCan ≫ mapPcg₂).1 ≫ mapEps₂.1 ≫
                    ((mapLoc₂ ≫ mapLeg₂).1 ≫ tail) := by
                      simp only [Category.assoc]
              _ = (targetCan ≫ mapPcg₂).1 ≫ mapEps₂.1 ≫
                    ((pbY₂ ≫ loc₂.hom.1) ≫ g i₂) := by
                      simpa only [Category.assoc] using
                        congrArg (fun t ↦ (targetCan ≫ mapPcg₂).1 ≫
                          mapEps₂.1 ≫ t) hrightTail
              _ = (targetCan ≫ mapPcg₂).1 ≫ (mapEps₂.1 ≫ pbY₂) ≫
                    loc₂.hom.1 ≫ g i₂ := by
                      simp only [Category.assoc]
              _ = (targetCan ≫ mapPcg₂).1 ≫
                    ((mapEps₂.1 ≫ pcfD₂.hom.1) ≫ H.toHom.map pbD₂) ≫
                    loc₂.hom.1 ≫ g i₂ := by
                      calc
                        (targetCan ≫ mapPcg₂).1 ≫ (mapEps₂.1 ≫ pbY₂) ≫
                            loc₂.hom.1 ≫ g i₂ =
                            (targetCan ≫ mapPcg₂).1 ≫
                              (mapEps₂.1 ≫ (pcfD₂.hom.1 ≫ H.toHom.map pbD₂)) ≫
                              loc₂.hom.1 ≫ g i₂ := by
                              exact congrArg
                                (fun t ↦ (targetCan ≫ mapPcg₂).1 ≫
                                  (mapEps₂.1 ≫ t) ≫ loc₂.hom.1 ≫ g i₂)
                                hpcfD₂.symm
                        _ = (targetCan ≫ mapPcg₂).1 ≫
                              ((mapEps₂.1 ≫ pcfD₂.hom.1) ≫ H.toHom.map pbD₂) ≫
                              loc₂.hom.1 ≫ g i₂ := by
                              exact congrArg
                                (fun t ↦ (targetCan ≫ mapPcg₂).1 ≫ t ≫
                                  loc₂.hom.1 ≫ g i₂)
                                (Category.assoc mapEps₂.1 pcfD₂.hom.1
                                  (H.toHom.map pbD₂)).symm
              _ = (targetCan ≫ mapPcg₂).1 ≫
                    ((pcf₂.hom.1 ≫ (FZ.map mapXε₂).1) ≫ H.toHom.map pbD₂) ≫
                    loc₂.hom.1 ≫ g i₂ := by
                      exact congrArg
                        (fun t ↦ (targetCan ≫ mapPcg₂).1 ≫
                          (t ≫ H.toHom.map pbD₂) ≫ loc₂.hom.1 ≫ g i₂)
                        hnat₂
              _ = ((targetCan ≫ mapPcg₂ ≫ pcf₂.hom).1 ≫
                    (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                    g i₂ := by
                        have htargetPrefixValue :
                            (targetCan ≫ mapPcg₂).1 ≫ pcf₂.hom.1 =
                              (targetCan ≫ mapPcg₂ ≫ pcf₂.hom).1 := by
                          change (targetCan.1 ≫ mapPcg₂.1) ≫ pcf₂.hom.1 =
                            targetCan.1 ≫ (mapPcg₂.1 ≫ pcf₂.hom.1)
                          rw [Category.assoc]
                        have htargetAssoc :
                            ((targetCan ≫ mapPcg₂).1 ≫ pcf₂.hom.1 ≫
                              (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫
                              loc₂.hom.1) ≫ g i₂ =
                            (((targetCan ≫ mapPcg₂).1 ≫ pcf₂.hom.1) ≫
                              (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫
                              loc₂.hom.1) ≫ g i₂ := by
                          simp only [Category.assoc]
                        exact
                          (reassoc6 (targetCan ≫ mapPcg₂).1 pcf₂.hom.1
                            (FZ.map mapXε₂).1 (H.toHom.map pbD₂) loc₂.hom.1
                            (g i₂)).trans
                            (htargetAssoc.trans
                              (congrArg
                                (fun t ↦ (t ≫ (FZ.map mapXε₂).1 ≫
                                  H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫ g i₂)
                                htargetPrefixValue))
          exact hrightTarget.trans hprefixPost
        have hsourceTarget :
            ((FZ.map mapXε₁).1 ≫ H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫ g i₁ =
              ((FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫
                loc₂.hom.1) ≫ g i₂ := by
          calc
            ((FZ.map mapXε₁).1 ≫ H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫ g i₁ =
                (FZ.map mapXε₁).1 ≫ ((H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫ g i₁) := by
                  simp only [Category.assoc]
            _ = (FZ.map mapXε₁).1 ≫
                ((H.toHom.map simple.1 ≫ (H.toHom.map pbD₂ ≫ loc₂.hom.1)) ≫
                  g i₂) := by
                  exact congrArg (fun t ↦ (FZ.map mapXε₁).1 ≫ t) hpost'.symm
            _ = ((FZ.map mapXε₁).1 ≫ H.toHom.map simple.1 ≫ H.toHom.map pbD₂ ≫
                  loc₂.hom.1) ≫ g i₂ := by
                  simp only [Category.assoc]
            _ = (((FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1) ≫ H.toHom.map pbD₂ ≫
                  loc₂.hom.1) ≫ g i₂ := by
                  calc
                    ((FZ.map mapXε₁).1 ≫ H.toHom.map simple.1 ≫ H.toHom.map pbD₂ ≫
                        loc₂.hom.1) ≫ g i₂ =
                        (((FZ.map mapXε₁).1 ≫ H.toHom.map simple.1) ≫
                          H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫ g i₂ := by
                          simp only [← Category.assoc]
                    _ = (((FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1) ≫
                          H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫ g i₂ := by
                          exact congrArg
                            (fun t ↦ (t ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫ g i₂)
                            hεFv'
            _ = ((FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫
                  loc₂.hom.1) ≫ g i₂ := by
                  simp only [Category.assoc]
        calc
          leftFiber.1 ≫ tail =
              (mapPcg₁.1 ≫ pcf₁.hom.1 ≫ (FZ.map mapXε₁).1 ≫
                H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫ g i₁ := hleftReduce
          _ = mapPcg₁.1 ≫ pcf₁.hom.1 ≫
                (((FZ.map mapXε₁).1 ≫ H.toHom.map pbD₁ ≫ loc₁.hom.1) ≫
                  g i₁) := by
                simp only [Category.assoc]
          _ = mapPcg₁.1 ≫ pcf₁.hom.1 ≫
                (((FZ.map sourceCan).1 ≫ (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫
                  loc₂.hom.1) ≫ g i₂) := by
                exact congrArg (fun t ↦ mapPcg₁.1 ≫ pcf₁.hom.1 ≫ t) hsourceTarget
          _ = (mapPcg₁.1 ≫ pcf₁.hom.1 ≫ (FZ.map sourceCan).1 ≫
                (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                g i₂ := by
                simp only [Category.assoc]
          _ = ((mapPcg₁ ≫ pcf₁.hom ≫ FZ.map sourceCan).1 ≫
                (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                g i₂ := by
                have hmapPrefixValue :
                    mapPcg₁.1 ≫ (pcf₁.hom.1 ≫ (FZ.map sourceCan).1) =
                      (mapPcg₁ ≫ pcf₁.hom ≫ FZ.map sourceCan).1 := by
                  rfl
                have hmapAssoc :
                    (mapPcg₁.1 ≫ pcf₁.hom.1 ≫ (FZ.map sourceCan).1 ≫
                      (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                      g i₂ =
                    ((mapPcg₁.1 ≫ pcf₁.hom.1 ≫ (FZ.map sourceCan).1) ≫
                      (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫ loc₂.hom.1) ≫
                      g i₂ := by
                  simp only [Category.assoc]
                exact hmapAssoc.trans
                  (congrArg
                    (fun t ↦ (t ≫ (FZ.map mapXε₂).1 ≫ H.toHom.map pbD₂ ≫
                      loc₂.hom.1) ≫ g i₂)
                    hmapPrefixValue)
          _ = rightFiber.1 ≫ tail := hrightReduce.symm
    let e := TY.preimageIso descentIso
    refine ⟨e, ?_⟩
    intro i
    exact
      inherited_basis_target_preimageIso_component_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
        (D := D) (x := x) (ε := ε) (descentIso := descentIso)
        (by
          intro i
          rfl)
        i
  let targetComparison :
      ∀ D : ((canonicalFiberPseudofunctor (G F)).DescentData g),
        (fiberFunctor F (Yₛ.p.obj y)).obj (gluedSourceObject D) ≅
          (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)) :=
    fun D ↦ (targetComparisonData D).1
  let reconstructedObject :
      ((canonicalFiberPseudofunctor (G F)).DescentData g) →
        (G F).Fiber y :=
    fun D ↦
      (((canonicalFiberPseudofunctor (G F)).map (targetComparison D).inv.1.op.toLoc).toFunctor.obj
        (Functor.Fiber.mk (a := (gluedSourceObject D).1) rfl))
  refine
    inherited_basis_toDescentData_isEquivalence_of_objwise_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F reconstructedObject ?_
  intro D
  -- The counit is assembled componentwise from the source counit and target comparison.
  let x := gluedSourceObject D
  let ε := sourceCounit D
  let tc := targetComparison D
  let A := reconstructedObject D
  let αX := inherited_basis_reconstructed_source_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F x tc
  let componentHom :
      ∀ i,
        (((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj A) ⟶
          D.obj i :=
    fun i ↦
      Classical.choose
        (inherited_basis_reconstructed_component_hom_exists
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
          (D := D) (x := x) (ε := ε) (tc := tc)
          ((targetComparisonData D).2) i)
  have hcomponentHom :
      ∀ i,
        (inherited_source_fiber_forget (F := F) (Y i)).map (componentHom i) =
          (inherited_source_pullback_comparison
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A).hom ≫
            (((canonicalFiberPseudofunctor Xₛ.p).map
                (Yₛ.p.map (g i)).op.toLoc).toFunctor.map αX) ≫
              ε.hom.hom i := by
    intro i
    exact
      Classical.choose_spec
        (inherited_basis_reconstructed_component_hom_exists
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
          (D := D) (x := x) (ε := ε) (tc := tc)
          ((targetComparisonData D).2) i)
  let componentIso :
      ∀ i,
        (((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj A) ≅
          D.obj i :=
    fun i ↦
      @asIso ((G F).Fiber (Y i)) _ _ _ (componentHom i)
        (IsFibredInGroupoids.hom_isIso (p := G F) (Y i) (componentHom i))
  refine Pseudofunctor.DescentData.isoMk componentIso ?_
  intro Z q i₁ i₂ f₁ f₂ hf₁ hf₂
  have hForgetFaithful :
      Functor.Faithful (inherited_source_fiber_forget (F := F) Z) :=
    inherited_source_fiber_forget_faithful (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
  letI : Functor.Faithful (inherited_source_fiber_forget (F := F) Z) := hForgetFaithful
  apply (inherited_source_fiber_forget (F := F) Z).map_injective
  let eD₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  apply (cancel_mono eD₂.hom).1
  change
    (inherited_source_fiber_forget (F := F) Z).map
        ((((canonicalFiberPseudofunctor (G F)).map f₁.op.toLoc).toFunctor.map
            (componentHom i₁)) ≫ D.hom q f₁ f₂ hf₁ hf₂) ≫ eD₂.hom =
      (inherited_source_fiber_forget (F := F) Z).map
        (((((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A).hom
            q f₁ f₂ hf₁ hf₂) ≫
          (((canonicalFiberPseudofunctor (G F)).map f₂.op.toLoc).toFunctor.map
            (componentHom i₂))) ≫ eD₂.hom
  exact
    inherited_basis_reconstructed_component_postcancel
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (D := D) (x := x) (ε := ε)
      (A := A) (αX := αX) (componentHom := componentHom)
      (hcomponentHom := hcomponentHom) (q := q) (f₁ := f₁) (f₂ := f₂) hf₁ hf₂

/-- Helper for Lemma 8.10.5: the remaining fixed-cover target descent functor is the exact
coverwise equivalence needed for the inherited-topology stack criterion. -/
private theorem inherited_basis_fixed_cover_toDescentData_isEquivalence
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {y : Yₛ.S} (T : (inheritedTopology J Yₛ).Cover y) :
    ((canonicalFiberPseudofunctor (G F)).toDescentData (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  -- Project the canonical inherited cover to a downstairs `J`-cover and apply the fixed-family
  -- descent theorem to the same arrow family.
  exact
    inherited_basis_fixed_family_toDescentData_isEquivalence
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
      (Y := fun I : T.Arrow ↦ I.Y) (g := fun I : T.Arrow ↦ I.f)
      (inherited_cover_arrow_family_base_covering (J := J) (Yₛ := Yₛ) T)

/-- Helper for Lemma 8.10.5: if `F : Xₛ ⟶ Yₛ` is fibred in groupoids over `Yₛ`, then `G F` is a
stack on the inherited topology on `Yₛ`. -/
theorem isStackOnSiteOverInheritedTopology_of_isFibredInGroupoids
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)] :
    IsStackOnSite (inheritedTopology J Yₛ) (G F) := by
  -- Apply the standard coverwise stack criterion for the inherited topology, reducing the main
  -- theorem to the fixed-cover descent equivalence isolated above.
  refine
    (inheritedTopology_stackOnSite_iff_coverwise_descent
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F).2 ?_
  intro y T
  exact
    inherited_basis_fixed_cover_toDescentData_isEquivalence
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F T

/-- Helper for Lemma 8.10.5: once the inherited-topology stack-on-site owner is available for
`G F`, the ambient fibred-in-groupoids hypothesis upgrades it to a stack in groupoids. -/
private theorem inheritedTopology_isStackInGroupoids_of_stackOnSite
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    [IsStackOnSite (inheritedTopology J Yₛ) (G F)] :
    IsStackInGroupoids (inheritedTopology J Yₛ) (G F) := by
  -- The only remaining datum is the already available fibred-in-groupoids structure on `G F`.
  infer_instance

/- Route correction: keep the first exported wrapper theorems as the canonical owner. The stale
shadow copy below only reintroduced duplicate unfinished declarations, so it has been removed in
favor of the established stack-on-site wrapper plus the standard stack-in-groupoids upgrade. -/
/-- Lemma 8.10.5: let `Xₛ` and `Yₛ` be stacks in groupoids over the site `(C, J)`, and let
`F : Xₛ ⟶ Yₛ` be a `1`-morphism of stacks in groupoids over `(C, J)`. If the underlying functor
`F.G` makes the total category of `Xₛ` into a category fibred in groupoids over the total
category of `Yₛ`, then `F.G` is a stack in groupoids for the topology on `Yₛ` inherited from
`(C, J)`. -/
@[stacks 06NX]
theorem isStackInGroupoidsOverInheritedTopology_of_isFibredInGroupoids
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)] :
    IsStackInGroupoids (inheritedTopology J Yₛ) (G F) := by
  -- Route correction: the exported statement is now just the standard upgrade from the
  -- stack-on-site theorem already isolated above.
  letI : IsStackOnSite (inheritedTopology J Yₛ) (G F) :=
    isStackOnSiteOverInheritedTopology_of_isFibredInGroupoids
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F
  exact
    inheritedTopology_isStackInGroupoids_of_stackOnSite
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F

end

end CategoryTheory
