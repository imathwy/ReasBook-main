import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Example_7_33_8
import stacks_proof.stacks_project.Chap07.Remark_7_35_4
import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategoryBasic
import stacks_proof.stacks_project.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory)
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: localized direct image of sheaves of modules on a ringed site and the induced
  stalk functors at points;
- sampled owner declarations:
  `ringSheaf`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.pushforwardOver`,
  `SheafOfModules.toSheaf`,
  `GrothendieckTopology.Point.sheafFiber`;
- best owner abstraction: the canonical localized direct-image functor
  `SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)` between
  `ringedSiteModuleCategory (J.over U) (𝒪.over U)` and `ringedSiteModuleCategory J 𝒪`;
- primitive data: the structure sheaf `𝒪`, the object `U`, the point `p`, and the localized
  module `𝒢`;
- derived API: the source-facing universal stalk formula obtained by replacing `j_{U!}` with
  `j_{U,*}` in Lemma `18.38.1`, and the global counterexample theorem negating that universal
  statement;
- source/core/bridge triage:
  `source-facing`: the remark that the shriek-style stalk coproduct formula fails for `j_{U,*}`;
  `core/canonical`: `ringSheaf`, `ringedSiteModuleCategory`,
    `SheafOfModules.pushforwardOver`, `SheafOfModules.pushforward`, and
    `SheafOfModules.toSheaf` together with `GrothendieckTopology.Point.sheafFiber`;
  `bridge/view`: the universal formula appearing directly under the outer negation in the theorem
    below.

The previous local aliases for the underlying `RingCat`-valued sheaf, the module category, and
the localized direct image were duplicate wheels of these chapter/mathlib owners, so the public
surface below now uses the canonical declarations directly. -/

/-- Helper for Remark 18.38.2: a universal module-valued stalk formula for `j_{U,*}` would
allow one to recover an equivalence of the underlying generators from an additive isomorphism
between free abelian groups. -/
private theorem freeAbelianIsoInducesEquiv {A B : Type u}
    (h : IsIsomorphic (AddCommGrpCat.free.obj A) (AddCommGrpCat.free.obj B)) :
    Nonempty (A ≃ B) := by
  classical
  let e := Classical.choice h
  let eAdd : FreeAbelianGroup A ≃+ FreeAbelianGroup B := e.addCommGroupIsoToAddEquiv
  -- The standard generator-recovery lemma for free abelian groups turns this additive
  -- equivalence into an equivalence of the generator types.
  exact ⟨Equiv.ofFreeAbelianGroupEquiv eAdd⟩

/-- Helper for Remark 18.38.2: once the witness-side stalk formula has been normalized to a free
abelian-group isomorphism, the original site-level counterexample is contradicted immediately. -/
private theorem freeAbelianIsoContradictsWitness {A B : Type u}
    (hbad : ¬ IsIsomorphic A B)
    (hfree : IsIsomorphic (AddCommGrpCat.free.obj A) (AddCommGrpCat.free.obj B)) :
    False := by
  classical
  obtain ⟨e⟩ := freeAbelianIsoInducesEquiv hfree
  -- The recovered equivalence of generators is exactly the forbidden site-level isomorphism.
  exact hbad ⟨Equiv.toIso e⟩

/-- Helper for Chap18 Remark 18 38 2: a constant sheaf on a singleton type is canonically the
terminal sheaf on any site of set-valued sheaves. -/
private noncomputable def constantSheafSingletonIsoTerminalSheaf
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type u)] (X : Type u) [Unique X] :
    (constantSheaf J (Type u)).obj X ≅
      ⊤_ Sheaf J (Type u) := by
  -- Proof comment: the constant sheaf is the sheafification of the constant presheaf, which is
  -- already a sheaf when the value is terminal.
  let hX : IsTerminal X := (Types.isTerminalEquivUnique X).symm inferInstance
  exact (sheafificationIso (Sheaf.terminal J hX)) ≪≫
    Limits.IsTerminal.uniqueUpToIso (Sheaf.isTerminalTerminal J hX) terminalIsTerminal

/-- Helper for Remark 18.38.2: the additive group `ULift ℤ` is the free abelian group on a
singleton. -/
private noncomputable def uliftIntIsoFreeAbelianPUnit :
    AddCommGrpCat.of (ULift.{u, 0} ℤ) ≅ AddCommGrpCat.free.obj (ULift.{u, 0} PUnit) := by
  let e : ULift.{u, 0} ℤ ≃+ FreeAbelianGroup (ULift.{u, 0} PUnit) :=
    { toFun := fun z ↦ (FreeAbelianGroup.uniqueEquiv (ULift.{u, 0} PUnit)).symm z.down
      invFun := fun g ↦ ULift.up ((FreeAbelianGroup.uniqueEquiv (ULift.{u, 0} PUnit)) g)
      left_inv := fun z ↦ by
        change ULift.up ((FreeAbelianGroup.uniqueEquiv (ULift.{u, 0} PUnit))
          ((FreeAbelianGroup.uniqueEquiv (ULift.{u, 0} PUnit)).symm z.down)) = z
        simp
      right_inv := fun g ↦ by
        simp
      map_add' := fun x y ↦ by
        simp }
  exact e.toAddCommGrpIso

/-- Helper for Remark 18.38.2: pushing forward a sheaf of modules commutes with forgetting to the
underlying additive sheaf. -/
private noncomputable def moduleToSheafPushforwardIso
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    SheafOfModules.pushforward φ ⋙ SheafOfModules.toSheaf S ≅
      SheafOfModules.toSheaf R ⋙ F.sheafPushforwardContinuous AddCommGrpCat.{u} J K :=
  NatIso.ofComponents
    (fun M ↦ eqToIso (by apply ObjectProperty.FullSubcategory.ext; rfl))
    (fun {M N} f ↦ by
      apply (sheafToPresheaf J AddCommGrpCat.{u}).map_injective
      simp only [Functor.comp_map, Functor.map_comp]
      rfl)

/-- Helper for Remark 18.38.2: the constant sheaf of `ULift ℤ`, viewed additively, is the free
abelian-group sheaf on the constant singleton sheaf. -/
private noncomputable def constantIntUnderlyingFreeAbelianIso
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}]
    [J.PreservesSheafification (forget₂ CommRingCat RingCat.{u})]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J RingCat.{u}]
    [J.PreservesSheafification (forget₂ RingCat AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
    [HasWeakSheafify J (Type u)]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.PreservesSheafification AddCommGrpCat.free]
    [J.HasSheafCompose AddCommGrpCat.free] :
    ((sheafCompose J (forget₂ RingCat AddCommGrpCat.{u})).obj
        ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj
          ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (ULift.{u, 0} ℤ))))) ≅
      (sheafCompose J AddCommGrpCat.free).obj
        ((constantSheaf J (Type u)).obj (ULift.{u, 0} PUnit)) := by
  -- Proof comment: both sides are constant additive sheaves, and the underlying additive group of
  -- `ULift ℤ` is canonically the free abelian group on one generator.
  exact (Functor.mapIso (sheafCompose J (forget₂ RingCat AddCommGrpCat.{u}))
      ((constantCommuteCompose J (forget₂ CommRingCat RingCat.{u})).app
        (CommRingCat.of (ULift.{u, 0} ℤ)))) ≪≫
    (constantCommuteCompose J (forget₂ RingCat AddCommGrpCat.{u})).app
      (RingCat.of (ULift.{u, 0} ℤ)) ≪≫
    (Functor.mapIso (constantSheaf J AddCommGrpCat.{u}) uliftIntIsoFreeAbelianPUnit) ≪≫
    ((constantCommuteCompose J AddCommGrpCat.free).app (ULift.{u, 0} PUnit)).symm

/-- Helper for Remark 18.38.2: taking the point-presheaf fiber commutes with the free abelian
group functor. -/
private noncomputable def presheafFiberFreeAbelianIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} [LocallySmall.{u} C]
    (p : GrothendieckTopology.Point.{u} J) (G : Cᵒᵖ ⥤ Type u) :
    p.presheafFiber.obj (G ⋙ AddCommGrpCat.free) ≅
      AddCommGrpCat.free.obj (p.presheafFiber.obj G) :=
  -- Proof comment: the point fiber is a filtered colimit, so the free abelian group functor
  -- commutes with it by the generic `presheafFiberCompIso` bridge.
  (p.presheafFiberCompIso AddCommGrpCat.free).app G

/-- Helper for Remark 18.38.2: the colimit of a discrete `Type`-valued diagram is its sigma type. -/
private noncomputable def discreteColimitIsoSigma {α : Type u} (F : α → Type u) :
    colimit (Discrete.functor F) ≅ Σ a, F a :=
  Limits.coproductIso F

/-- Helper for Remark 18.38.2: a coproduct of free abelian groups is the free abelian group on the
corresponding sigma type. -/
private noncomputable def freeAbelianSigmaIsoCoproduct {α : Type u} (F : α → Type u) :
    (∐ fun a : α ↦ AddCommGrpCat.free.obj (F a)) ≅
      AddCommGrpCat.free.obj (Σ a, F a) := by
  -- Proof comment: this is the canonical coproduct-preservation isomorphism for the free abelian
  -- group functor, specialized to the family `F`.
  exact (PreservesCoproduct.iso AddCommGrpCat.free F).symm ≪≫
    Functor.mapIso AddCommGrpCat.free (discreteColimitIsoSigma F)

/-- Helper for Chap18 Remark 18 38 2: the two-object site used for the localized direct-image
counterexample. -/
private abbrev boolCounterexampleCategory : Type u := ULift.{u, 0} Bool

/-- Helper for Chap18 Remark 18 38 2: the chaotic topology on the two-object counterexample site. -/
private abbrev boolCounterexampleTopology :
    GrothendieckTopology boolCounterexampleCategory := ⊥

/-- Helper for Chap18 Remark 18 38 2: the localization object in the counterexample site. -/
private abbrev boolCounterexampleLocalizationObject : boolCounterexampleCategory := ULift.up false

/-- Helper for Chap18 Remark 18 38 2: the point-supporting object in the counterexample site. -/
private abbrev boolCounterexamplePointObject : boolCounterexampleCategory := ULift.up true

/-- Helper for Chap18 Remark 18 38 2: the point of the chaotic counterexample site. -/
private abbrev boolCounterexamplePoint :
    GrothendieckTopology.Point boolCounterexampleTopology :=
  GrothendieckTopology.pointBot (C := boolCounterexampleCategory) boolCounterexamplePointObject

/-- Helper for Chap18 Remark 18 38 2: the constant singleton sheaf on the localization slice. -/
private abbrev boolCounterexampleTypeSheaf :
    Sheaf (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u) :=
  (constantSheaf (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u)).obj
    (ULift.{u, 0} PUnit)

/-- Helper for Chap18 Remark 18 38 2: the constant `\mathbf Z`-valued structure sheaf on the
counterexample site. -/
private abbrev boolCounterexampleRingSheaf :
    Sheaf boolCounterexampleTopology CommRingCat.{u} :=
  (constantSheaf boolCounterexampleTopology CommRingCat.{u}).obj
    (CommRingCat.of (ULift.{u, 0} ℤ))

/-- Helper for Chap18 Remark 18 38 2: the left-hand stalk type appearing in the site-level
counterexample. -/
private abbrev boolCounterexampleLeftFiberType : Type u :=
  boolCounterexamplePoint.sheafFiber.obj
    (((((Over.forget boolCounterexampleLocalizationObject).morphismOfTopoiInOfCocontinuous
          (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
          boolCounterexampleTopology) _*).obj boolCounterexampleTypeSheaf))

/-- Helper for Chap18 Remark 18 38 2: the right-hand sigma type appearing in the site-level
counterexample. -/
private abbrev boolCounterexampleRightSigmaType : Type u :=
  Σ x : boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject,
    (boolCounterexamplePoint.over x).sheafFiber.obj boolCounterexampleTypeSheaf

/-- Helper for Chap18 Remark 18 38 2: the localization morphism used in the counterexample. -/
private abbrev boolCounterexampleLocalizationMorphism :=
  (Over.forget boolCounterexampleLocalizationObject).morphismOfTopoiInOfCocontinuous
    (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
    boolCounterexampleTopology

/-- Helper for Chap18 Remark 18 38 2: the localized structure sheaf on the slice site. -/
private abbrev boolCounterexampleOverRingSheaf :
    Sheaf (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) CommRingCat.{u} :=
  boolCounterexampleRingSheaf.over boolCounterexampleLocalizationObject

/-- Helper for Chap18 Remark 18 38 2: the unit module over the localized counterexample structure
sheaf. -/
private abbrev boolCounterexampleUnitModule :
    ringedSiteModuleCategory
      (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
      boolCounterexampleOverRingSheaf :=
  SheafOfModules.unit
    (ringSheaf
      (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
      boolCounterexampleOverRingSheaf)

/-- Helper for Chap18 Remark 18 38 2: the additive sheaf obtained by applying free abelian groups
to the singleton counterexample sheaf. -/
private abbrev boolCounterexampleAdditiveSheaf :
    Sheaf (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) AddCommGrpCat.{u} :=
  (sheafCompose (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
    AddCommGrpCat.free).obj boolCounterexampleTypeSheaf

/-- Helper for Remark 18.38.2: the unit module over the counterexample structure sheaf forgets to
the free-abelian-group sheaf on the singleton counterexample sheaf. -/
private theorem boolCounterexampleUnderlyingUnitIso :
    (SheafOfModules.toSheaf
      (ringSheaf
        (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
        boolCounterexampleOverRingSheaf)).obj boolCounterexampleUnitModule ≅
      boolCounterexampleAdditiveSheaf := by
  simpa
    [boolCounterexampleUnitModule, boolCounterexampleAdditiveSheaf, boolCounterexampleTypeSheaf,
      boolCounterexampleRingSheaf, boolCounterexampleOverRingSheaf, ringSheaf, SheafOfModules.unit,
      boolCounterexampleLocalizationObject] using
    constantIntUnderlyingFreeAbelianIso
      (J := boolCounterexampleTopology.over boolCounterexampleLocalizationObject)

/-- Helper for Remark 18.38.2: the left-hand side of the universal module formula specializes to
the free abelian group on the site-level counterexample stalk type. -/
private theorem boolCounterexampleLeftFreeIso :
    ((SheafOfModules.toSheaf (ringSheaf boolCounterexampleTopology boolCounterexampleRingSheaf) ⋙
          boolCounterexamplePoint.sheafFiber).obj
        ((SheafOfModules.pushforward
            (SheafOfModules.pushforwardOver boolCounterexampleLocalizationObject)).obj
          boolCounterexampleUnitModule)) ≅
      AddCommGrpCat.free.obj boolCounterexampleLeftFiberType := by
  letI :
      (boolCounterexampleTopology.over boolCounterexampleLocalizationObject).HasSheafCompose
        (forget₂ RingCat AddCommGrpCat.{u}) := inferInstance
  letI :
      (boolCounterexampleTopology.over boolCounterexampleLocalizationObject).HasSheafCompose
        AddCommGrpCat.free := inferInstance
  letI : boolCounterexampleTopology.HasSheafCompose AddCommGrpCat.free := inferInstance
  have hPushforwardFree :
      (boolCounterexampleLocalizationMorphism _*).obj boolCounterexampleAdditiveSheaf ≅
        (sheafCompose boolCounterexampleTopology AddCommGrpCat.free).obj
          ((boolCounterexampleLocalizationMorphism _*).obj boolCounterexampleTypeSheaf) := by
    refine eqToIso ?_
    apply ObjectProperty.FullSubcategory.ext
    rfl
  let hpush :
      ((SheafOfModules.toSheaf (ringSheaf boolCounterexampleTopology boolCounterexampleRingSheaf) ⋙
            boolCounterexamplePoint.sheafFiber).obj
          ((SheafOfModules.pushforward
              (SheafOfModules.pushforwardOver boolCounterexampleLocalizationObject)).obj
            boolCounterexampleUnitModule)) ≅
        boolCounterexamplePoint.sheafFiber.obj
          ((boolCounterexampleLocalizationMorphism _*).obj
            ((SheafOfModules.toSheaf
                (ringSheaf
                  (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
                  boolCounterexampleOverRingSheaf)).obj
              boolCounterexampleUnitModule)) :=
    boolCounterexamplePoint.sheafFiber.mapIso
      ((moduleToSheafPushforwardIso
          (SheafOfModules.pushforwardOver boolCounterexampleLocalizationObject)).app
        boolCounterexampleUnitModule)
  exact hpush ≪≫
    boolCounterexamplePoint.sheafFiber.mapIso
      ((Functor.mapIso (boolCounterexampleLocalizationMorphism _*) boolCounterexampleUnderlyingUnitIso) ≪≫
        hPushforwardFree) ≪≫
    (boolCounterexamplePoint.sheafFiberCompIso AddCommGrpCat.free).app
      ((boolCounterexampleLocalizationMorphism _*).obj boolCounterexampleTypeSheaf)

/-- Helper for Remark 18.38.2: the right-hand side of the universal module formula specializes to
the free abelian group on the sigma-indexed counterexample type. -/
private theorem boolCounterexampleRightFreeIso :
    (∐ fun x : boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject ↦
        ((SheafOfModules.toSheaf
              (ringSheaf
                (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
                boolCounterexampleOverRingSheaf) ⋙
            (boolCounterexamplePoint.over x).sheafFiber).obj boolCounterexampleUnitModule)) ≅
      AddCommGrpCat.free.obj boolCounterexampleRightSigmaType := by
  letI :
      (boolCounterexampleTopology.over boolCounterexampleLocalizationObject).HasSheafCompose
        (forget₂ RingCat AddCommGrpCat.{u}) := inferInstance
  letI :
      (boolCounterexampleTopology.over boolCounterexampleLocalizationObject).HasSheafCompose
        AddCommGrpCat.free := inferInstance
  have hrightBranch :
      ∀ x : boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject,
        ((SheafOfModules.toSheaf
              (ringSheaf
                (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
                boolCounterexampleOverRingSheaf) ⋙
            (boolCounterexamplePoint.over x).sheafFiber).obj boolCounterexampleUnitModule) ≅
          AddCommGrpCat.free.obj
            ((boolCounterexamplePoint.over x).sheafFiber.obj boolCounterexampleTypeSheaf) := by
    intro x
    exact (boolCounterexamplePoint.over x).sheafFiber.mapIso boolCounterexampleUnderlyingUnitIso ≪≫
      ((boolCounterexamplePoint.over x).sheafFiberCompIso AddCommGrpCat.free).app
        boolCounterexampleTypeSheaf
  exact (Sigma.mapIso hrightBranch) ≪≫
    (by
      simpa [boolCounterexampleRightSigmaType] using
        freeAbelianSigmaIsoCoproduct
          (fun x : boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject ↦
            (boolCounterexamplePoint.over x).sheafFiber.obj boolCounterexampleTypeSheaf))

/-- Helper for Remark 18.38.2: a universal module-valued stalk formula for `j_{U,*}` contradicts
the forbidden site-level witness from Remark `7.35.4`. -/
private theorem boolCounterexampleNotIsomorphic :
    ¬ IsIsomorphic boolCounterexampleLeftFiberType boolCounterexampleRightSigmaType := by
  letI : LocallySmall.{u} boolCounterexampleCategory := inferInstance
  let hG :
      boolCounterexampleTypeSheaf ≅
        ⊤_ Sheaf (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u) := by
    simpa [boolCounterexampleTypeSheaf] using
      constantSheafSingletonIsoTerminalSheaf
        (J := boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
        (ULift.{u, 0} PUnit)
  have hHom :
      IsEmpty (boolCounterexamplePointObject ⟶ boolCounterexampleLocalizationObject) := by
    refine ⟨fun f ↦ ?_⟩
    have hle : boolCounterexamplePointObject.down ≤ boolCounterexampleLocalizationObject.down :=
      f.down.down
    have hfalse : false = true := hle rfl
    cases hfalse
  let _ : IsEmpty (boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject) := by
    refine ⟨fun x ↦ hHom.false ?_⟩
    exact
      (CategoryTheory.shrinkYonedaObjObjEquiv
        (X := boolCounterexampleLocalizationObject) (Y := op boolCounterexamplePointObject)) x
  let hleft :
      boolCounterexampleLeftFiberType ≅
        boolCounterexamplePoint.sheafFiber.obj
          (((((Over.forget boolCounterexampleLocalizationObject).morphismOfTopoiInOfCocontinuous
                (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
                boolCounterexampleTopology) _*).obj
            (⊤_ Sheaf
              (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u)))) :=
    boolCounterexamplePoint.sheafFiber.mapIso
      (Functor.mapIso
        ((((Over.forget boolCounterexampleLocalizationObject).morphismOfTopoiInOfCocontinuous
              (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
              boolCounterexampleTopology) _*)) hG)
  let hright :
      boolCounterexampleRightSigmaType ≅
        (Σ x : boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject,
          (boolCounterexamplePoint.over x).sheafFiber.obj
            (⊤_ Sheaf
              (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u))) :=
    (Equiv.sigmaCongrRight
      fun x ↦ ((boolCounterexamplePoint.over x).sheafFiber.mapIso hG).toEquiv).toIso
  let _ :
      Unique
        (boolCounterexamplePoint.sheafFiber.obj
          (((((Over.forget boolCounterexampleLocalizationObject).morphismOfTopoiInOfCocontinuous
                (boolCounterexampleTopology.over boolCounterexampleLocalizationObject)
                boolCounterexampleTopology) _*).obj
            (⊤_ Sheaf
              (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u))))) := by
    simpa only [Functor.morphismOfTopoiInOfCocontinuous_pushforward] using
      (Types.isTerminalEquivUnique _
        (stalk_terminal_of_terminal_pushforward (J := boolCounterexampleTopology)
          boolCounterexampleLocalizationObject boolCounterexamplePoint))
  let _ :
      IsEmpty
        (Σ x : boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject,
          (boolCounterexamplePoint.over x).sheafFiber.obj
            (⊤_ Sheaf
              (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u))) :=
    sigma_pointOver_isEmpty_of_fiber_isEmpty boolCounterexamplePoint
      boolCounterexampleLocalizationObject
      (⊤_ Sheaf (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u))
  intro h
  obtain ⟨e⟩ := h
  exact (inferInstance :
      IsEmpty
        (Σ x : boolCounterexamplePoint.fiber.obj boolCounterexampleLocalizationObject,
          (boolCounterexamplePoint.over x).sheafFiber.obj
            (⊤_ Sheaf
              (boolCounterexampleTopology.over boolCounterexampleLocalizationObject) (Type u)))).false
    ((hleft.symm ≪≫ e ≪≫ hright).hom default)

/-- Helper for Remark 18.38.2: the universal module-valued formula would force a free abelian-group
isomorphism between the two site-level counterexample types. -/
private theorem boolCounterexampleFreeWitness
    (hall : ∀ {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
        [LocallySmall.{u} C]
        [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
        (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (p : GrothendieckTopology.Point.{u} J)
        (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)),
        IsIsomorphic
          (((SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj
            ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj 𝒢)))
          (∐ fun x : p.fiber.obj U ↦
            ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
                (p.over x).sheafFiber).obj 𝒢))) :
    IsIsomorphic (AddCommGrpCat.free.obj boolCounterexampleLeftFiberType)
      (AddCommGrpCat.free.obj boolCounterexampleRightSigmaType) := by
  -- Proof comment: specialize the universal module statement to the chaotic `Bool` site and then
  -- normalize both sides to free abelian groups on the site-level counterexample types.
  letI : SemilatticeInf boolCounterexampleCategory := inferInstance
  letI : HasBinaryProducts boolCounterexampleCategory := inferInstance
  letI : LocallySmall.{u} boolCounterexampleCategory := inferInstance
  have hspecial :=
    hall
      (C := boolCounterexampleCategory)
      (J := boolCounterexampleTopology)
      (𝒪 := boolCounterexampleRingSheaf)
      (U := boolCounterexampleLocalizationObject)
      (p := boolCounterexamplePoint)
      (𝒢 := boolCounterexampleUnitModule)
  obtain ⟨e⟩ := hspecial
  exact ⟨boolCounterexampleLeftFreeIso.symm ≪≫ e ≪≫ boolCounterexampleRightFreeIso⟩

/-- Helper for Remark 18.38.2: a universal module-valued stalk formula for `j_{U,*}` contradicts
the forbidden site-level witness from Remark `7.35.4`. -/
private theorem moduleUniversalFormulaContradictsSiteWitness
    (hall : ∀ {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
        [LocallySmall.{u} C]
        [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
        (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (p : GrothendieckTopology.Point.{u} J)
        (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)),
        IsIsomorphic
          (((SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj
            ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj 𝒢)))
          (∐ fun x : p.fiber.obj U ↦
            ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
                (p.over x).sheafFiber).obj 𝒢))) :
    False := by
  have hbad0 : ¬ IsIsomorphic boolCounterexampleLeftFiberType boolCounterexampleRightSigmaType :=
    boolCounterexampleNotIsomorphic
  have hfree :
      IsIsomorphic (AddCommGrpCat.free.obj boolCounterexampleLeftFiberType)
        (AddCommGrpCat.free.obj boolCounterexampleRightSigmaType) :=
    boolCounterexampleFreeWitness hall
  exact freeAbelianIsoContradictsWitness hbad0 hfree

/-- Remark 18.38.2: the coproduct decomposition of stalks proved in Lemma `18.38.1` for
`j_{U!}` does not extend to the localization direct-image functor `j_{U,*}`. Equivalently, the
naive statement obtained by replacing `j_{U!}` with `j_{U,*}` in Lemma `18.38.1` is not valid in
general. -/
@[stacks 0711]
theorem ringedSiteLocalizedDirectImage_not_hasShriekStyleStalkFormula
    : ¬ ∀ {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
        [LocallySmall.{u} C]
        [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
        (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (p : GrothendieckTopology.Point.{u} J)
        (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)),
        IsIsomorphic
          (((SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj
            ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj 𝒢)))
          (∐ fun x : p.fiber.obj U ↦
            ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
                (p.over x).sheafFiber).obj 𝒢)) := by
  -- Proof comment: after the route correction above, it is enough to derive a contradiction from
  -- one witness of the site-level failure supplied by Remark `7.35.4`.
  intro hall
  exact moduleUniversalFormulaContradictsSiteWitness hall
