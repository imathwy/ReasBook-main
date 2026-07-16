import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_1_Base
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_5_Bridge
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_5_TowerBridge

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
local notation "F" => sequentialRingSystem A ρ

variable [CategoryWithHomology (SeqRingMod A ρ)]

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

/- Domain-style sampling:
- primary domain: derived inverse limits for varying-ring systems `Mod(ℕ, (A_n))`, compared
  across different realizations of the same stagewise derived tower;
- sampled owner declarations:
  `DerivedModuleTower.Realization`,
  `DerivedModuleTower.stageRestrictionToLimit`,
  `ringedModuleDerivedInverseLimitFunctor`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit`;
- best owner abstraction: the ambient owner for `R \!\varprojlim` is the canonical Chapter 15
  functor `ringedModuleDerivedInverseLimitFunctor A ρ`, while the source-facing data of the remark
  are carried by the bridge/view predicate `DerivedModuleTower.Realization` and the induced
  fixed-base stages `DerivedModuleTower.stageRestrictionToLimit`;
- primitive data: a compatible tower `T : DerivedModuleTower A ρ` and realizations
  `T.Realization M`, `T.Realization N` in `D(Mod(ℕ, (A_n)))`;
- derived API: the canonical fixed-base inverse system `stageRestrictionToLimitTower T`,
  realization-independence of the image under the canonical owner
  `ringedModuleDerivedInverseLimitFunctor A ρ`, and the descended Milnor short exact sequence on
  cohomology; the source does not assert uniqueness of the realizing object itself in
  `D(Mod(ℕ, (A_n)))`.

Source/core/bridge triage:
- `source-facing`: independence of the isomorphism class of `R \!\varprojlim(M)` from the chosen
  realization of the fixed stagewise tower `T`, together with the fact that the Milnor exact
  sequence depends only on `T`;
- `core/canonical`: `ringedModuleDerivedInverseLimitFunctor A ρ`;
- `bridge/view`: `DerivedModuleTower A ρ`, `DerivedModuleTower.Realization`, and
  `DerivedModuleTower.stageRestrictionToLimit`.
-/

namespace DerivedModuleTower

local notation "DModLim" => DerivedCategory (ModuleCat (inverseLimitRing F))
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat (inverseLimitRing F))

local notation:max "R" " lim(" K ")" =>
  Functor.obj (ringedModuleDerivedInverseLimitFunctor (A := A) (ρ := ρ)) K

/-- Helper for Remark 15.88.6: the same tower may be viewed over the canonical stage-ring API of
`F = sequentialRingSystem A ρ`. -/
private theorem asStageRingTower_stepMap
    (T : DerivedModuleTower A ρ) (n : ℕ) :
    T.obj (n + 1) ⟶
      ((show DerivedCategory (ModuleCat (DerivedModuleTower.stageRing F n)) ⥤
          DerivedCategory (ModuleCat (DerivedModuleTower.stageRing F (n + 1))) from
          sequentialRingedModuleTransitionFunctor A ρ n).obj
        (T.obj n)) := by
  -- Proof comment: this is only the definitional identification between the local `(A_n, ρ_n)`
  -- surface and the stage-ring surface attached to `F`.
  simpa [sequentialRingSystem, _root_.DerivedModuleTower.stageRing,
    _root_.DerivedModuleTower.stageTransitionRingHom] using T.stepMap n

/-- Helper for Remark 15.88.6: a local `DerivedModuleTower A ρ` can be fed to the public
stage-restriction owner over `F = sequentialRingSystem A ρ`. -/
private abbrev asStageRingTower
    (T : DerivedModuleTower A ρ) :
    DerivedModuleTower
      (_root_.DerivedModuleTower.stageRing F)
      (_root_.DerivedModuleTower.stageTransitionRingHom F) where
  obj n := T.obj n
  stepMap n := asStageRingTower_stepMap (A := A) (ρ := ρ) T n

/-- Helper for Remark 15.88.6: the limit projections satisfy the same compatibility relation as
the original inverse system maps. -/
private theorem limitProjectionRingHom_comp (n : ℕ) :
    _root_.DerivedModuleTower.limitProjectionRingHom F n =
      (ρ n).comp (_root_.DerivedModuleTower.limitProjectionRingHom F (n + 1)) := by
  -- Proof comment: this is the defining cone compatibility of the inverse limit.
  ext x
  simpa [_root_.DerivedModuleTower.stageTransitionRingHom] using congrArg
    (fun f : limit F ⟶ F.obj (op n) ↦ f x)
    ((limit.w F ((homOfLE (Nat.le_succ n)).op)).symm)

/-- Helper for Remark 15.88.6: evaluate a varying-ring module system at stage `n` and then
restrict scalars to the inverse limit ring `A = \varprojlim_n A_n`. -/
private abbrev fixedBaseLimitEvaluation (n : ℕ) :
    SeqRingMod A ρ ⥤ ModuleCat (inverseLimitRing F) :=
  sequentialRingedModuleEvaluation A ρ n ⋙
    ModuleCat.restrictScalars (_root_.DerivedModuleTower.limitProjectionRingHom F n)

/-- Helper for Remark 15.88.6: the stagewise fixed-base evaluations assemble into a strict tower
of `A`-modules. -/
private abbrev fixedBaseLimitEvaluationStep (n : ℕ) :
    fixedBaseLimitEvaluation (A := A) (ρ := ρ) (n + 1) ⟶
      fixedBaseLimitEvaluation (A := A) (ρ := ρ) n :=
  (Functor.whiskerRight
      (sequentialRingedModuleEvaluationStep A ρ n)
      (ModuleCat.restrictScalars (_root_.DerivedModuleTower.limitProjectionRingHom F (n + 1)))) ≫
    Functor.whiskerLeft (sequentialRingedModuleEvaluation A ρ n)
      ((ModuleCat.restrictScalarsComp'
        (_root_.DerivedModuleTower.limitProjectionRingHom F (n + 1))
        (ρ n)
        (_root_.DerivedModuleTower.limitProjectionRingHom F n)
        (limitProjectionRingHom_comp (A := A) (ρ := ρ) n)).inv)

/-- Helper for Remark 15.88.6: the stagewise fixed-base evaluation is natural in the varying-ring
module object. -/
private theorem fixedBaseLimitTowerFunctor_naturality
    {M N : SeqRingMod A ρ} (f : M ⟶ N) (n : ℕ) :
    (fixedBaseLimitEvaluationStep (A := A) (ρ := ρ) n).app M ≫
        (fixedBaseLimitEvaluation (A := A) (ρ := ρ) n).map f =
      (fixedBaseLimitEvaluation (A := A) (ρ := ρ) (n + 1)).map f ≫
        (fixedBaseLimitEvaluationStep (A := A) (ρ := ρ) n).app N := by
  -- Proof comment: this is exactly naturality of the stage-transition natural transformation.
  simpa using ((fixedBaseLimitEvaluationStep (A := A) (ρ := ρ) n).naturality f).symm

/-- Helper for Remark 15.88.6: the source-faithful strict fixed-base tower functor on
`\mathrm{Mod}(\mathbf N, (A_n))`. -/
private abbrev fixedBaseLimitTowerFunctor :
    SeqRingMod A ρ ⥤ SequentialInverseSystem (ModuleCat (inverseLimitRing F)) where
  obj := ringedModuleLimitTower A ρ
  map f :=
    show ringedModuleLimitTower A ρ _ ⟶ ringedModuleLimitTower A ρ _ from
      NatTrans.ofOpSequence
        (fun n ↦ (fixedBaseLimitEvaluation (A := A) (ρ := ρ) n).map f)
        (fixedBaseLimitTowerFunctor_naturality (A := A) (ρ := ρ) f)
  map_id := by
    intro M
    ext n
    simp [fixedBaseLimitEvaluation]
  map_comp := by
    intro M N P f g
    ext n
    simp [fixedBaseLimitEvaluation]

/-- Helper for Remark 15.88.6: evaluating the strict fixed-base tower functor at stage `n`
recovers the corresponding fixed-base stage evaluation functor. -/
private noncomputable def fixedBaseLimitTowerFunctor_stage_iso (n : ℕ) :
    fixedBaseLimitTowerFunctor (A := A) (ρ := ρ) ⋙
      (evaluation ℕᵒᵖ (ModuleCat (inverseLimitRing F))).obj (op n) ≅
    fixedBaseLimitEvaluation (A := A) (ρ := ρ) n :=
  NatIso.ofComponents
    (fun M ↦ Iso.refl _)
    (fun {_ _} f ↦ by
      -- Proof comment: both functors send `f` to the same stagewise restricted-scalars map.
      simp [fixedBaseLimitTowerFunctor, fixedBaseLimitEvaluation])

/-- Helper for Remark 15.88.6: a natural isomorphism between exact module functors induces the
corresponding objectwise isomorphism on derived categories. -/
private noncomputable theorem mapDerivedCategory_obj_iso_of_natIso
    {R S : Type u} [CommRing R] [CommRing S]
    {F G : ModuleCat R ⥤ ModuleCat S}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory (ModuleCat R)) :
    (F.mapDerivedCategory.obj K) ≅ (G.mapDerivedCategory.obj K) :=
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: compute both derived images through the standard `mapDerivedCategoryFactors`
  -- comparisons and insert the strict natural isomorphism on cochain complexes.
  (F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (F.mapDerivedCategoryFactors.app C) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app C) ≪≫
    (G.mapDerivedCategoryFactors.app C).symm ≪≫
    (G.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K)

/-- Helper for Remark 15.88.6: the derived functor of an exact composite agrees objectwise with
the composite of the induced derived functors. -/
private noncomputable theorem mapDerivedCategory_comp_obj_iso
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (F : ModuleCat R ⥤ ModuleCat S) (G : ModuleCat S ⥤ ModuleCat T)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory (ModuleCat R)) :
    ((F ⋙ G).mapDerivedCategory.obj K) ≅
      (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) :=
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: identify the derived image of the composite by first computing the strict
  -- composite on complexes and then peeling off the two `mapDerivedCategoryFactors` isomorphisms.
  ((F ⋙ G).mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    ((F ⋙ G).mapDerivedCategoryFactors.app C) ≪≫
    (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).symm ≪≫
    (G.mapDerivedCategory).mapIso ((F.mapDerivedCategoryFactors.app C).symm) ≪≫
    (G.mapDerivedCategory).mapIso
      ((F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K))

/-- Helper for Remark 15.88.6: the `n`th stage of the derived image under the strict fixed-base
tower functor matches the canonical `A`-linear stage restriction attached to `M`. -/
private noncomputable def fixedBaseLimitTowerFunctor_stage_component_iso
    (M : DModSeq) (n : ℕ) :
    (stagewiseModuleDerivedLimitTower (A := inverseLimitRing F)
      (((fixedBaseLimitTowerFunctor (A := A) (ρ := ρ)).mapDerivedCategory).obj M)).obj (op n) ≅
      _root_.DerivedModuleTower.stageRestrictionToLimit F
        (asStageRingTower (A := A) (ρ := ρ)
          (_root_.DerivedModuleTower.ofDerivedObject (A := A) (ρ := ρ) M)) n := by
  -- Proof comment: first rewrite stagewise derived evaluation of the derived image as the
  -- derived image of the strict composite `fixedBaseLimitTowerFunctor ⋙ evaluation_n`, then
  -- transport along the strict stagewise identification `fixedBaseLimitTowerFunctor_stage_iso n`.
  simpa [stagewiseModuleDerivedLimitTower, _root_.DerivedModuleTower.stageRestrictionToLimit,
    fixedBaseLimitEvaluation, asStageRingTower, _root_.DerivedModuleTower.ofDerivedObject] using
    ((mapDerivedCategory_comp_obj_iso
        (fixedBaseLimitTowerFunctor (A := A) (ρ := ρ))
        ((evaluation ℕᵒᵖ (ModuleCat (inverseLimitRing F))).obj (op n))
        M).symm ≪≫
      mapDerivedCategory_obj_iso_of_natIso
        (fixedBaseLimitTowerFunctor_stage_iso (A := A) (ρ := ρ) n)
        M)

/-- Helper for Remark 15.88.6: the derived inverse-limit object attached to the strict fixed-base
tower functor is exactly the public Chapter 15 owner `R lim(M)`. -/
private noncomputable def fixedBaseLimitTowerFunctor_derived_inverse_limit_obj_iso
    (M : DModSeq) :
    Functor.obj
      (CategoryTheory.additiveFunctorTotalRightDerived
        (((fixedBaseLimitTowerFunctor (A := A) (ρ := ρ)) ⋙
          (lim : SequentialInverseSystem (ModuleCat (inverseLimitRing F)) ⥤
            ModuleCat (inverseLimitRing F))))) M ≅
      Functor.obj (ringedModuleDerivedInverseLimitFunctor (A := A) (ρ := ρ)) M := by
  -- Proof comment: both sides are the total right derived functor of the same strict
  -- inverse-limit functor, so the comparison is definitional.
  simpa [ringedModuleDerivedInverseLimitFunctor] using
    (Iso.refl
      (Functor.obj
        (CategoryTheory.additiveFunctorTotalRightDerived
          (((fixedBaseLimitTowerFunctor (A := A) (ρ := ρ)) ⋙
            (lim : SequentialInverseSystem (ModuleCat (inverseLimitRing F)) ⥤
              ModuleCat (inverseLimitRing F))))) M))

/-- Helper for Remark 15.88.6: a tower isomorphism induces the canonical isomorphism between the
countable products of its stages. -/
private noncomputable def tower_product_iso
    {Ksys Lsys : SequentialInverseSystem DModLim}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    ∏ᶜ inverseSystemFamily Ksys ≅ ∏ᶜ inverseSystemFamily Lsys := by
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Remark 15.88.6: the product comparison induced by a tower isomorphism projects to
the given stagewise isomorphism. -/
private theorem tower_product_iso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem DModLim}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom := by
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (op m.as)
  -- The product comparison is the limit comparison attached to the stagewise isomorphism `e`.
  simpa [tower_product_iso, eFamily] using
    limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Remark 15.88.6: the product comparison induced by a tower isomorphism intertwines
the Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DModLim}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  -- Proof comment: compare the two Milnor endomorphisms after each projection and use tower
  -- naturality to identify the successor-transition term.
  apply Pi.hom_ext
  intro n
  calc
    ((tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (tower_product_iso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (op (n + 1))).hom ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [tower_product_iso_hom_comp_π]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              (tower_product_iso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (op n)).hom) := by
          -- Naturality identifies the successor-transition contribution.
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
              (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
          rw [Category.assoc, ← tower_product_iso_hom_comp_π, ← Category.assoc]

/-- Helper for Remark 15.88.6: a derived-limit witness transports across an isomorphism of towers
when the limiting object is kept fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem DModLim} {K : DModLim}
    (e : Ksys ≅ Lsys)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Lsys K := by
  rcases hK with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let Tmilnor : Triangle DModLim :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Ttransported : Triangle DModLim :=
    Triangle.mk (ι ≫ (tower_product_iso e).hom) (derivedLimitDifferenceMap Lsys)
      ((tower_product_iso e).inv ≫ δ)
  have hIso : Tmilnor ≅ Ttransported := by
    -- Proof comment: repackage the original Milnor triangle through the product comparison
    -- isomorphism induced by the tower isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) (tower_product_iso e) (tower_product_iso e) ?_ ?_ ?_
    · simp [Tmilnor, Ttransported]
    · simpa [Tmilnor, Ttransported] using (tower_product_iso_hom_comm_difference e).symm
    · simp [Tmilnor, Ttransported]
  have hTtransported : Ttransported ∈ distTriang DModLim := by
    -- Distinguished triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ⟨ι ≫ (tower_product_iso e).hom, (tower_product_iso e).inv ≫ δ, hTtransported⟩⟩

/-- Helper for Remark 15.88.6: once a Milnor triangle is fixed for a tower, the limiting object
may be replaced by any isomorphic object. -/
private theorem isDerivedLimit_of_object_iso
    {Ksys : SequentialInverseSystem DModLim} {L M : DModLim}
    (e : L ≅ M)
    (hL : IsDerivedLimit Ksys L) :
    IsDerivedLimit Ksys M := by
  rcases hL with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let Tmilnor : Triangle DModLim :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Ttransported : Triangle DModLim :=
    Triangle.mk (e.inv ≫ ι) (derivedLimitDifferenceMap Ksys)
      (δ ≫ (shiftFunctor DModLim (1 : ℤ)).map e.hom)
  have hIso : Tmilnor ≅ Ttransported := by
    -- Proof comment: only the first vertex changes, so the comparison triangle is induced by the
    -- chosen isomorphism of limiting objects.
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [Tmilnor, Ttransported]
    · simp [Tmilnor, Ttransported]
    · simp [Tmilnor, Ttransported]
  have hTtransported : Ttransported ∈ distTriang DModLim := by
    -- Proof comment: distinguished triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact
    ⟨hP, ⟨e.inv ≫ ι, δ ≫ (shiftFunctor DModLim (1 : ℤ)).map e.hom, hTtransported⟩⟩

/-- Helper for Remark 15.88.6: the stagewise realization isomorphism induces the corresponding
isomorphism after restricting scalars from `A_n` to `A = \varprojlim_n A_n`. -/
private noncomputable def stageRestrictionToLimit_component_iso
    (T : DerivedModuleTower A ρ) {M : DModSeq}
    (hM : _root_.DerivedModuleTower.Realization T M) (n : ℕ) :
    _root_.DerivedModuleTower.stageRestrictionToLimit F
        (asStageRingTower (A := A) (ρ := ρ)
          (_root_.DerivedModuleTower.ofDerivedObject (A := A) (ρ := ρ) M)) n ≅
      _root_.DerivedModuleTower.stageRestrictionToLimit F
        (asStageRingTower (A := A) (ρ := ρ) T) n := by
  -- Proof comment: each component is just the exact restriction-of-scalars functor applied to the
  -- realization isomorphism at stage `n`.
  simpa [_root_.DerivedModuleTower.stageRestrictionToLimit,
    _root_.DerivedModuleTower.stageRestrictionToBase, asStageRingTower] using
    ((((ModuleCat.restrictScalars (_root_.DerivedModuleTower.limitProjectionRingHom F n))
        .mapDerivedCategory)).mapIso
      (hM.app n))

/-- Helper for Remark 15.88.6: the restricted stagewise realization isomorphisms are compatible
with the successor maps of the two fixed-base towers. -/
private theorem stageRestrictionToLimitTower_component_naturality
    (T : DerivedModuleTower A ρ) {M : DModSeq}
    (hM : _root_.DerivedModuleTower.Realization T M) (n : ℕ) :
    (_root_.DerivedModuleTower.stageRestrictionToLimitTower F
        (asStageRingTower (A := A) (ρ := ρ)
          (_root_.DerivedModuleTower.ofDerivedObject (A := A) (ρ := ρ) M))).map
        ((homOfLE (Nat.le_succ n)).op) ≫
      (stageRestrictionToLimit_component_iso (A := A) (ρ := ρ) T hM n).hom =
        (stageRestrictionToLimit_component_iso (A := A) (ρ := ρ) T hM (n + 1)).hom ≫
          (_root_.DerivedModuleTower.stageRestrictionToLimitTower F
            (asStageRingTower (A := A) (ρ := ρ) T)).map
              ((homOfLE (Nat.le_succ n)).op) := by
  -- Proof comment: unfold the tower successor maps and apply restriction of scalars to the
  -- realization compatibility square.
  simpa [SequentialInverseSystem.stepMap, stageRestrictionToLimit_component_iso,
    _root_.DerivedModuleTower.stageRestrictionToLimitTower,
    _root_.DerivedModuleTower.stageRestrictionToBaseTower,
    _root_.DerivedModuleTower.stageRestrictionToLimit,
    _root_.DerivedModuleTower.stageRestrictionToBase, asStageRingTower, Category.assoc] using
    (hM.naturality n).w

/-- Helper for Remark 15.88.6: the restricted stagewise realization components assemble into a
morphism of fixed-base towers. -/
private noncomputable def stageRestrictionToLimitTower_hom
    (T : DerivedModuleTower A ρ) {M : DModSeq}
    (hM : _root_.DerivedModuleTower.Realization T M) :
    _root_.DerivedModuleTower.stageRestrictionToLimitTower F
        (asStageRingTower (A := A) (ρ := ρ)
          (_root_.DerivedModuleTower.ofDerivedObject (A := A) (ρ := ρ) M)) ⟶
      _root_.DerivedModuleTower.stageRestrictionToLimitTower F
        (asStageRingTower (A := A) (ρ := ρ) T) :=
  NatTrans.ofOpSequence
    (fun n ↦ (stageRestrictionToLimit_component_iso (A := A) (ρ := ρ) T hM n).hom)
    (stageRestrictionToLimitTower_component_naturality (A := A) (ρ := ρ) T hM)

/-- Helper for Remark 15.88.6: a realization identifies the canonical fixed-base tower extracted
from `M` with the fixed-base tower attached to `T`. -/
private noncomputable def stageRestrictionToLimitTower_iso_of_realization
    (T : DerivedModuleTower A ρ) {M : DModSeq}
    (hM : _root_.DerivedModuleTower.Realization T M) :
    _root_.DerivedModuleTower.stageRestrictionToLimitTower F
        (asStageRingTower (A := A) (ρ := ρ)
          (_root_.DerivedModuleTower.ofDerivedObject (A := A) (ρ := ρ) M)) ≅
      _root_.DerivedModuleTower.stageRestrictionToLimitTower F
        (asStageRingTower (A := A) (ρ := ρ) T) :=
  NatIso.ofComponents
    (fun n ↦ stageRestrictionToLimit_component_iso (A := A) (ρ := ρ) T hM (Opposite.unop n))
    (fun {_ _} f ↦ by
      simpa using (stageRestrictionToLimitTower_hom (A := A) (ρ := ρ) T hM).naturality f)

/-- Helper for Remark 15.88.6: the canonical tower extracted from a realization `M` has
`R \!\varprojlim(M)` as a derived limit. -/
private theorem canonical_stageRestrictionToLimitTower_isDerivedLimit
    (M : DModSeq) :
    IsDerivedLimit
      (_root_.DerivedModuleTower.stageRestrictionToLimitTower F
        (asStageRingTower (A := A) (ρ := ρ)
          (_root_.DerivedModuleTower.ofDerivedObject (A := A) (ρ := ρ) M)))
      (R lim(M)) := by
  -- Route correction: the duplicate local stage-restriction API has been removed in favor of the
  -- canonical owner `DerivedModuleTower.stageRestrictionToLimitTower`.
  -- TODO: the objectwise inverse-limit comparison
  -- `fixedBaseLimitTowerFunctor_derived_inverse_limit_obj_iso` and the stagewise component
  -- comparison `fixedBaseLimitTowerFunctor_stage_component_iso` are now available. The remaining
  -- blocker is to package those stage components into a tower isomorphism by proving the single
  -- successor-map compatibility square, and then transport
  -- `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation` across that tower
  -- isomorphism and the object isomorphism.
  sorry

/-- Helper for Remark 15.88.6: a natural isomorphism of sequential inverse systems is already a
pro-isomorphism in the Chapter 4 representative calculus. -/
private theorem ofNatTrans_isProIsomorphism_of_natIso
    {C : Type*} [Category C] {X Y : ℕᵒᵖ ⥤ C} (e : X ≅ Y) :
    (SequentialProObjectMorphismRep.ofNatTrans e.hom).IsProIsomorphism := by
  -- Proof comment: use the inverse natural isomorphism as the reverse representative; with
  -- identity reindexing on both sides, the common-refinement equations reduce to the component
  -- identities of `e`.
  refine ⟨SequentialProObjectMorphismRep.ofNatTrans e.inv, ?_, ?_⟩
  · refine ⟨OrderHom.id, fun n ↦ le_rfl, fun n ↦ le_rfl, ?_⟩
    intro n
    change
      X.map (homOfLE (le_rfl : n ≤ n)).op ≫
          (e.hom.app (Opposite.op n) ≫ e.inv.app (Opposite.op n)) =
        X.map (homOfLE (le_rfl : n ≤ n)).op ≫ 𝟙 (X.obj (Opposite.op n))
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ X.map (homOfLE (le_rfl : n ≤ n)).op ≫ t)
        (e.hom_inv_id_app (Opposite.op n))
  · refine ⟨OrderHom.id, fun n ↦ le_rfl, fun n ↦ le_rfl, ?_⟩
    intro n
    change
      Y.map (homOfLE (le_rfl : n ≤ n)).op ≫
          (e.inv.app (Opposite.op n) ≫ e.hom.app (Opposite.op n)) =
        Y.map (homOfLE (le_rfl : n ≤ n)).op ≫ 𝟙 (Y.obj (Opposite.op n))
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ Y.map (homOfLE (le_rfl : n ≤ n)).op ≫ t)
        (e.inv_hom_id_app (Opposite.op n))

/-- Helper for Remark 15.88.6: a pro-isomorphism representative induces an isomorphism of the
associated sequential pro-objects. -/
private theorem isIso_toProObjectHom_of_isProIsomorphism
    {X Y : ℕᵒᵖ ⥤ DModLim} (a : SequentialProObjectMorphismRep X Y)
    (ha : a.IsProIsomorphism) :
    IsIso a.toProObjectHom := by
  -- Proof comment: evaluate on every test object and use the Chapter 4 bridge from
  -- pro-isomorphisms to bijectivity of the represented Hom-colimit map.
  letI : ∀ Z : DModLim, IsIso (a.toProObjectHom.app Z) := fun Z ↦
    (CategoryTheory.isIso_iff_bijective (a.toProObjectHom.app Z)).2
      (SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective ha Z)
  exact NatIso.isIso_of_isIso_app a.toProObjectHom

/-- Helper for Remark 15.88.6: the identity natural transformation of the common fixed-base
tower yields an isomorphism of the associated pro-object. -/
private theorem identity_stageRestrictionToLimitTower_toProObjectHom_isIso
    (Ksys : ℕᵒᵖ ⥤ DModLim) :
    IsIso ((SequentialProObjectMorphismRep.ofNatTrans (𝟙 Ksys)).toProObjectHom) := by
  -- Proof comment: the identity natural transformation is a natural isomorphism, hence already a
  -- pro-isomorphism, so the induced pro-object morphism is invertible.
  exact
    isIso_toProObjectHom_of_isProIsomorphism
      (SequentialProObjectMorphismRep.ofNatTrans (𝟙 Ksys))
      (ofNatTrans_isProIsomorphism_of_natIso (Iso.refl Ksys))

/-- Remark 15.88.6: if `M` realizes `T`, then the canonical fixed-base inverse system
`stageRestrictionToLimitTower T` in `D(A)` has stage `n` equal to `T.obj n` after restricting
scalars along `A → A_n`, and `R \!\varprojlim(M)` is a derived limit of this actual system. This
is the tower-level form of the observation that `R lim(M)` depends only on `T`. -/
theorem stageRestrictionToLimitTower_isDerivedLimit_of_realization
    (T : DerivedModuleTower A ρ) {M : DModSeq}
    (hM : _root_.DerivedModuleTower.Realization T M) :
    IsDerivedLimit
      (_root_.DerivedModuleTower.stageRestrictionToLimitTower F
        (asStageRingTower (A := A) (ρ := ρ) T))
      (R lim(M)) := by
  -- Proof comment: first handle the canonical tower extracted from `M`, then transport the
  -- derived-limit witness across the realization-induced tower isomorphism.
  exact
    isDerivedLimit_of_tower_iso
      (stageRestrictionToLimitTower_iso_of_realization (A := A) (ρ := ρ) T hM)
      (canonical_stageRestrictionToLimitTower_isDerivedLimit (A := A) (ρ := ρ) M)

-- Proof sketch: use `hM` and `hN` to identify the two stagewise `D(A)`-towers obtained by
-- restricting scalars from the evaluations of `M` and `N` along `A = \varprojlim A_n → A_n`.
-- Each image under `ringedModuleDerivedInverseLimitFunctor A ρ` is then a derived limit of the
-- same canonical fixed-base tower `stageRestrictionToLimitTower T`, so the Chapter 15
-- derived-limit uniqueness theorem yields an
-- isomorphism between the two images. The remark does not assert that `M` and `N` themselves are
-- isomorphic in `D(Mod(ℕ, (A_n)))`.
/-- Remark 15.88.6: if `M` and `N` are two realizations of the same compatible tower
`T : DerivedModuleTower A ρ` from Lemma `15.88.5`, then the isomorphism class of the canonical
Chapter 15 object `R \!\varprojlim(M)` depends only on `T`. Equivalently, `R lim(M)` and
`R lim(N)` are isomorphic in the target derived category over `A = \varprojlim_n A_n`. -/
theorem derivedInverseLimit_isIsomorphic_of_realization
    (T : DerivedModuleTower A ρ) {M N : DModSeq}
    (hM : _root_.DerivedModuleTower.Realization T M)
    (hN : _root_.DerivedModuleTower.Realization T N) :
    IsIsomorphic (R lim(M)) (R lim(N)) := by
  have hMlim :
      IsDerivedLimit
        (_root_.DerivedModuleTower.stageRestrictionToLimitTower F
          (asStageRingTower (A := A) (ρ := ρ) T))
        (R lim(M)) :=
    stageRestrictionToLimitTower_isDerivedLimit_of_realization (A := A) (ρ := ρ) T hM
  have hNlim :
      IsDerivedLimit
        (_root_.DerivedModuleTower.stageRestrictionToLimitTower F
          (asStageRingTower (A := A) (ρ := ρ) T))
        (R lim(N)) :=
    stageRestrictionToLimitTower_isDerivedLimit_of_realization (A := A) (ρ := ρ) T hN
  let Ksys :
      ℕᵒᵖ ⥤ DModLim :=
    _root_.DerivedModuleTower.stageRestrictionToLimitTower F
      (asStageRingTower (A := A) (ρ := ρ) T)
  let η :
      colimit (Ksys.op ⋙ uliftCoyoneda.{0}) ⟶
        proSystemHomColimitFunctor Ksys ⋙ uliftFunctor.{0} :=
    (SequentialProObjectMorphismRep.ofNatTrans (𝟙 Ksys)).toProObjectHom
  letI : IsIso η :=
    identity_stageRestrictionToLimitTower_toProObjectHom_isIso (A := A) (ρ := ρ) Ksys
  -- Proof comment: both chosen `R lim` objects are derived limits of the same fixed-base tower,
  -- so the Chapter 15 uniqueness theorem applied to the identity pro-object yields an invertible
  -- comparison morphism between them.
  obtain ⟨φ, hφ⟩ :=
    CategoryTheory.exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit
      (Ksys := Ksys) (Msys := Ksys) hMlim hNlim η
  exact ⟨asIso φ⟩

end DerivedModuleTower

end
