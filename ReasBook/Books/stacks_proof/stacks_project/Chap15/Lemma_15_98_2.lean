import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_88_1_Base
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Lemma_15_88_5_TowerBridge

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open CommRingCat
open Opposite
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- The sequential inverse system of quotient rings `A / I^(n+1)`. -/
abbrev idealPowerQuotientRingSystem : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  sequentialRingSystem (fun n ↦ A ⧸ I ^ (n + 1))
    (fun n ↦ Ideal.Quotient.factorPowSucc I (n + 1))

local notation "F" => idealPowerQuotientRingSystem I

/-- Each stage ring in the quotient system is naturally an `A`-algebra. -/
instance idealPowerQuotientStageRingAlgebra (n : ℕ) :
    Algebra A (stageRing F n) := by
  change Algebra A (A ⧸ I ^ (n + 1))
  exact RingHom.toAlgebra (Ideal.Quotient.mk (I ^ (n + 1)))

/-- Helper for Lemma 15.98.2: the quotient transition map is compatible with the ambient
`A`-algebra structures on consecutive stages. -/
private theorem idealPowerQuotient_algebraMap_comp (n : ℕ) :
    algebraMap A (stageRing F n) =
      (stageTransitionRingHom F n).comp (algebraMap A (stageRing F (n + 1))) := by
  -- Route correction: after removing the broken `15.98.4` import, we rebuild the tiny quotient
  -- owner API locally and verify the scalar-tower compatibility directly on quotient classes.
  ext x
  change (algebraMap A (A ⧸ I ^ (n + 1))) x =
      ((stageTransitionRingHom F n).comp (algebraMap A (A ⧸ I ^ (n + 2)))) x
  have htransition : stageTransitionRingHom F n = Ideal.Quotient.factorPowSucc I (n + 1) := by
    simp [idealPowerQuotientRingSystem, sequentialRingSystem, stageTransitionRingHom]
  rw [htransition]
  rfl

/-- The stage transition in the quotient system is compatible with the ambient `A`-algebra
structure. -/
instance idealPowerQuotientStageRingIsScalarTower (n : ℕ) :
    IsScalarTower A (stageRing F (n + 1)) (stageRing F n) := by
  exact IsScalarTower.of_algebraMap_eq' (idealPowerQuotient_algebraMap_comp (I := I) n)

/-- A compatible tower of derived quotient stages `K_n ∈ D(A / I^(n+1))`, expressed through the
chapter owner `DerivedModuleTower` specialized to the ideal-power quotient system. -/
abbrev IdealPowerQuotientDerivedTower :=
  DerivedModuleTower (stageRing F) (stageTransitionRingHom F)

/-- Helper for Lemma 15.98.2: the canonical stagewise derived base-change comparison induced by
the tower map `T.stepMap n : K_{n+1} ⟶ K_n` viewed over the successor quotient stage. -/
abbrev stageDerivedBaseChangeComparison
    (T : IdealPowerQuotientDerivedTower I) (n : ℕ) :
    stageDerivedBaseChange F T n ⟶ T.obj n :=
  ((derivedTensorWithAlgebraAdjunction).homEquiv (T.obj (n + 1)) (T.obj n)).symm (T.stepMap n)

namespace CategoryTheory

/-- Helper for Lemma 15.98.2: a natural isomorphism between exact module functors yields the
corresponding objectwise isomorphism on derived categories. -/
noncomputable def mapDerivedCategory_obj_iso_of_natIso
    {R S : Type u} [CommRing R] [CommRing S]
    {F₁ G₁ : ModuleCat R ⥤ ModuleCat S}
    [F₁.Additive] [G₁.Additive]
    [Limits.PreservesFiniteLimits F₁] [Limits.PreservesFiniteColimits F₁]
    [Limits.PreservesFiniteLimits G₁] [Limits.PreservesFiniteColimits G₁]
    (e : F₁ ≅ G₁) (K : DerivedCategory (ModuleCat R)) :
    (F₁.mapDerivedCategory.obj K) ≅ (G₁.mapDerivedCategory.obj K) :=
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: rewrite `K` through a chosen preimage complex, transport the module-functor
  -- natural isomorphism degreewise, and descend back to the derived category.
  (F₁.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (F₁.mapDerivedCategoryFactors.app C) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app C) ≪≫
    (G₁.mapDerivedCategoryFactors.app C).symm ≪≫
    (G₁.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K)

/-- Helper for Lemma 15.98.2: the derived functor of an exact composite agrees objectwise with
the composite of the induced derived functors. -/
noncomputable def mapDerivedCategory_comp_obj_iso
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (F₁ : ModuleCat R ⥤ ModuleCat S) (G₁ : ModuleCat S ⥤ ModuleCat T)
    [F₁.Additive] [G₁.Additive]
    [Limits.PreservesFiniteLimits F₁] [Limits.PreservesFiniteColimits F₁]
    [Limits.PreservesFiniteLimits G₁] [Limits.PreservesFiniteColimits G₁]
    (K : DerivedCategory (ModuleCat R)) :
    ((F₁ ⋙ G₁).mapDerivedCategory.obj K) ≅
      (G₁.mapDerivedCategory.obj (F₁.mapDerivedCategory.obj K)) :=
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: compare both sides on a chosen representing complex, where the composite is
  -- already identified by the two derived-factorization isomorphisms.
  ((F₁ ⋙ G₁).mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    ((F₁ ⋙ G₁).mapDerivedCategoryFactors.app C) ≪≫
    (G₁.mapDerivedCategoryFactors.app ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).symm ≪≫
    (G₁.mapDerivedCategory).mapIso ((F₁.mapDerivedCategoryFactors.app C).symm) ≪≫
    (G₁.mapDerivedCategory).mapIso
      ((F₁.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K))

end CategoryTheory

/- Domain-style sampling for Lemma 15.98.2:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, together with
  pseudo-coherence, derived base change, and derived completeness;
- sampled owner declarations:
  `IdealPowerQuotientDerivedTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChangeComparison`,
  `CategoryTheory.IsDerivedLimit`,
  `IsAdicComplete`,
  `derivedLimit_of_idealPowerQuotientTower_isDerivedComplete`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing specialized tower owner
  `IdealPowerQuotientDerivedTower I` from `Lemma_15_98_4`, together with its canonical fixed-base
  tower `stageRestrictionToBaseTower F A T` and stagewise base-change comparison
  `stageDerivedBaseChangeComparison T n`;
- primitive vs. derived:
  primitive data are the specialized tower `T : IdealPowerQuotientDerivedTower I`, the chosen
  derived-limit object `K : D(A)`, the source-essential adic-completeness hypothesis
  `IsAdicComplete I A`, and the textbook pseudo-coherence/base-change hypotheses on the stages;
  derived API is the pseudo-coherence and derived-completeness conclusion for `K`, together with
  the induced quotient-stage base-change identification.

Source/core/bridge triage:
- `source-facing`: the two theorem statements in this file;
- `core/canonical`: `K.IsPseudoCoherent`, `K.IsDerivedCompleteWithRespectTo I`, and
  `CategoryTheory.IsDerivedLimit`;
- `bridge/view`: `stageRestrictionToBaseTower F A`,
  `stageDerivedBaseChangeComparison`, and the quotient-stage base-change object
  `K ⊗[A]^L[A ⧸ I ^ (n + 1)]`, all reused directly from `Lemma_15_98_4` and
  `Lemma_15_98_5`. -/

/-- Helper for Lemma 15.98.2: every element in a transition kernel of the ideal-power quotient
tower is nilpotent, hence lies in the corresponding nilradical. -/
private theorem idealPowerQuotient_transition_kernel_le_nilradical
    (n : ℕ) :
    RingHom.ker (stageTransitionRingHom F n) ≤ nilradical (stageRing F (n + 1)) := by
  intro x hx
  rcases Ideal.Quotient.mk_surjective x with ⟨a, rfl⟩
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  have ha : a ∈ I ^ (n + 1) := by
    have hx' :
        Ideal.Quotient.factorPowSucc I (n + 1) (Ideal.Quotient.mk (I ^ (n + 2)) a) = 0 := by
      simpa [idealPowerQuotientRingSystem, sequentialRingSystem, stageTransitionRingHom] using hx
    exact Ideal.Quotient.eq_zero_iff_mem.1 hx'
  have hsq_mem_high :
      a ^ 2 ∈ I ^ ((n + 1) + (n + 1)) := by
    simpa [pow_add, pow_two] using (Ideal.mul_mem_mul ha ha : a * a ∈ I ^ (n + 1) * I ^ (n + 1))
  have hsq_mem : a ^ 2 ∈ I ^ (n + 2) := by
    exact
      (Ideal.pow_le_pow_right (show n + 2 ≤ (n + 1) + (n + 1) by omega)) hsq_mem_high
  -- Proof comment: kernel classes come from `I^(n+1)`, so their square already vanishes modulo
  -- `I^(n+2)`.
  simpa [pow_two] using
    (Ideal.Quotient.eq_zero_iff_mem.2 hsq_mem :
      Ideal.Quotient.mk (I ^ (n + 2)) (a ^ 2) = 0)

/-- Helper for Lemma 15.98.2: every element of `I` acts by a sufficiently high zero power on each
restricted quotient stage of the tower. -/
private theorem idealPowerQuotient_stage_power_zero
    (T : IdealPowerQuotientDerivedTower I) {f : A} (hf : f ∈ I) (n : ℕ) :
    ∃ e : ℕ, (f ^ e : A) • 𝟙 ((stageRestrictionToBaseTower F A T).obj (Opposite.op n)) = 0 := by
  let F₀ :=
    (ModuleCat.restrictScalars (algebraMap A (stageRing F n))).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let C := DerivedCategory.Q.objPreimage (T.obj n)
  let eT : DerivedCategory.Q.obj C ≅ T.obj n := DerivedCategory.Q.objObjPreimageIso (T.obj n)
  let eX :
      stageRestrictionToBase F A T n ≅ DerivedCategory.Q.obj (F₀.obj C) :=
    ((ModuleCat.restrictScalars (algebraMap A (stageRing F n))).mapDerivedCategory).mapIso
        eT.symm ≪≫
      (ModuleCat.restrictScalars (algebraMap A (stageRing F n))).mapDerivedCategoryFactors.app C
  have hpow_zero :
      (algebraMap A (stageRing F n)) (f ^ (n + 1)) = 0 := by
    -- Proof comment: `f^(n+1)` lies in `I^(n+1)`, so its class in the `n`th quotient stage is
    -- already zero.
    change Ideal.Quotient.mk (I ^ (n + 1)) (f ^ (n + 1)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hf (n + 1))
  have hcomplex_zero :
      ((f ^ (n + 1) : A) • 𝟙 (F₀.obj C)) = 0 := by
    -- Proof comment: after restricting scalars, the scalar action is multiplication by the image
    -- of `f^(n+1)` in `A / I^(n+1)`, which vanishes by the previous step.
    ext i x
    change (((algebraMap A (stageRing F n)) (f ^ (n + 1)) : stageRing F n) •
        (show C.X i from x)) = 0
    rw [hpow_zero, zero_smul]
  have hderived_zero :
      (f ^ (n + 1) : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C)) = 0 := by
    -- Proof comment: `Q` carries the zero complex endomorphism to zero in the derived category.
    simpa [Functor.map_smul] using congrArg DerivedCategory.Q.map hcomplex_zero
  refine ⟨n + 1, ?_⟩
  -- Proof comment: transport the vanishing scalar action back across the standard comparison
  -- isomorphism between the restricted stage and the strict cochain model.
  calc
    (f ^ (n + 1) : A) • 𝟙 ((stageRestrictionToBaseTower F A T).obj (Opposite.op n)) =
        eX.hom ≫ ((f ^ (n + 1) : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv := by
          change (f ^ (n + 1) : A) • 𝟙 (stageRestrictionToBase F A T n) =
            eX.hom ≫ ((f ^ (n + 1) : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv
          simp [CategoryTheory.Linear.comp_smul, CategoryTheory.Linear.smul_comp]
    _ = 0 := by simp [hderived_zero]

/-- Helper for Lemma 15.98.2: the product of a stagewise zero family of modules is zero. -/
private theorem module_pi_isZero_of_stagewise_isZero
    {R : Type*} [Ring R] (X : ℕ → ModuleCat R)
    (hX : ∀ n : ℕ, IsZero (X n)) :
    IsZero (∏ᶜ X) := by
  -- The identity on the product vanishes because every projection lands in a zero object.
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply Pi.hom_ext
  intro n
  exact (hX n).eq_of_tgt _ _

/-- Helper for Lemma 15.98.2: shifting a chosen product yields a chosen product of the shifted
family. -/
private theorem hasProduct_shift {ι : Type*} (X : ι → DMod) [HasProduct X] (n : ℤ) :
    HasProduct (fun i ↦ (X i)⟦n⟧) := by
  let t :
      IsLimit
        (Fan.mk ((∏ᶜ X)⟦n⟧) (fun i ↦ (Pi.π X i)⟦n⟧')) := by
    simpa using
      (Limits.isLimitOfHasProductOfPreservesLimit (shiftFunctor DMod n) X)
  exact ⟨⟨_, t⟩⟩

/-- Helper for Lemma 15.98.2: applying represented Hom to a product identifies it with the
product of the stagewise represented Hom modules. -/
private noncomputable abbrev preadditiveCoyonedaObj_product_iso
    (L : DMod) (X : ℕ → DMod) [HasProduct X] :
    (preadditiveCoyonedaObj L).obj (∏ᶜ X) ≅
      ∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (X n) :=
  let Z : ℕ → ModuleCat (End L)ᵐᵒᵖ := fun n ↦ (preadditiveCoyonedaObj L).obj (X n)
  (LinearEquiv.ofBijective
      (LinearMap.pi fun n ↦
        ModuleCat.Hom.hom ((preadditiveCoyonedaObj L).map (Pi.π X n))) <| by
        constructor
        · intro f g hfg
          apply Pi.hom_ext
          intro n
          have hfg' := congrArg (fun t : (n : ℕ) → (L ⟶ X n) ↦ t n) hfg
          simpa using hfg'
        · intro x
          refine ⟨Pi.lift fun n ↦ x n, ?_⟩
          ext n
          change (Pi.lift fun n ↦ x n) ≫ Pi.π X n = x n
          rw [Pi.lift_π]).toModuleIso ≪≫
    (ModuleCat.piIsoPi Z).symm

/-- Helper for Lemma 15.98.2: multiplication by a unit scalar on an object is an isomorphism. -/
private theorem isIso_units_smul_id
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (r : Rˣ) (X : C) :
    IsIso ((r : R) • 𝟙 X) := by
  -- Proof comment: the inverse scalar action is multiplication by the inverse unit.
  refine ⟨⟨((↑(r⁻¹) : R) • 𝟙 X), ?_, ?_⟩⟩
  · simpa [smul_smul, Linear.comp_units_smul]
  · simpa [smul_smul, Linear.units_smul_comp]

/-- Helper for Lemma 15.98.2: after restricting scalars from `A_(g^e)` to `A`, the endomorphism
`(g^e) • 𝟙` remains an isomorphism. -/
private theorem localizationAway_power_restrictScalars_smul_id_isIso
    (g : A) (e : ℕ) (E : DerivedCategory (ModuleCat (Localization.Away g))) :
    IsIso
      ((g ^ e : A) •
        𝟙 (((ModuleCat.restrictScalars
          (algebraMap A (Localization.Away g))).mapDerivedCategory.obj E))) := by
  let Fder :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory
  let F₀ :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let C := DerivedCategory.Q.objPreimage E
  let eE : DerivedCategory.Q.obj C ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eX : Fder.obj E ≅ DerivedCategory.Q.obj (F₀.obj C) :=
    Fder.mapIso eE.symm ≪≫ (ModuleCat.restrictScalars
      (algebraMap A (Localization.Away g))).mapDerivedCategoryFactors.app C
  let u : (Localization.Away g)ˣ :=
    (IsLocalization.Away.algebraMap_isUnit g).unit ^ e
  have hcomplex_map :
      F₀.map (((u : Localization.Away g) • 𝟙 C) : C ⟶ C) =
        ((g ^ e : A) • 𝟙 (F₀.obj C)) := by
    -- Proof comment: restriction of scalars sends the localized unit action to the expected
    -- `A`-linear action on the underlying complex.
    ext i x
    rw [Functor.mapHomologicalComplex_map_f]
    let y : C.X i := x
    change (((algebraMap A (Localization.Away g)) g ^ e : Localization.Away g) • y =
      ((algebraMap A (Localization.Away g)) (g ^ e) : Localization.Away g) • y)
    simp [map_pow]
  have hsource_iso :
      IsIso (((u : Localization.Away g) • 𝟙 C) : C ⟶ C) := by
    -- Proof comment: multiplication by a unit is invertible on the concrete preimage complex.
    simpa using
      (isIso_units_smul_id (R := Localization.Away g) u C)
  have hcomplex_iso :
      IsIso (((g ^ e : A) • 𝟙 (F₀.obj C)) : F₀.obj C ⟶ F₀.obj C) := by
    -- Proof comment: mapping preserves the unit-scalar isomorphism at the complex level.
    simpa [hcomplex_map] using
      (Functor.map_isIso F₀
        (((u : Localization.Away g) • 𝟙 C) : C ⟶ C))
  have hderived_iso :
      IsIso
        (((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) :
          DerivedCategory.Q.obj (F₀.obj C) ⟶ DerivedCategory.Q.obj (F₀.obj C)) := by
    -- Proof comment: applying `Q` preserves the complex-level scalar isomorphism.
    simpa [Functor.map_smul] using
      (Functor.map_isIso DerivedCategory.Q
        (((g ^ e : A) • 𝟙 (F₀.obj C)) : F₀.obj C ⟶ F₀.obj C))
  have hconj :
      eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv =
        ((g ^ e : A) • 𝟙 (Fder.obj E)) := by
    -- Proof comment: scalar multiplication commutes with the comparison isomorphism to the
    -- concrete cochain model.
    apply (cancel_mono eX.hom).1
    calc
      (eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv) ≫ eX.hom =
          eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) := by
            simp
      _ =
          (g ^ e : A) • eX.hom := by
            simp [CategoryTheory.Linear.comp_smul]
      _ = ((g ^ e : A) • 𝟙 (Fder.obj E)) ≫ eX.hom := by
            simp [CategoryTheory.Linear.smul_comp]
  -- Proof comment: conjugate the strict-model scalar isomorphism back across `eX`.
  simpa [hconj] using
    (show IsIso
      (eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv) by
        infer_instance)

/-- Helper for Lemma 15.98.2: if `(g^e) • 𝟙` acts by zero on `K`, then every morphism from an
object of `D(A_g)` to `K` vanishes after restriction of scalars. -/
private theorem localizationAwayDerivedHomVanishingCondition_of_power_zero_action
    (g : A) (e : ℕ) (K : DMod)
    (hzero : (g ^ e : A) • 𝟙 K = 0) :
    localizationAwayDerivedHomVanishingCondition g K := by
  intro E
  let Fder :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory
  let X : DMod := Fder.obj E
  have hsourceIso :
      IsIso ((g ^ e : A) • 𝟙 X) :=
    localizationAway_power_restrictScalars_smul_id_isIso g e E
  refine ⟨fun φ ψ ↦ ?_⟩
  have hφ : φ = 0 := by
    -- Route correction: work with the annihilating power `g^e`, whose source action is already
    -- invertible after localization, and cancel it from the left.
    have hφzero : ((g ^ e : A) • 𝟙 X) ≫ φ = 0 := by
      calc
        ((g ^ e : A) • 𝟙 X) ≫ φ = (g ^ e : A) • φ := by
          simp [CategoryTheory.Linear.smul_comp]
        _ = φ ≫ ((g ^ e : A) • 𝟙 K) := by
          simp [CategoryTheory.Linear.comp_smul]
        _ = 0 := by
          rw [hzero]
          simp
    have hcancel :
        inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ φ) = φ := by
      simpa [Category.assoc] using
        (IsIso.inv_hom_id_assoc ((g ^ e : A) • 𝟙 X) φ)
    calc
      φ = inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ φ) := by
        exact hcancel.symm
      _ = inv ((g ^ e : A) • 𝟙 X) ≫ 0 := by
        rw [hφzero]
      _ = 0 := by simp
  have hψ : ψ = 0 := by
    -- Proof comment: the same cancellation argument forces any competing morphism `ψ` to be zero.
    have hψzero : ((g ^ e : A) • 𝟙 X) ≫ ψ = 0 := by
      calc
        ((g ^ e : A) • 𝟙 X) ≫ ψ = (g ^ e : A) • ψ := by
          simp [CategoryTheory.Linear.smul_comp]
        _ = ψ ≫ ((g ^ e : A) • 𝟙 K) := by
          simp [CategoryTheory.Linear.comp_smul]
        _ = 0 := by
          rw [hzero]
          simp
    have hcancel :
        inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ ψ) = ψ := by
      simpa [Category.assoc] using
        (IsIso.inv_hom_id_assoc ((g ^ e : A) • 𝟙 X) ψ)
    calc
      ψ = inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ ψ) := by
        exact hcancel.symm
      _ = inv ((g ^ e : A) • 𝟙 X) ≫ 0 := by
        rw [hψzero]
      _ = 0 := by simp
  simpa [hφ, hψ]

/-- Helper for Lemma 15.98.2: a complex annihilated by powers of each `f ∈ I` is derived
complete with respect to `I`. -/
private theorem stage_isDerivedCompleteWithRespectTo_of_power_zero
    (K : DMod)
    (hpow : ∀ f ∈ I, ∃ e : ℕ, (f ^ e : A) • 𝟙 K = 0) :
    K.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: test derived completeness against each `f ∈ I`; after localizing away from
  -- `f`, the chosen power `f^e` becomes invertible on the source.
  rw [DerivedCategory.isDerivedCompleteWithRespectTo_iff]
  intro f hf
  rcases hpow f hf with ⟨e, he⟩
  exact localizationAwayDerivedHomVanishingCondition_of_power_zero_action f e K he

/-- Helper for Lemma 15.98.2: a derived-complete target has zero represented-Hom module from
any source obtained by restricting scalars from `D(A_f)`. -/
private theorem localized_source_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
    (f : A) (hf : f ∈ I) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    IsZero
      ((preadditiveCoyonedaObj
          (((ModuleCat.restrictScalars
              (algebraMap A (Localization.Away f))).mapDerivedCategory).obj E)).obj K) := by
  let Fder :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := Fder.obj E
  have hsub : Subsingleton (L ⟶ K) := by
    -- Proof comment: derived completeness identifies the Hom-set from the localized source as a
    -- subsingleton.
    simpa [Fder, L] using
      ((DerivedCategory.isDerivedCompleteWithRespectTo_iff K I).1 hK f hf E)
  -- Proof comment: a represented Hom module with subsingleton underlying type is zero.
  change IsZero (ModuleCat.of (End L)ᵐᵒᵖ (L ⟶ K))
  letI : Subsingleton (L ⟶ K) := hsub
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.98.2: derived completeness also kills the shifted represented-Hom module
from any source obtained by restricting scalars from `D(A_f)`. -/
private theorem localized_source_shifted_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
    (f : A) (hf : f ∈ I) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    IsZero
      ((preadditiveCoyonedaObj
          (((ModuleCat.restrictScalars
              (algebraMap A (Localization.Away f))).mapDerivedCategory).obj E)).obj
        (K⟦(-1 : ℤ)⟧)) := by
  let Fder :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := Fder.obj E
  have hshift_source :
      Subsingleton (Fder.obj (E⟦(1 : ℤ)⟧) ⟶ K) := by
    -- Proof comment: apply derived completeness to the shifted source object `E⟦1⟧`.
    exact ((DerivedCategory.isDerivedCompleteWithRespectTo_iff K I).1 hK f hf (E⟦(1 : ℤ)⟧))
  have hshifted : Subsingleton (L⟦(1 : ℤ)⟧ ⟶ K) := by
    let e : Fder.obj (E⟦(1 : ℤ)⟧) ≅ L⟦(1 : ℤ)⟧ := (Fder.commShiftIso (1 : ℤ)).app E
    -- Proof comment: transport the subsingleton statement across the functorial shift
    -- comparison.
    refine ⟨fun g h ↦ ?_⟩
    exact (cancel_epi e.hom).1 (hshift_source.elim (e.hom ≫ g) (e.hom ≫ h))
  have hsub : Subsingleton (L ⟶ K⟦(-1 : ℤ)⟧) := by
    let e :
        (L ⟶ K⟦(-1 : ℤ)⟧) ≃ (L⟦(1 : ℤ)⟧ ⟶ K) :=
      (((shiftEquiv DMod (-1 : ℤ)).symm.toAdjunction.homEquiv L K).symm)
    -- Proof comment: the standard shift adjunction converts the target shift into a source shift.
    refine ⟨fun g h ↦ e.injective (hshifted.elim (e g) (e h))⟩
  change IsZero (ModuleCat.of (End L)ᵐᵒᵖ (L ⟶ K⟦(-1 : ℤ)⟧))
  letI : Subsingleton (L ⟶ K⟦(-1 : ℤ)⟧) := hsub
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.98.2: if every stage is derived complete, then the ordinary represented
Hom tower from a localized source is stagewise zero. -/
private theorem stagewise_represented_hom_isZero_of_stagewise_complete
    (Ksys : ℕᵒᵖ ⥤ DMod) (f : A) (hf : f ∈ I)
    (E : DerivedCategory (ModuleCat (Localization.Away f)))
    (hstage : ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (n : ℕ) :
    let L : DMod :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
    IsZero (((Ksys ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
  let L : DMod :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  -- Proof comment: apply the object-level represented-Hom vanishing to the `n`th stage.
  simpa [L] using
    localized_source_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
      (I := I) f hf (Ksys.obj (op n)) (hstage n) E

/-- Helper for Lemma 15.98.2: if every stage is derived complete, then the shifted represented
Hom tower from a localized source is stagewise zero. -/
private theorem stagewise_shifted_represented_hom_isZero_of_stagewise_complete
    (Ksys : ℕᵒᵖ ⥤ DMod) (f : A) (hf : f ∈ I)
    (E : DerivedCategory (ModuleCat (Localization.Away f)))
    (hstage : ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (n : ℕ) :
    let L : DMod :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
    IsZero ((((Ksys ⋙ shiftFunctor DMod (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
  let L : DMod :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  -- Proof comment: apply the shifted object-level vanishing to the `n`th stage.
  simpa [L] using
    localized_source_shifted_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
      (I := I) f hf (Ksys.obj (op n)) (hstage n) E

/-- Helper for Lemma 15.98.2: any derived limit of a sequential inverse system of
`I`-derived-complete objects is again derived complete with respect to `I`. -/
private theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise
    (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hstage :
      ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: test derived completeness against a fixed localized source and apply exactness
  -- to the inverse-rotated Milnor triangle of the chosen derived-limit witness.
  rw [DerivedCategory.isDerivedCompleteWithRespectTo_iff]
  intro f hf E
  let Fder :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := Fder.obj E
  let Fadd := preadditiveCoyoneda.obj (Opposite.op L)
  rcases hlim with ⟨hprodKsys, ⟨ι, δ, hδ⟩⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hprodKsys
  have hright_stage :
      ∀ n : ℕ, IsZero (((Ksys ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
    intro n
    simpa [Fder, L] using
      stagewise_represented_hom_isZero_of_stagewise_complete
        (I := I) Ksys f hf E hstage n
  have hleft_stage :
      ∀ n : ℕ,
        IsZero ((((Ksys ⋙ shiftFunctor DMod (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L).obj
          (op n))) := by
    intro n
    simpa [Fder, L] using
      stagewise_shifted_represented_hom_isZero_of_stagewise_complete
        (I := I) Ksys f hf E hstage n
  have hright_product_module :
      IsZero ((preadditiveCoyonedaObj L).obj (∏ᶜ inverseSystemFamily Ksys)) := by
    have hpi :
        IsZero
          (∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (Ksys.obj (op n))) := by
      -- Proof comment: the unshifted represented-Hom product is zero because each stage is zero.
      refine (IsZero.iff_id_eq_zero _).2 ?_
      apply Pi.hom_ext
      intro n
      exact (hright_stage n).eq_of_tgt _ _
    exact hpi.of_iso
      (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily Ksys))
  let shiftedFamily : ℕ → DMod := fun n ↦ (Ksys.obj (op n))⟦(-1 : ℤ)⟧
  letI : HasProduct shiftedFamily := hasProduct_shift (inverseSystemFamily Ksys) (-1 : ℤ)
  have hleft_product_module :
      IsZero ((preadditiveCoyonedaObj L).obj ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧)) := by
    have hpi :
        IsZero (∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (shiftedFamily n)) := by
      -- Proof comment: the same product argument works after shifting the tower stages.
      refine (IsZero.iff_id_eq_zero _).2 ?_
      apply Pi.hom_ext
      intro n
      exact (hleft_stage n).eq_of_tgt _ _
    have hshifted_product :
        IsZero ((preadditiveCoyonedaObj L).obj (∏ᶜ shiftedFamily)) := by
      exact hpi.of_iso
        (preadditiveCoyonedaObj_product_iso L shiftedFamily)
    let e :
        ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧) ≅
          ∏ᶜ shiftedFamily :=
      PreservesProduct.iso (shiftFunctor DMod (-1 : ℤ)) (inverseSystemFamily Ksys)
    exact hshifted_product.of_iso ((preadditiveCoyonedaObj L).mapIso e)
  have hright_product :
      IsZero (Fadd.obj (∏ᶜ inverseSystemFamily Ksys)) := by
    simpa [Fadd] using
      (forget₂ (ModuleCat (End L)ᵐᵒᵖ) AddCommGrpCat).map_isZero hright_product_module
  have hleft_product :
      IsZero (Fadd.obj ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧)) := by
    simpa [Fadd] using
      (forget₂ (ModuleCat (End L)ᵐᵒᵖ) AddCommGrpCat).map_isZero hleft_product_module
  let T : Triangle DMod := Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let S :=
    (shortComplexOfDistTriangle T.invRotate (inv_rot_of_distTriang _ hδ)).map Fadd
  have hmiddle_add : IsZero S.X₂ := by
    have hexact : S.Exact := by
      -- Proof comment: represented Hom sends the inverse-rotated Milnor triangle to an exact
      -- sequence in additive groups.
      simpa [S] using Fadd.map_distinguished_exact T.invRotate (inv_rot_of_distTriang _ hδ)
    -- Proof comment: the middle term vanishes because both outer terms are already zero.
    refine hexact.isZero_X₂ ?_ ?_
    · exact hleft_product.eq_of_src _ _
    · exact hright_product.eq_of_tgt _ _
  letI : Subsingleton (L ⟶ K') := by
    simpa [Fadd, S, T] using AddCommGrpCat.subsingleton_of_isZero hmiddle_add
  simpa [L]

/-- Helper for Lemma 15.98.2: if every stage is annihilated by suitable powers of the elements of
`I`, then any derived limit is derived complete with respect to `I`. -/
private theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
    (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hpow :
      ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, (f ^ e : A) • 𝟙 (Ksys.obj (op n)) = 0)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: first promote the stagewise power-zero hypothesis to stagewise derived
  -- completeness, then pass completeness through the derived limit.
  apply isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise (I := I) Ksys K'
  · intro n
    exact stage_isDerivedCompleteWithRespectTo_of_power_zero (I := I) (Ksys.obj (op n))
      (fun f hf ↦ hpow f hf n)
  · exact hlim

/-- Helper for Lemma 15.98.2: the derived functor of a module-category equivalence induced by a
ring equivalence is itself an equivalence. -/
private noncomputable def derivedRestrictScalarsEquivalenceOfRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    DerivedCategory (ModuleCat S) ≌ DerivedCategory (ModuleCat R) :=
  -- TODO: identify the derived functors of the restriction-of-scalars equivalence on modules and
  -- package them as an equivalence of derived categories for the later transport step.
  sorry

/-- Helper for Lemma 15.98.2: an exact functor preserving countable products sends a Milnor
triangle to a Milnor triangle for the image tower. -/
private theorem isDerivedLimit_map_functor
    {R S : Type u} [CommRing R] [CommRing S]
    (G : DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat S))
    [G.CommShift ℤ] [G.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    {Ksys : SequentialInverseSystem (DerivedCategory (ModuleCat R))}
    {K : DerivedCategory (ModuleCat R)}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ G) (G.obj K) := by
  -- TODO: map the chosen Milnor triangle for `Ksys` through `G`, using preservation of countable
  -- products and triangulated exactness to obtain the transported Milnor witness.
  sorry

/-- Helper for Lemma 15.98.2: an isomorphism of sequential inverse systems induces the canonical
product isomorphism on their stage families. -/
private noncomputable def tower_product_iso
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys := by
  -- Transport the discrete product diagram along the stagewise natural isomorphism of towers.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Lemma 15.98.2: the product isomorphism attached to a tower isomorphism preserves
the projection to each stage. -/
private theorem tower_product_iso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom := by
  -- This is the defining projection formula for `HasLimit.isoOfNatIso`.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (op m.as)
  simpa [tower_product_iso, eFamily] using
    limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Lemma 15.98.2: the product isomorphism attached to a tower isomorphism intertwines
the Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  apply Pi.hom_ext
  intro n
  -- Compare both Milnor endomorphisms after the `n`th projection and reduce to naturality of
  -- the stagewise comparison `e`.
  calc
    ((tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (tower_product_iso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (Opposite.op (n + 1))).hom ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [tower_product_iso_hom_comp_π]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              (tower_product_iso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (Opposite.op n)).hom) := by
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
        (e.app (Opposite.op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (Opposite.op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
          rw [Category.assoc, ← tower_product_iso_hom_comp_π, ← Category.assoc]

/-- Helper for Lemma 15.98.2: a derived-limit witness transports across an isomorphism of towers
when the limiting object is kept fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem DMod} {K : DMod}
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
  let Tmilnor : Triangle DMod :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Ttransported : Triangle DMod :=
    Triangle.mk (ι ≫ (tower_product_iso e).hom) (derivedLimitDifferenceMap Lsys)
      ((tower_product_iso e).inv ≫ δ)
  have hIso : Tmilnor ≅ Ttransported := by
    -- Repackage the original Milnor triangle through the product comparison isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) (tower_product_iso e) (tower_product_iso e) ?_ ?_ ?_
    · simp [Tmilnor, Ttransported]
    · simpa [Tmilnor, Ttransported] using (tower_product_iso_hom_comm_difference e).symm
    · simp [Tmilnor, Ttransported]
  have hTtransported : Ttransported ∈ distTriang DMod := by
    -- Distinguished triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ⟨ι ≫ (tower_product_iso e).hom, (tower_product_iso e).inv ≫ δ, hTtransported⟩⟩

/-- Helper for Lemma 15.98.2: once a Milnor triangle is fixed for a tower, the limiting object
may be replaced by any isomorphic object. -/
private theorem isDerivedLimit_of_object_iso
    {Ksys : SequentialInverseSystem DMod} {K L : DMod}
    (e : K ≅ L)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Ksys L := by
  rcases hK with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let Tmilnor : Triangle DMod :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Ttransported : Triangle DMod :=
    Triangle.mk (e.inv ≫ ι) (derivedLimitDifferenceMap Ksys)
      (δ ≫ (shiftFunctor DMod (1 : ℤ)).map e.hom)
  have hIso : Tmilnor ≅ Ttransported := by
    -- Only the first vertex changes, so the comparison triangle is induced by `e`.
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [Tmilnor, Ttransported]
    · simp [Tmilnor, Ttransported]
    · simp [Tmilnor, Ttransported]
  have hTtransported : Ttransported ∈ distTriang DMod := by
    -- Distinguished triangles are stable under isomorphism, so the transported Milnor triangle
    -- remains distinguished.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact
    ⟨hP, ⟨e.inv ≫ ι, δ ≫ (shiftFunctor DMod (1 : ℤ)).map e.hom, hTtransported⟩⟩

/-- Helper for Lemma 15.98.2: adic completeness identifies `A` with the inverse limit of the
quotient system `A / I^(n+1)` in a way that is compatible with every stage projection. -/
private theorem idealPowerQuotient_limit_ring_equiv
    (hA : IsAdicComplete I A) :
    ∃ e : A ≃+* inverseLimitRing F,
      ∀ n : ℕ, (limitProjectionRingHom F n).comp e.toRingHom = algebraMap A (stageRing F n) := by
  -- TODO: build the compatible quotient maps `A → A / I^(n+1)`, lift them with
  -- `IsAdicComplete.liftRingHom`, and prove the inverse identities quotientwise with
  -- `IsAdicComplete.eq_liftRingHom`.
  sorry

/-- Helper for Lemma 15.98.2: once the complete-ring comparison is fixed, the inverse-limit-ring
fixed-base tower and the original base-`A` tower become naturally isomorphic. -/
private noncomputable def idealPowerQuotient_limit_tower_component_iso
    (T : IdealPowerQuotientDerivedTower I)
    {e : A ≃+* inverseLimitRing F}
    (he : ∀ n : ℕ, (limitProjectionRingHom F n).comp e.toRingHom = algebraMap A (stageRing F n))
    (n : ℕ) :
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory).obj
      (stageRestrictionToLimit F T n)) ≅
    stageRestrictionToBase F A T n :=
  -- TODO: compare the two restriction-of-scalars functors stagewise using `he n`, then pass the
  -- resulting module-level natural isomorphism to derived categories.
  sorry

/-- Helper for Lemma 15.98.2: once the complete-ring comparison is fixed, the inverse-limit-ring
fixed-base tower and the original base-`A` tower have explicit stagewise comparison isomorphisms,
so the remaining blocker is only to package their naturality into a tower isomorphism. -/
private theorem idealPowerQuotient_limit_tower_component_naturality
    (T : IdealPowerQuotientDerivedTower I)
    {e : A ≃+* inverseLimitRing F}
    (he : ∀ n : ℕ, (limitProjectionRingHom F n).comp e.toRingHom = algebraMap A (stageRing F n))
    (n : ℕ) :
    ((stageRestrictionToLimitTower F T ⋙
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory).map
        ((homOfLE (Nat.le_succ n)).op)) ≫
      (idealPowerQuotient_limit_tower_component_iso (I := I) T he n).hom =
        (idealPowerQuotient_limit_tower_component_iso (I := I) T he (n + 1)).hom ≫
          (stageRestrictionToBaseTower F A T).map ((homOfLE (Nat.le_succ n)).op) := by
  -- TODO: reduce both sides to the stagewise comparison isomorphisms from
  -- `idealPowerQuotient_limit_tower_component_iso` and check naturality against the tower step.
  sorry

/-- Helper for Lemma 15.98.2: once the complete-ring comparison is fixed, the inverse-limit-ring
fixed-base tower and the original base-`A` tower become naturally isomorphic. -/
private noncomputable def idealPowerQuotient_limit_tower_iso
    (T : IdealPowerQuotientDerivedTower I)
    {e : A ≃+* inverseLimitRing F}
    (he : ∀ n : ℕ, (limitProjectionRingHom F n).comp e.toRingHom = algebraMap A (stageRing F n)) :
    stageRestrictionToLimitTower F T ⋙
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory ≅
      stageRestrictionToBaseTower F A T :=
  -- TODO: package the stagewise comparison isomorphisms into a `NatIso` using the naturality
  -- lemma above.
  sorry

/-- Helper for Lemma 15.98.2: after transporting the tower and the chosen limiting object across
the complete-ring equivalence, the derived-limit witness lands in the owner setting of
Lemma `15.98.1`. -/
private theorem idealPowerQuotient_isDerivedLimit_transport
    (T : IdealPowerQuotientDerivedTower I) (K : DMod)
    {e : A ≃+* inverseLimitRing F}
    (he : ∀ n : ℕ, (limitProjectionRingHom F n).comp e.toRingHom = algebraMap A (stageRing F n))
    (htower :
      stageRestrictionToLimitTower F T ⋙
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory ≅
        stageRestrictionToBaseTower F A T)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K) :
    IsDerivedLimit (stageRestrictionToLimitTower F T)
      (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapDerivedCategory).obj K) := by
  -- TODO: transport `hKlim` across `htower.symm`, then map the Milnor witness through the
  -- derived restriction-of-scalars equivalence and normalize the unit isomorphism stagewise.
  sorry

/-- Helper for Lemma 15.98.2: after transporting the quotient tower from the complete base ring
`A` to the inverse-limit ring presentation, Lemma `15.98.1` yields pseudo-coherence of the chosen
derived limit. -/
private theorem idealPowerQuotient_limit_pseudoCoherent
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison (I := I) T n)) :
    K.IsPseudoCoherent := by
  rcases idealPowerQuotient_limit_ring_equiv (I := I) hA with ⟨e, he⟩
  have htower :
      stageRestrictionToLimitTower F T ⋙
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory ≅
        stageRestrictionToBaseTower F A T :=
    idealPowerQuotient_limit_tower_iso (I := I) T he
  have hKlimLim :
      IsDerivedLimit (stageRestrictionToLimitTower F T)
        (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapDerivedCategory).obj K) :=
    idealPowerQuotient_isDerivedLimit_transport (I := I) T K he htower hKlim
  -- TODO: package the textbook stagewise pseudo-coherence hypothesis as the eventual branch at
  -- stage `0`, apply Lemma `15.98.1` to the transported inverse-limit-ring tower, and then
  -- transport pseudo-coherence back to `K` using the counit isomorphism of the derived
  -- restriction-of-scalars equivalence.
  sorry

/-- Helper for Lemma 15.98.2: after the same inverse-limit-ring transport as above, the
stagewise base-change isomorphism follows from the base-change part of Lemma `15.98.1`. -/
private theorem idealPowerQuotient_limit_baseChange_isomorphic
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison (I := I) T n))
    (n : ℕ) : IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := by
  rcases idealPowerQuotient_limit_ring_equiv (I := I) hA with ⟨e, he⟩
  have htower :
      stageRestrictionToLimitTower F T ⋙
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory ≅
        stageRestrictionToBaseTower F A T :=
    idealPowerQuotient_limit_tower_iso (I := I) T he
  have hKlimLim :
      IsDerivedLimit (stageRestrictionToLimitTower F T)
        (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapDerivedCategory).obj K) :=
    idealPowerQuotient_isDerivedLimit_transport (I := I) T K he htower hKlim
  -- TODO: choose a Milnor product map for the transported derived-limit witness, apply the
  -- base-change half of Lemma `15.98.1` to the inverse-limit-ring tower, and identify that owner
  -- comparison morphism with the public base-change map
  -- `K ⊗[A]^L[A ⧸ I^(n+1)] ⟶ T.obj n`.
  sorry

-- Proof sketch: specialize Lemma `15.98.1` to the ideal-power quotient tower to obtain
-- pseudo-coherence of the chosen derived limit `K`, then combine it with the direct stagewise
-- power-zero criterion from Lemma `15.92.14` to deduce derived completeness.
/-- Lemma 15.98.2: let `A` be a ring, let `I ⊆ A` be an ideal, and let `K` be a chosen derived
limit of the canonical fixed-base tower attached to a compatible tower
`T : IdealPowerQuotientDerivedTower I` of objects `K_n ∈ D(A / I^(n+1))` viewed over `A`.
Assume `A` is `I`-adically complete, the first stage `K_1` is pseudo-coherent, and the stagewise
derived reductions
`K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1) → K_n` induced by `T.stepMap` are
isomorphisms. Then `K` is pseudo-coherent and derived complete with respect to `I`. Here stage
`0` corresponds to the textbook object `K_1`. -/
@[stacks 09AV]
theorem derivedLimit_of_idealPowerQuotientTower_isPseudoCoherent_and_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison (I := I) T n)) :
    K.IsPseudoCoherent ∧ K.IsDerivedCompleteWithRespectTo I := by
  constructor
  · -- The pseudo-coherence half is exactly the transported quotient-tower case of Lemma `15.98.1`.
    exact idealPowerQuotient_limit_pseudoCoherent
      (I := I) T K hA hKlim hK₁ hstageBaseChange
  · -- Derived completeness is independent of the inverse-limit-ring transport and follows
    -- directly from stagewise power-zero over the fixed base ring `A`.
    refine isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
      (I := I)
      (Ksys := stageRestrictionToBaseTower F A T)
      (K' := K)
      ?_ hKlim
    intro f hf n
    exact idealPowerQuotient_stage_power_zero (I := I) T hf n

-- Proof sketch: this is the base-change part of Lemma `15.98.1` specialized to the ideal-power
-- quotient tower `A / I^(n+1)`, whose transition maps are the canonical quotient morphisms.
/-- For the quotient tower of Lemma 15.98.2, if `A` is `I`-adically complete, then the derived
base change of the chosen limit object `K` to each quotient stage `A / I^(n+1)` recovers the
corresponding stage object `K_n`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_pseudoCoherent_derivedLimit
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison (I := I) T n))
    (n : ℕ) : IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := by
  -- The base-change statement uses the same inverse-limit-ring transport as the pseudo-coherent
  -- half of the main theorem, so we package that blocker in a dedicated helper.
  exact idealPowerQuotient_limit_baseChange_isomorphic
    (I := I) T K hA hKlim hK₁ hstageBaseChange n

end
