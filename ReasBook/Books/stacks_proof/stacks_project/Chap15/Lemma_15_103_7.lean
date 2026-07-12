import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.Chap13.Proposition_13_4_23
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_59_15
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Lemma_15_67_2
import StacksProject_2024.Chap15.Lemma_15_67_6
import StacksProject_2024.Chap15.Lemma_15_67_17
import StacksProject_2024.Chap15.Lemma_15_103_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Pretriangulated
open DerivedCategory
open scoped DerivedTensorProduct
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
private abbrev single₀ : ModuleCat R ⥤ DMod :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
private abbrev ringSingle : DMod :=
  single₀.obj (ModuleCat.of R R)

/- Domain-style sampling for Lemma 15.103.7:
- primary domain: tor-amplitude in `D(R)` and its source-facing degree-zero flatness
  reformulation;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `DerivedCategory.IsLE`,
  `CategoryTheory.hasTorAmplitudeIn_iff_exists_flat_representative`,
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`;
- best owner abstraction: the chapter owner is `HasTorAmplitudeIn`, with the degree-zero flatness
  wording treated as a bridge/view used only to restore the textbook statement of Lemma 15.103.7;
- primitive vs. derived:
  primitive data are the derived object and its tor-amplitude predicate;
  derived API is the degree-zero bridge
  `hasTorAmplitudeIn_zero_zero_iff_exists_flat_module`, used to recover the textbook flat-module
  formulation from the owner predicate.

Source/core/bridge triage:
- `source-facing`: `isFlatModuleInDegreeZero_of_localizationAway_and_quotient`;
- `core/canonical`: `HasTorAmplitudeIn _ 0 0`;
- `bridge/view`: `hasTorAmplitudeIn_zero_zero_iff_exists_flat_module`. -/

-- Proof sketch: specialize `hasTorAmplitudeIn_iff_exists_flat_representative` to the interval
-- `[0, 0]`. The representative then has a single possibly nonzero term in degree `0`, and
-- `ModuleCat.hasTorDimensionLE_zero_iff_flat` identifies that term as flat.
/-- An object of `D(R)` has tor-amplitude in `[0, 0]` exactly when it is isomorphic to a flat
`R`-module placed in degree `0`. -/
theorem hasTorAmplitudeIn_zero_zero_iff_exists_flat_module (M : DMod) :
    HasTorAmplitudeIn M 0 0 ↔
      ∃ N : ModuleCat R, Module.Flat R N ∧ IsIsomorphic M ((single₀).obj N) := by
  classical
  constructor
  · intro hM
    let eUnit : ringSingle ≅ 𝟙_ DMod :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (ModuleCat.of R R)) ≪≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
            ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
              (ModuleCat.of R R))).symm
    let eRing : M ⊗[R]^L ringSingle ≅ M :=
      (derivedTensorProduct_comm M ringSingle) ≪≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct ringSingle M).symm ≪≫
          whiskerRightIso eUnit M ≪≫ λ_ M
    have hGE : M.IsGE 0 := by
      -- Test tor-amplitude against the tensor unit and transport the resulting vanishing back to `M`.
      rw [DerivedCategory.isGE_iff]
      intro i hi
      have hi' : i ∉ Set.Icc (0 : ℤ) 0 := by
        simp [hi.ne]
      have hzero : IsZero ((H i).obj (M ⊗[R]^L ringSingle)) := hM (ModuleCat.of R R) i hi'
      exact hzero.of_iso ((H i).mapIso eRing.symm)
    have hLE : M.IsLE 0 := by
      -- The same tensor-unit test controls positive homology and yields the upper truncation bound.
      rw [DerivedCategory.isLE_iff]
      intro i hi
      have hi' : i ∉ Set.Icc (0 : ℤ) 0 := by
        simp [ne_of_gt hi]
      have hzero : IsZero ((H i).obj (M ⊗[R]^L ringSingle)) := hM (ModuleCat.of R R) i hi'
      exact hzero.of_iso ((H i).mapIso eRing.symm)
    -- Once `M` is concentrated in degree `0`, its degree-zero cohomology module presents `M`.
    let hsingle := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M 0
    let N : ModuleCat R := Classical.choose hsingle
    let e : M ≅ (single₀).obj N := Classical.choice (Classical.choose_spec hsingle)
    have hNamp : HasTorAmplitudeIn ((single₀).obj N) 0 0 := by
      intro P i hi
      have hzero : IsZero ((H i).obj (M ⊗[R]^L (single₀).obj P)) := hM P i hi
      exact
        hzero.of_iso
          ((H i).mapIso (((derivedTensorProduct ((single₀).obj P)).mapIso e.symm)))
    have hNtor : ModuleHasTorDimensionLE N 0 := by
      simpa using hNamp
    have hNflat : Module.Flat R N := (ModuleCat.hasTorDimensionLE_zero_iff_flat N).1 hNtor
    refine ⟨N, hNflat, ?_⟩
    exact ⟨e⟩
  · rintro ⟨N, hNflat, hNiso⟩
    let e : M ≅ (single₀).obj N := Classical.choice hNiso
    -- For a degree-zero object, tor-amplitude `[0, 0]` is exactly module tor-dimension `≤ 0`.
    have hNtor : ModuleHasTorDimensionLE N 0 := by
      exact (ModuleCat.hasTorDimensionLE_zero_iff_flat N).2 hNflat
    have hNamp : HasTorAmplitudeIn ((single₀).obj N) 0 0 := by
      simpa using hNtor
    intro P i hi
    have hzero : IsZero ((H i).obj ((single₀).obj N ⊗[R]^L (single₀).obj P)) := hNamp P i hi
    exact
      hzero.of_iso
        ((H i).mapIso (((derivedTensorProduct ((single₀).obj P)).mapIso e)))

variable (f : R)

local notation "Rf" => Localization.Away f
local notation "Rbar" => R ⧸ Ideal.span (Set.singleton f)
local notation "HRf" => DerivedCategory.homologyFunctor (ModuleCat Rf)
local notation "HRbar" => DerivedCategory.homologyFunctor (ModuleCat Rbar)
private abbrev single₀Rf : ModuleCat Rf ⥤ DerivedCategory (ModuleCat Rf) :=
  DerivedCategory.singleFunctor (ModuleCat Rf) (0 : ℤ)
private abbrev single₀Rbar : ModuleCat Rbar ⥤ DerivedCategory (ModuleCat Rbar) :=
  DerivedCategory.singleFunctor (ModuleCat Rbar) (0 : ℤ)

/-- Helper for Lemma 15.103.7: scalar extension is additive on module categories. -/
local instance extendScalars_additive_local
    {A : Type u} [CommRing A] [Algebra R A] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap R A)).left_adjoint_additive

/-- Helper for Lemma 15.103.7: flat scalar extension preserves finite limits. -/
local instance extendScalars_preservesFiniteLimits_local
    {A : Type u} [CommRing A] [Algebra R A] [Module.Flat R A] :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R A from inferInstance))

-- Proof sketch: tensor `M` with an arbitrary `R`-module concentrated in degree `0`, use `hM`
-- to keep the tensor product in `D^{≤ 0}(R)`, then apply Lemma `15.103.6` to the multiplication
-- triangle by `f`. The localization and quotient hypotheses are fed in through the chapter owner
-- `HasTorAmplitudeIn _ 0 0`, which is the canonical degree-zero flatness condition.
/-- Helper for Lemma 15.103.7: flat scalar extension commutes with the standard degree-zero test
object. -/
noncomputable def tensor_single_baseChange_iso
    {A : Type u} [CommRing A] [Algebra R A] [Module.Flat R A]
    (M : DMod) (N : ModuleCat R) :
    ((M ⊗[R]^L[A]) ⊗[A]^L
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        ((ModuleCat.extendScalars (algebraMap R A)).obj N))) ≅
      (M ⊗[R]^L (single₀.obj N)) ⊗[R]^L[A] :=
  -- Reuse the chapter's canonical change-of-rings comparison on the common test object `N[0]`.
  (derivedTensorWithAlgebra_tensor_single_iso (R := R) (R' := A) M N).symm

/-- Helper for Lemma 15.103.7: scalar extension on module categories is the canonical tensor
product with the target ring. -/
private noncomputable def extendScalars_tensor_iso
    {A : Type u} [CommRing A] [Algebra R A] (M : ModuleCat R) :
    (ModuleCat.extendScalars (algebraMap R A)).obj M ≅
      ModuleCat.of A (A ⊗[R] M) := by
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) ≃ₗ[A] A :=
    { __ := AddEquiv.refl A
      map_smul' := fun _ _ ↦ rfl }
  let _ : IsScalarTower R A
      ↑((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  -- Expand extension of scalars and collapse the restricted-scalar copy of the target ring.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl R ↑M)).toModuleIso

/-- Helper for Lemma 15.103.7: exact scalar extension to `R_f` is the usual away-localization on
modules. -/
noncomputable def extendScalars_localizationAway_iso (M : ModuleCat R) :
    (ModuleCat.extendScalars (algebraMap R Rf)).obj M ≅
      ModuleCat.of Rf (LocalizedModule.Away f M) :=
  -- Rewrite scalar extension through the tensor presentation, then identify that tensor with
  -- away-localization.
  extendScalars_tensor_iso (R := R) (A := Rf) M ≪≫
    ((LocalizedModule.equivTensorProduct (Submonoid.powers f) (↑M)).symm).toModuleIso

/-- Helper for Lemma 15.103.7: restriction of scalars reflects zero objects on module
categories. -/
private lemma isZero_of_restrictScalars_obj
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat B)
    (hM : IsZero ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :
    IsZero M := by
  -- Restriction of scalars leaves the underlying additive group unchanged, so zero reflects.
  letI : Subsingleton ↑((ModuleCat.restrictScalars (algebraMap A B)).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.restrictScalars (algebraMap A B)).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.103.7: exact restriction of scalars commutes with homology on the
derived category of modules. -/
private noncomputable def restrictScalars_homology_iso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (L : DerivedCategory (ModuleCat B)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj K
  let eB :
      (DerivedCategory.homologyFunctor (ModuleCat B) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso
        (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Pass to a complex representative, compare homology before and after restriction, and then
  -- return to the derived-category homology objects.
  (DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso
      (((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app FK ≪≫
    (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap A B)) ≪≫
      (ModuleCat.restrictScalars (algebraMap A B)).mapIso eB.symm

/-- Helper for Lemma 15.103.7: zero homology remains zero after restricting scalars from `B` to
`A`. -/
private lemma isZero_homology_restrictScalars_of_isZero
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (L : DerivedCategory (ModuleCat B)) (i : ℤ)
    (hL : IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj L)) :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)) := by
  -- Move the vanishing statement across the canonical homology comparison for restriction of
  -- scalars.
  exact (restrictScalars_homology_iso L i).isZero_iff.2 <|
    (ModuleCat.restrictScalars (algebraMap A B)).map_isZero hL

/-- Helper for Lemma 15.103.7: the localization hypothesis kills every nonzero localized
homology group after testing against `N[0]`. -/
lemma localized_homology_isZero_of_localizationAway_torAmplitude_zero_zero
    (M : DMod)
    (hlocalization : HasTorAmplitudeIn (M ⊗[R]^L[Rf]) 0 0)
    (N : ModuleCat R) :
    ∀ i : ℤ, i ≠ 0 →
      IsZero (ModuleCat.of Rf (LocalizedModule.Away f ((H i).obj (M ⊗[R]^L (single₀.obj N))))) := by
  intro i hi
  let K : DMod := M ⊗[R]^L (single₀.obj N)
  let Nf : ModuleCat Rf := (ModuleCat.extendScalars (algebraMap R Rf)).obj N
  have hi' : i ∉ Set.Icc (0 : ℤ) 0 := by
    simp [hi]
  have hbase :
      IsZero
        ((HRf i).obj
          (((M ⊗[R]^L[Rf]) ⊗[Rf]^L ((single₀Rf (f := f)).obj Nf)))) := by
    -- Evaluate the localization tor-amplitude hypothesis on the scalar-extended test module.
    simpa [Nf] using hlocalization Nf i hi'
  have htensor :
      IsZero ((HRf i).obj (K ⊗[R]^L[Rf])) := by
    -- Rewrite the localized tested object to the canonical base-changed tensor comparison.
    exact hbase.of_iso
      ((HRf i).mapIso (tensor_single_baseChange_iso (R := R) (A := Rf) M N).symm)
  have hmap :
      IsZero
        ((HRf i).obj
          (((ModuleCat.extendScalars (algebraMap R Rf)).mapDerivedCategory).obj K)) := by
    -- Replace the derived scalar-extension owner by exact scalar extension on the derived category.
    exact htensor.of_iso
      ((HRf i).mapIso ((extendScalars_mapDerivedCategory_iso (R := R) (R' := Rf)).app K))
  have hext :
      IsZero ((ModuleCat.extendScalars (algebraMap R Rf)).obj ((H i).obj K)) := by
    -- Commute exact scalar extension with homology to move vanishing back to the module level.
    exact
      (extendScalars_homology_iso (R := R) (R' := Rf) K i).isZero_iff.1 hmap
  -- Finally rewrite exact scalar extension of homology as away-localization of that homology.
  exact
    (extendScalars_localizationAway_iso (R := R) (f := f) ((H i).obj K)).isZero_iff.2 hext

/-- Helper for Lemma 15.103.7: on a test module, the image of multiplication by `f` is the
submodule `fK`. -/
private theorem testModule_range_lsmul_eq_span_singleton_smul_top
    (Kmod : ModuleCat R) :
    LinearMap.range (LinearMap.lsmul R Kmod f) =
      Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod) := by
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- A visible `f`-multiple lies in the principal-ideal multiple by construction.
    simpa [LinearMap.lsmul_apply] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
        (show y ∈ (⊤ : Submodule R Kmod) by simp))
  · intro hx
    -- Conversely, every generator of `fK` is visibly in the image of multiplication by `f`.
    have hle :
        Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod) ≤
          LinearMap.range (LinearMap.lsmul R Kmod f) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨a, rfl⟩
      refine LinearMap.mem_range.mpr ⟨a • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.103.7: on a test module, the kernel of multiplication by `f` is the
standard `f`-torsion submodule. -/
private theorem testModule_ker_lsmul_eq_torsionBy
    (Kmod : ModuleCat R) :
    LinearMap.ker (LinearMap.lsmul R Kmod f) = Submodule.torsionBy R Kmod f := by
  ext x
  -- Both owners encode the same equation `f • x = 0`.
  rw [LinearMap.mem_ker, Submodule.mem_torsionBy_iff, LinearMap.lsmul_apply]

/-- Helper for Lemma 15.103.7: the kernel-to-image row
`0 → K[f] → K → im(·f) → 0` is short exact for any test module `K`. -/
private theorem testModule_multiplication_kernel_range_shortExact
    (Kmod : ModuleCat R) :
    let μ : Kmod →ₗ[R] Kmod := LinearMap.lsmul R Kmod f
    (ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.ker μ).subtype)
      (ModuleCat.ofHom μ.rangeRestrict)
      (by
        -- The range-restricted multiplication map vanishes on the kernel by definition.
        ext x
        simp)).ShortExact := by
  let μ : Kmod →ₗ[R] Kmod := LinearMap.lsmul R Kmod f
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.ker μ).subtype)
      (ModuleCat.ofHom μ.rangeRestrict)
      (by
        -- The kernel condition is exactly the vanishing needed for the composite to be zero.
        ext x
        simp)
  have hExact : Function.Exact (LinearMap.ker μ).subtype μ.rangeRestrict := by
    -- Rewrite exactness of the kernel-range row to the standard owner equality `range = ker`.
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  -- The source row is the canonical short exact kernel-to-range sequence for multiplication by `f`.
  simpa [S] using
    ModuleCat.shortComplex_shortExact S hExact (Submodule.injective_subtype _) μ.surjective_rangeRestrict

/-- Helper for Lemma 15.103.7: the canonical quotient row
`0 → fK → K → K / fK → 0` is short exact for any test module `K`. -/
private theorem testModule_principal_quotient_shortExact
    (Kmod : ModuleCat R) :
    let fK : Submodule R Kmod := Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod)
    (ShortComplex.mk
      (ModuleCat.ofHom fK.subtype)
      (ModuleCat.ofHom fK.mkQ)
      (by
        -- The quotient map kills the denominator by definition.
        ext x
        simp)).ShortExact := by
  let fK : Submodule R Kmod := Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod)
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (ModuleCat.ofHom fK.subtype)
      (ModuleCat.ofHom fK.mkQ)
      (by
        -- The quotient map kills each denominator element by construction.
        ext x
        simp)
  have hExact : Function.Exact fK.subtype fK.mkQ := by
    -- This is the canonical exactness statement for a submodule inclusion followed by quotient.
    simpa using LinearMap.exact_subtype_mkQ fK
  -- The quotient row is the standard short exact sequence attached to a submodule.
  simpa [S] using
    ModuleCat.shortComplex_shortExact S hExact (Submodule.injective_subtype _) (Submodule.mkQ_surjective fK)

/-- Helper for Lemma 15.103.7: the principal ideal `(f)` acts trivially on the `f`-torsion
test module. -/
private theorem testModule_torsionBy_span_singleton_smul_eq_bot
    (Kmod : ModuleCat R) :
    Ideal.span ({f} : Set R) • (⊤ : Submodule R (Submodule.torsionBy R Kmod f)) = ⊥ := by
  let T : ModuleCat R := ModuleCat.of R (Submodule.torsionBy R Kmod f)
  calc
    Ideal.span ({f} : Set R) • (⊤ : Submodule R (Submodule.torsionBy R Kmod f)) =
        LinearMap.range (LinearMap.lsmul R T f) := by
          -- Rewrite the principal-ideal multiple as the visible range of multiplication by `f`.
          simpa [T] using
            (testModule_range_lsmul_eq_span_singleton_smul_top
              (R := R) (f := f) (Kmod := T)).symm
    _ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
      -- On the torsion submodule, multiplication by `f` is already zero.
      exact Subtype.ext <| by
        have hy : f • (y : Kmod) = 0 := by
          simpa [Submodule.mem_torsionBy_iff] using y.property
        simpa [LinearMap.lsmul_apply] using hy

/-- Helper for Lemma 15.103.7: every element of `(f)` acts trivially on the `f`-torsion test
module. -/
private theorem testModule_torsionBy_smul_eq_zero_of_mem_span_singleton
    (Kmod : ModuleCat R) {r : R}
    (hr : r ∈ Ideal.span ({f} : Set R))
    (x : Submodule.torsionBy R Kmod f) :
    r • (x : Kmod) = 0 := by
  rcases Ideal.mem_span_singleton.mp hr with ⟨a, rfl⟩
  have hx : f • (x : Kmod) = 0 := by
    -- Membership in the torsion submodule is exactly the equation `f • x = 0`.
    simpa [Submodule.mem_torsionBy_iff] using x.property
  -- Pull the torsion equation through scalar multiplication by `a`.
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun y : Kmod => a • y) hx

/-- Helper for Lemma 15.103.7: scalar multiples of `f`-torsion elements remain `f`-torsion. -/
private theorem testModule_torsionBy_smul_mem
    (Kmod : ModuleCat R) (a : R)
    (x : Submodule.torsionBy R Kmod f) :
    a • (x : Kmod) ∈ Submodule.torsionBy R Kmod f := by
  have hx : f • (x : Kmod) = 0 := by
    -- Rewrite the torsion condition as the defining vanishing equation.
    simpa [Submodule.mem_torsionBy_iff] using x.property
  rw [Submodule.mem_torsionBy_iff]
  -- Commute the two scalar actions so the original torsion equation can be reused.
  calc
    f • (a • (x : Kmod)) = (f * a) • (x : Kmod) := by
      rw [smul_smul]
    _ = a • (f • (x : Kmod)) := by
      rw [smul_smul, mul_comm]
    _ = 0 := by
      simp [hx]

/-- Helper for Lemma 15.103.7: sums of elements already known to be `f`-torsion remain
`f`-torsion. -/
private theorem testModule_torsionBy_add_mem
    (Kmod : ModuleCat R) {x y : Kmod}
    (hx : x ∈ Submodule.torsionBy R Kmod f)
    (hy : y ∈ Submodule.torsionBy R Kmod f) :
    x + y ∈ Submodule.torsionBy R Kmod f :=
  add_mem hx hy

/-- Helper for Lemma 15.103.7: the quotient-class action on `K[f]` is independent of the chosen
representative in `R / fR`. -/
private theorem testModule_torsionBy_bar_smul_wellDefined
    (Kmod : ModuleCat R) {a b : R}
    (hab : (a : Rbar) = b)
    (x : Submodule.torsionBy R Kmod f) :
    (⟨a • (x : Kmod), testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a x⟩ :
      Submodule.torsionBy R Kmod f) =
      ⟨b • (x : Kmod), testModule_torsionBy_smul_mem (R := R) (f := f) Kmod b x⟩ := by
  apply Subtype.ext
  have hmem : a - b ∈ Ideal.span ({f} : Set R) := Ideal.Quotient.eq.mp hab
  have hzero : (a - b) • (x : Kmod) = 0 :=
    testModule_torsionBy_smul_eq_zero_of_mem_span_singleton
      (R := R) (f := f) (Kmod := Kmod) hmem x
  -- Equality of the two representatives reduces to vanishing of their difference.
  apply sub_eq_zero.mp
  simpa [sub_smul] using hzero

/-- Helper for Lemma 15.103.7: the `f`-torsion test module carries its canonical `R / fR`
module structure. -/
private noncomputable instance testModule_torsionBy_bar_module
    (Kmod : ModuleCat R) :
    Module Rbar (Submodule.torsionBy R Kmod f) where
  smul q x :=
    Quotient.liftOn q
      (fun a : R =>
        -- Use the chosen representative to act on the underlying `R`-module, then close on the
        -- torsion submodule with the scalar-stability lemma above.
        (⟨a • (x : Kmod), testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a x⟩ :
          Submodule.torsionBy R Kmod f))
      (fun a b hab =>
        testModule_torsionBy_bar_smul_wellDefined
          (R := R) (f := f) (Kmod := Kmod)
          (show (a : Rbar) = b from Quotient.sound hab) x)
  one_smul := by
    intro x
    -- On the class of `1`, the quotient action reduces to the original scalar action.
    change (⟨(1 : R) • (x : Kmod),
        testModule_torsionBy_smul_mem (R := R) (f := f) Kmod 1 x⟩ :
      Submodule.torsionBy R Kmod f) = x
    apply Subtype.ext
    simp
  mul_smul := by
    intro q₁ q₂ x
    -- Check the module law on representatives of the two quotient classes.
    refine Quotient.inductionOn q₁ ?_
    intro a
    refine Quotient.inductionOn q₂ ?_
    intro b
    change (⟨((a * b : R) • (x : Kmod)),
        testModule_torsionBy_smul_mem (R := R) (f := f) Kmod (a * b) x⟩ :
      Submodule.torsionBy R Kmod f) =
        ⟨a •
            ((⟨b • (x : Kmod),
                testModule_torsionBy_smul_mem (R := R) (f := f) Kmod b x⟩ :
              Submodule.torsionBy R Kmod f) : Kmod),
          testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a _⟩
    apply Subtype.ext
    simp [mul_smul]
  smul_add := by
    intro q x y
    -- Additivity is also checked on representatives, then on the underlying `R`-module.
    refine Quotient.inductionOn q ?_
    intro a
    change (⟨a • ((x + y : Submodule.torsionBy R Kmod f) : Kmod),
        testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a (x + y)⟩ :
      Submodule.torsionBy R Kmod f) =
        ⟨a • (x : Kmod) + a • (y : Kmod),
          testModule_torsionBy_add_mem (R := R) (f := f) (Kmod := Kmod)
            (testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a x)
            (testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a y)⟩
    apply Subtype.ext
    simp [smul_add]
  smul_zero := by
    intro q
    -- The zero vector remains zero after acting by any representative.
    refine Quotient.inductionOn q ?_
    intro a
    change (⟨a • ((0 : Submodule.torsionBy R Kmod f) : Kmod),
        testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a 0⟩ :
      Submodule.torsionBy R Kmod f) = 0
    apply Subtype.ext
    simp
  add_smul := by
    intro q₁ q₂ x
    -- The distributive law follows from the corresponding `R`-module identity on representatives.
    refine Quotient.inductionOn q₁ ?_
    intro a
    refine Quotient.inductionOn q₂ ?_
    intro b
    change (⟨((a + b : R) • (x : Kmod)),
        testModule_torsionBy_smul_mem (R := R) (f := f) Kmod (a + b) x⟩ :
      Submodule.torsionBy R Kmod f) =
        ⟨a • (x : Kmod) + b • (x : Kmod),
          testModule_torsionBy_add_mem (R := R) (f := f) (Kmod := Kmod)
            (testModule_torsionBy_smul_mem (R := R) (f := f) Kmod a x)
            (testModule_torsionBy_smul_mem (R := R) (f := f) Kmod b x)⟩
    apply Subtype.ext
    simp [add_smul]
  zero_smul := by
    intro x
    -- The class of `0` acts trivially.
    change (⟨(0 : R) • (x : Kmod),
        testModule_torsionBy_smul_mem (R := R) (f := f) Kmod 0 x⟩ :
      Submodule.torsionBy R Kmod f) = 0
    apply Subtype.ext
    simp

/-- Helper for Lemma 15.103.7: the `f`-torsion outer term has its canonical `R / fR`
module-category owner. -/
private abbrev testModule_torsionBy_bar (Kmod : ModuleCat R) : ModuleCat Rbar :=
  ModuleCat.of Rbar (Submodule.torsionBy R Kmod f)

/-- Helper for Lemma 15.103.7: after restricting scalars, the quotient-ring owner of `K[f]`
recovers the original torsion submodule object over `R`. -/
private abbrev testModule_torsionBy_bar_restrictScalars_iso (Kmod : ModuleCat R) :
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).obj
      (testModule_torsionBy_bar (f := f) Kmod)) ≅
      ModuleCat.of R (Submodule.torsionBy R Kmod f) :=
  -- Restricting the quotient action along `R → R / fR` recovers the original `R`-module.
  Iso.refl _

/-- Helper for Lemma 15.103.7: the principal ideal `(f)` acts trivially on the quotient test
module `K / fK`. -/
private theorem testModule_principal_quotient_span_singleton_smul_eq_bot
    (Kmod : ModuleCat R) :
    let fK : Submodule R Kmod := Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod)
    Ideal.span ({f} : Set R) • (⊤ : Submodule R (Kmod ⧸ fK)) = ⊥ := by
  let fK : Submodule R Kmod := Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod)
  let Q : ModuleCat R := ModuleCat.of R (Kmod ⧸ fK)
  calc
    Ideal.span ({f} : Set R) • (⊤ : Submodule R (Kmod ⧸ fK)) =
        LinearMap.range (LinearMap.lsmul R Q f) := by
          -- Rewrite the principal-ideal multiple as the range of multiplication by `f`.
          simpa [Q, fK] using
            (testModule_range_lsmul_eq_span_singleton_smul_top
              (R := R) (f := f) (Kmod := Q)).symm
    _ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective fK y
      -- The class of `f • z` is zero because `f • z` already lies in the denominator `fK`.
      change Submodule.mkQ fK (f • z) = 0
      refine (Submodule.Quotient.mk_eq_zero fK).2 ?_
      refine ⟨f • z, ?_, rfl⟩
      simpa [fK] using
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
          (show z ∈ (⊤ : Submodule R Kmod) by simp))

/-- Helper for Lemma 15.103.7: the quotient outer term already has its canonical `R / fR`
module-category owner. -/
private abbrev testModule_principal_quotient_bar (Kmod : ModuleCat R) : ModuleCat Rbar :=
  ModuleCat.of Rbar (Kmod ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod)))

/-- Helper for Lemma 15.103.7: after restricting scalars, the quotient-ring owner of `K / fK`
recovers the original quotient object over `R`. -/
private abbrev testModule_principal_quotient_bar_restrictScalars_iso (Kmod : ModuleCat R) :
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).obj
      (testModule_principal_quotient_bar (f := f) Kmod)) ≅
      ModuleCat.of R (Kmod ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod))) :=
  Iso.refl _

/-- Helper for Lemma 15.103.7: after restricting scalars from `R / fR` back to `R`, tensoring
the quotient-side base change of `M` against a degree-zero `R / fR`-module agrees with tensoring
`M` against the restricted degree-zero module. -/
private noncomputable theorem tensor_single_restrictScalars_quotient_iso
    (M : DMod) (P : ModuleCat Rbar) :
    (((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P)))) ≅
      (M ⊗[R]^L
        (single₀.obj
          (((ModuleCat.restrictScalars
            (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).obj P)))) := by
  let q : R →+* Rbar := Ideal.Quotient.mk (Ideal.span ({f} : Set R))
  let K := DerivedCategory.Q.objPreimage M
  let extK : CochainComplex (ModuleCat Rbar) ℤ :=
    (((ModuleCat.extendScalars q).mapHomologicalComplex (up ℤ)).obj K)
  let singleP : CochainComplex (ModuleCat Rbar) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat Rbar) (0 : ℤ)).obj P
  let res := (ModuleCat.restrictScalars q).mapDerivedCategory
  let resC := (ModuleCat.restrictScalars q).mapHomologicalComplex (up ℤ)
  let ext :
      ((ModuleCat.extendScalars q).mapDerivedCategory.obj M) ≅
        DerivedCategory.Q.obj extK :=
    ((ModuleCat.extendScalars q).mapDerivedCategory).mapIso
        (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      (ModuleCat.extendScalars q).mapDerivedCategoryFactors.app K
  -- Route correction: normalize the quotient-side base change through exact scalar extension,
  -- push restriction of scalars down to a chosen complex representative, and then rebuild the
  -- source-facing degree-zero tensor object on the restricted module.
  calc
    res.obj (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P))) ≅
        res.obj ((((ModuleCat.extendScalars q).mapDerivedCategory).obj M) ⊗[Rbar]^L
          ((single₀Rbar (f := f)).obj P)) := by
      -- First replace the derived quotient base change by exact scalar extension.
      exact
        res.mapIso
          ((derivedTensorProduct ((single₀Rbar (f := f)).obj P)).mapIso
            ((extendScalars_mapDerivedCategory_iso (R := R) (R' := Rbar)).symm.app M))
    _ ≅ res.obj ((DerivedCategory.Q.obj extK) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P)) := by
      -- Next rewrite the exact scalar-extension owner on `M` by the chosen complex model `extK`.
      exact
        res.mapIso
          ((derivedTensorProduct ((single₀Rbar (f := f)).obj P)).mapIso ext)
    _ ≅ res.obj (((single₀Rbar (f := f)).obj P) ⊗[Rbar]^L (DerivedCategory.Q.obj extK)) := by
      -- Commute the two tensor factors so the degree-zero quotient module is on the left.
      exact
        res.mapIso
          (derivedTensorProduct_comm
            (DerivedCategory.Q.obj extK)
            ((single₀Rbar (f := f)).obj P))
    _ ≅ res.obj (((single₀Rbar (f := f)).obj P) ⊗ (DerivedCategory.Q.obj extK)) := by
      -- Replace the left-derived tensor notation by the owner monoidal tensor.
      exact
        res.mapIso
          (derivedCategory_tensorObj_iso_derivedTensorProduct
            ((single₀Rbar (f := f)).obj P)
            (DerivedCategory.Q.obj extK)).symm
    _ ≅ res.obj ((DerivedCategory.Q.obj singleP) ⊗ (DerivedCategory.Q.obj extK)) := by
      -- Resolve the quotient-side degree-zero object to its explicit single-complex model.
      exact
        res.mapIso
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat Rbar) (0 : ℤ)).app P) ⊗ᵢ
            Iso.refl _)
    _ ≅ res.obj (DerivedCategory.Q.obj (HomologicalComplex.tensorObj singleP extK)) := by
      -- The localization functor `Q` is monoidal, so it recombines the two complex factors.
      exact
        res.mapIso
          (Functor.Monoidal.μIso
            (DerivedCategory.Q :
              CochainComplex (ModuleCat Rbar) ℤ ⥤ DerivedCategory (ModuleCat Rbar))
            singleP extK)
    _ ≅ DerivedCategory.Q.obj (resC.obj (HomologicalComplex.tensorObj singleP extK)) := by
      -- Push exact restriction of scalars through the derived-category quotient.
      exact
        (ModuleCat.restrictScalars q).mapDerivedCategoryFactors.app
          (HomologicalComplex.tensorObj singleP extK)
    _ ≅ DerivedCategory.Q.obj (HomologicalComplex.tensorObj (resC.obj singleP) K) := by
      -- Compare the restricted tensor complex with the tensor of the restricted degree-zero
      -- complex against the original representative of `M`.
      exact
        DerivedCategory.Q.mapIso
          (restrictScalars_tensorObj_extendScalars_iso q singleP K)
    _ ≅ DerivedCategory.Q.obj (resC.obj singleP) ⊗ DerivedCategory.Q.obj K := by
      -- Re-expand the recombined complex tensor on the `R`-side.
      exact
        (Functor.Monoidal.μIso
          (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod)
          (resC.obj singleP)
          K).symm
    _ ≅ (((ModuleCat.restrictScalars q).mapDerivedCategory).obj
        ((single₀Rbar (f := f)).obj P)) ⊗ M := by
      -- Reassemble the restricted degree-zero object and the original derived object `M`.
      exact
        ((((ModuleCat.restrictScalars q).mapDerivedCategoryFactors.app singleP).symm ≪≫
            (((ModuleCat.restrictScalars q).mapDerivedCategory).mapIso
              ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat Rbar) (0 : ℤ)).app P).symm)) ⊗ᵢ
          (DerivedCategory.Q.objObjPreimageIso M))
    _ ≅
        (single₀.obj (((ModuleCat.restrictScalars q).obj P))) ⊗ M := by
      -- Exact restriction of scalars sends a degree-zero complex to the degree-zero restricted
      -- module.
      exact (restrictScalars_single_iso q P) ⊗ᵢ Iso.refl _
    _ ≅
        (single₀.obj (((ModuleCat.restrictScalars q).obj P))) ⊗[R]^L M := by
      -- Return from the monoidal tensor owner to the source-facing derived tensor notation.
      exact
        derivedCategory_tensorObj_iso_derivedTensorProduct
          (single₀.obj (((ModuleCat.restrictScalars q).obj P)))
          M
    _ ≅
        M ⊗[R]^L (single₀.obj (((ModuleCat.restrictScalars q).obj P))) := by
      -- Finally commute the two tensor factors back to the textbook order.
      exact
        derivedTensorProduct_comm
          (single₀.obj (((ModuleCat.restrictScalars q).obj P)))
          M

/-- Helper for Lemma 15.103.7: applying `M ⊗_R^L -` to the standard degree-zero triangle of a
short exact module row preserves distinguishedness. -/
private theorem tensor_single_shortExact_triangle_distinguished
    (M : DMod) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    (derivedTensorProduct M).mapTriangle.obj hS.singleTriangle ∈ distTriang DMod := by
  -- Transport the canonical distinguished triangle of the short exact row through the
  -- triangulated functor `M ⊗_R^L -`.
  simpa using
    (derivedTensorProduct M).map_distinguished
      hS.singleTriangle
      hS.singleTriangle_distinguished

/-- Helper for Lemma 15.103.7: after exact restriction of scalars from `R / fR` to `R`, the
quotient tor-amplitude hypothesis kills every nonzero homology group on the corresponding
quotient-side test object. -/
private lemma quotient_test_object_isZero_of_torAmplitude_zero_zero
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (P : ModuleCat Rbar) :
    ∀ i : ℤ, i ≠ 0 →
      IsZero
        ((H i).obj
          (((ModuleCat.restrictScalars
              (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
            (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P))))) := by
  intro i hi
  have hi' : i ∉ Set.Icc (0 : ℤ) 0 := by
    simp [hi]
  have hbase :
      IsZero
        ((HRbar i).obj
          (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P)))) := by
    -- Evaluate the quotient tor-amplitude hypothesis on the chosen `R / fR`-module `P`.
    exact hquotient P i hi'
  -- Exact restriction of scalars commutes with homology, so the same vanishing holds over `R`.
  simpa using
    isZero_homology_restrictScalars_of_isZero
      (A := R) (B := Rbar)
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P)))
      i
      hbase

/-- Helper for Lemma 15.103.7: the restricted quotient-side test object lies in degrees `≥ 0`. -/
private lemma quotient_test_object_isGE_zero_of_torAmplitude_zero_zero
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (P : ModuleCat Rbar) :
    (((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P)))).IsGE 0 := by
  -- Re-express the lower truncation bound as vanishing of negative homology.
  rw [DerivedCategory.isGE_iff]
  intro i hi
  -- Every negative degree is automatically nonzero, so the previous vanishing lemma applies.
  exact
    quotient_test_object_isZero_of_torAmplitude_zero_zero
      (f := f) M hquotient P i hi.ne

/-- Helper for Lemma 15.103.7: the restricted quotient-side test object lies in degrees `≤ 0`. -/
private lemma quotient_test_object_isLE_zero_of_torAmplitude_zero_zero
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (P : ModuleCat Rbar) :
    (((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L ((single₀Rbar (f := f)).obj P)))).IsLE 0 := by
  -- Re-express the upper truncation bound as vanishing of positive homology.
  rw [DerivedCategory.isLE_iff]
  intro i hi
  -- Positive degrees are also nonzero, so the same vanishing transport closes the goal.
  exact
    quotient_test_object_isZero_of_torAmplitude_zero_zero
      (f := f) M hquotient P i (ne_of_gt hi)

/-- Helper for Lemma 15.103.7: the quotient-side torsion outer term is concentrated in degree
`0` after restricting scalars back to `R`. -/
private lemma torsion_quotient_side_test_object_isGE_zero_of_torAmplitude_zero_zero
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    ((((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
        ((single₀Rbar (f := f)).obj (testModule_torsionBy_bar (f := f) N))))).IsGE 0) := by
  -- This is the generic quotient-side lower bound specialized to the torsion test object.
  simpa using
    quotient_test_object_isGE_zero_of_torAmplitude_zero_zero
      (R := R) (f := f) M hquotient (testModule_torsionBy_bar (f := f) N)

/-- Helper for Lemma 15.103.7: the quotient-side torsion outer term is also concentrated in
degree `≤ 0` after restricting scalars back to `R`. -/
private lemma torsion_quotient_side_test_object_isLE_zero_of_torAmplitude_zero_zero
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    ((((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
        ((single₀Rbar (f := f)).obj (testModule_torsionBy_bar (f := f) N))))).IsLE 0) := by
  -- The same specialization gives the upper bound, so the torsion outer term is degree-zero.
  simpa using
    quotient_test_object_isLE_zero_of_torAmplitude_zero_zero
      (R := R) (f := f) M hquotient (testModule_torsionBy_bar (f := f) N)

/-- Helper for Lemma 15.103.7: the quotient-side principal-quotient outer term is concentrated
in degree `0` after restricting scalars back to `R`. -/
private lemma principal_quotient_side_test_object_isGE_zero_of_torAmplitude_zero_zero
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    ((((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
        ((single₀Rbar (f := f)).obj (testModule_principal_quotient_bar (f := f) N))))).IsGE
      0) := by
  -- This is the generic quotient-side lower bound specialized to `N / fN`.
  simpa using
    quotient_test_object_isGE_zero_of_torAmplitude_zero_zero
      (R := R) (f := f) M hquotient (testModule_principal_quotient_bar (f := f) N)

/-- Helper for Lemma 15.103.7: the quotient-side principal-quotient outer term is also
concentrated in degree `≤ 0` after restricting scalars back to `R`. -/
private lemma principal_quotient_side_test_object_isLE_zero_of_torAmplitude_zero_zero
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    ((((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span ({f} : Set R)))).mapDerivedCategory).obj
      (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
        ((single₀Rbar (f := f)).obj (testModule_principal_quotient_bar (f := f) N))))).IsLE
      0) := by
  -- The same specialization gives the matching upper bound for the quotient outer term.
  simpa using
    quotient_test_object_isLE_zero_of_torAmplitude_zero_zero
      (R := R) (f := f) M hquotient (testModule_principal_quotient_bar (f := f) N)

/-- Helper for Lemma 15.103.7: the actual tensor with the `f`-torsion test module lies in degrees
`≥ 0` under the quotient-side tor-amplitude hypothesis. -/
private lemma torsion_test_tensor_isGE_zero_of_quotient
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    (M ⊗[R]^L (single₀.obj (ModuleCat.of R (Submodule.torsionBy R N f)))).IsGE 0 := by
  let q : R →+* Rbar := Ideal.Quotient.mk (Ideal.span ({f} : Set R))
  let eP :
      (single₀.obj (((ModuleCat.restrictScalars q).obj (testModule_torsionBy_bar (f := f) N)))) ≅
        (single₀.obj (ModuleCat.of R (Submodule.torsionBy R N f))) :=
    (single₀).mapIso
      (testModule_torsionBy_bar_restrictScalars_iso (R := R) (f := f) N)
  let e :
      (((ModuleCat.restrictScalars q).mapDerivedCategory).obj
        (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
          ((single₀Rbar (f := f)).obj (testModule_torsionBy_bar (f := f) N))))) ≅
        (M ⊗[R]^L (single₀.obj (ModuleCat.of R (Submodule.torsionBy R N f)))) :=
    tensor_single_restrictScalars_quotient_iso (R := R) (f := f) M
        (testModule_torsionBy_bar (f := f) N) ≪≫
      (derivedTensorProduct M).mapIso eP
  have hbase :
      ((((ModuleCat.restrictScalars q).mapDerivedCategory).obj
        (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
          ((single₀Rbar (f := f)).obj (testModule_torsionBy_bar (f := f) N)))))).IsGE 0 :=
    torsion_quotient_side_test_object_isGE_zero_of_torAmplitude_zero_zero
      (R := R) (f := f) M hquotient N
  -- Transport the quotient-side lower bound across the explicit restriction/tensor comparison.
  rw [DerivedCategory.isGE_iff] at hbase ⊢
  intro i hi
  exact (hbase i hi).of_iso ((H i).mapIso e.symm)

/-- Helper for Lemma 15.103.7: the actual tensor with the principal-quotient test module lies in
degrees `≥ 0` under the quotient-side tor-amplitude hypothesis. -/
private lemma principal_quotient_test_tensor_isGE_zero_of_quotient
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    (M ⊗[R]^L
      (single₀.obj
        (ModuleCat.of R (N ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R N)))))).IsGE 0 := by
  let q : R →+* Rbar := Ideal.Quotient.mk (Ideal.span ({f} : Set R))
  let eP :
      (single₀.obj
        (((ModuleCat.restrictScalars q).obj (testModule_principal_quotient_bar (f := f) N)))) ≅
        (single₀.obj
          (ModuleCat.of R (N ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R N))))) :=
    (single₀).mapIso
      (testModule_principal_quotient_bar_restrictScalars_iso (R := R) (f := f) N)
  let e :
      (((ModuleCat.restrictScalars q).mapDerivedCategory).obj
        (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
          ((single₀Rbar (f := f)).obj (testModule_principal_quotient_bar (f := f) N))))) ≅
        (M ⊗[R]^L
          (single₀.obj
            (ModuleCat.of R (N ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R N)))))) :=
    tensor_single_restrictScalars_quotient_iso (R := R) (f := f) M
        (testModule_principal_quotient_bar (f := f) N) ≪≫
      (derivedTensorProduct M).mapIso eP
  have hbase :
      ((((ModuleCat.restrictScalars q).mapDerivedCategory).obj
        (((M ⊗[R]^L[Rbar]) ⊗[Rbar]^L
          ((single₀Rbar (f := f)).obj
            (testModule_principal_quotient_bar (f := f) N)))))).IsGE 0 :=
    principal_quotient_side_test_object_isGE_zero_of_torAmplitude_zero_zero
      (R := R) (f := f) M hquotient N
  -- Transport the quotient-side lower bound across the explicit restriction/tensor comparison.
  rw [DerivedCategory.isGE_iff] at hbase ⊢
  intro i hi
  exact (hbase i hi).of_iso ((H i).mapIso e.symm)

/-- Helper for Lemma 15.103.7: if `M` has no positive cohomology, then every degree-zero tensor
test object `M ⊗_R^L N[0]` also has no positive cohomology. -/
private lemma tensor_single_isLE_zero_of_isLE_zero
    (M : DMod) (hM : M.IsLE 0) (N : ModuleCat R) :
    (M ⊗[R]^L (single₀.obj N)).IsLE 0 := by
  -- Replace `M` by a strict `≤ 0` complex representative so positive tensor homology can be read
  -- off directly from the ordinary tensor complex.
  rw [DerivedCategory.isLE_iff]
  intro i hi
  letI : M.IsLE 0 := hM
  obtain ⟨K, hKle, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE M 0
  letI : K.IsStrictlyLE 0 := hKle
  let Tsingle :
      CochainComplex (ModuleCat R) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N
  have hTensorTermZero :
      IsZero
        ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).X i) := by
    -- The right-tensored complex has the same positive-degree support as `K`.
    change IsZero (((CategoryTheory.MonoidalCategory.tensorRight N).obj (K.X i)))
    exact CategoryTheory.Functor.map_isZero
      (CategoryTheory.MonoidalCategory.tensorRight N)
      (K.isZero_of_isStrictlyLE 0 i hi)
  have hOrdinaryHomologyZero :
      IsZero ((HomologicalComplex.tensorObj K Tsingle).homology i) := by
    let eSc :=
      tensor_single0_shortComplex_iso (R := R) K N i
    have hMappedHomologyZero :
        IsZero
          ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).sc i).homology := by
      -- With zero middle term, the short complex computing degree-`i` homology is exact.
      exact
        ShortComplex.isZero_homology_of_isZero_X₂
          (S := (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).sc i)
          (by simpa [HomologicalComplex.sc] using hTensorTermZero)
    exact (ShortComplex.homologyMapIso eSc).isZero_iff.2 hMappedHomologyZero
  have hRepresentedHomologyZero :
      IsZero ((H i).obj ((DerivedCategory.Q.obj K) ⊗[R]^L (single₀.obj N))) := by
    -- Transport ordinary tensor-complex homology to the derived tensor product owner.
    exact
      hOrdinaryHomologyZero.of_iso
        (tensorObj_single0_homology_iso_derivedTensor (R := R) K i N)
  -- Finally transport the vanishing statement back across the chosen strict `≤ 0` representative
  -- of `M`.
  exact
    ((H i).mapIso ((derivedTensorProduct ((single₀.obj N))).mapIso eK)).isZero_iff.2
      hRepresentedHomologyZero

/-- Helper for Lemma 15.103.7: multiplication by `f` on a test module is the scalar
endomorphism `f • 𝟙`. -/
private theorem testModule_ofHom_lsmul_eq_smul_id
    (N : ModuleCat R) :
    ModuleCat.ofHom (LinearMap.lsmul R N f) = f • 𝟙 N := by
  -- Both endomorphisms act by the same scalar multiplication on the underlying module.
  ext x
  rfl

/-- Helper for Lemma 15.103.7: the kernel-to-range row for multiplication by `f` becomes a
distinguished triangle in the derived category. -/
private theorem testModule_multiplication_kernel_range_triangle_distinguished
    (N : ModuleCat R) :
    let μ : N →ₗ[R] N := LinearMap.lsmul R N f
    Triangle.mk
        ((single₀).map (ModuleCat.ofHom (LinearMap.ker μ).subtype))
        ((single₀).map (ModuleCat.ofHom μ.rangeRestrict))
        (triangleOfSESδ
          (testModule_multiplication_kernel_range_shortExact (R := R) (f := f) N)) ∈
      distTriang DMod := by
  let μ : N →ₗ[R] N := LinearMap.lsmul R N f
  -- This is exactly the short-exact degree-zero triangle attached to the kernel-range row.
  simpa [μ] using
    DerivedCategory.triangleOfSES_distinguished
      (testModule_multiplication_kernel_range_shortExact (R := R) (f := f) N)

/-- Helper for Lemma 15.103.7: the trivial row `0 → N[0] → N[0]` is distinguished. -/
private theorem testModule_zero_to_single_triangle_distinguished
    (N : ModuleCat R) :
    Triangle.mk (0 : (0 : DMod) ⟶ (single₀.obj N)) (𝟙 (single₀.obj N)) 0 ∈
      distTriang DMod := by
  -- This is the standard contractible distinguished triangle on `N[0]`.
  simpa using contractible_distinguished₁ (single₀.obj N)

/-- Helper for Lemma 15.103.7: the principal-quotient row for multiplication by `f` becomes a
distinguished triangle in the derived category. -/
private theorem testModule_principal_quotient_triangle_distinguished
    (N : ModuleCat R) :
    let fN : Submodule R N := Ideal.span ({f} : Set R) • (⊤ : Submodule R N)
    Triangle.mk
        ((single₀).map (ModuleCat.ofHom fN.subtype))
        ((single₀).map (ModuleCat.ofHom fN.mkQ))
        (triangleOfSESδ
          (testModule_principal_quotient_shortExact (R := R) (f := f) N)) ∈
      distTriang DMod := by
  let fN : Submodule R N := Ideal.span ({f} : Set R) • (⊤ : Submodule R N)
  -- This is the degree-zero triangle attached to the quotient short exact sequence
  -- `0 → fN → N → N / fN → 0`.
  simpa [fN] using
    DerivedCategory.triangleOfSES_distinguished
      (testModule_principal_quotient_shortExact (R := R) (f := f) N)

/-- Helper for Lemma 15.103.7: the canonical quotient row
`0 → im(·f) → K → K / im(·f) → 0` is short exact for any test module `K`. -/
private theorem testModule_range_quotient_shortExact
    (Kmod : ModuleCat R) :
    let μ : Kmod →ₗ[R] Kmod := LinearMap.lsmul R Kmod f
    (ShortComplex.mk
      (ModuleCat.ofHom μ.range.subtype)
      (ModuleCat.ofHom μ.range.mkQ)
      (by
        -- The quotient map kills the image submodule by definition.
        ext x
        simp)).ShortExact := by
  let μ : Kmod →ₗ[R] Kmod := LinearMap.lsmul R Kmod f
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (ModuleCat.ofHom μ.range.subtype)
      (ModuleCat.ofHom μ.range.mkQ)
      (by
        -- The range inclusion followed by the quotient projection is zero.
        ext x
        simp)
  have hExact : Function.Exact μ.range.subtype μ.range.mkQ := by
    -- This is the standard exactness statement for a submodule inclusion and its quotient map.
    simpa using LinearMap.exact_subtype_mkQ μ.range
  simpa [S] using
    ModuleCat.shortComplex_shortExact S hExact (Submodule.injective_subtype _)
      (Submodule.mkQ_surjective μ.range)

/-- Helper for Lemma 15.103.7: the image-quotient row for multiplication by `f` becomes a
distinguished triangle in the derived category. -/
private theorem testModule_range_quotient_triangle_distinguished
    (N : ModuleCat R) :
    let μ : N →ₗ[R] N := LinearMap.lsmul R N f
    Triangle.mk
        ((single₀).map (ModuleCat.ofHom μ.range.subtype))
        ((single₀).map (ModuleCat.ofHom μ.range.mkQ))
        (triangleOfSESδ
          (testModule_range_quotient_shortExact (R := R) (f := f) N)) ∈
      distTriang DMod := by
  let μ : N →ₗ[R] N := LinearMap.lsmul R N f
  -- This is the degree-zero triangle attached to `0 → im(·f) → N → N / im(·f) → 0`.
  simpa [μ] using
    DerivedCategory.triangleOfSES_distinguished
      (testModule_range_quotient_shortExact (R := R) (f := f) N)

/-- Helper for Lemma 15.103.7: the kernel of multiplication by `f` is canonically the
`f`-torsion submodule. -/
private noncomputable def testModule_kernel_iso_torsionBy
    (Kmod : ModuleCat R) :
    ModuleCat.of R (LinearMap.ker (LinearMap.lsmul R Kmod f)) ≅
      ModuleCat.of R (Submodule.torsionBy R Kmod f) :=
  -- The two submodule owners are definitionally the same equation `f • x = 0`.
  (LinearEquiv.ofEq _ _
    (testModule_ker_lsmul_eq_torsionBy (R := R) (f := f) (Kmod := Kmod))).toModuleIso

/-- Helper for Lemma 15.103.7: quotienting by the image of multiplication by `f` agrees with
quotienting by the principal submodule `fK`. -/
private noncomputable def testModule_range_quotient_iso_principal_quotient
    (Kmod : ModuleCat R) :
    ModuleCat.of R (Kmod ⧸ LinearMap.range (LinearMap.lsmul R Kmod f)) ≅
      ModuleCat.of R (Kmod ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod))) :=
  -- The image submodule is exactly the principal-ideal multiple computed earlier.
  (Submodule.quotEquivOfEq
    (LinearMap.range (LinearMap.lsmul R Kmod f))
    (Ideal.span ({f} : Set R) • (⊤ : Submodule R Kmod))
    (testModule_range_lsmul_eq_span_singleton_smul_top
      (R := R) (f := f) (Kmod := Kmod))).toModuleIso

/-- Helper for Lemma 15.103.7: the localization and quotient hypotheses force every degree-zero
tensor test object `M ⊗_R^L N[0]` to lie in degrees `≥ 0`. -/
private theorem tensor_single_multiplication_cone_isGE_neg_one_of_quotient
    (M : DMod)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    ∃ (C : DMod) (g : M ⊗[R]^L (single₀.obj N) ⟶ C) (δ : C ⟶ (M ⊗[R]^L (single₀.obj N))⟦(1 : ℤ)⟧),
      Triangle.mk (f • 𝟙 (M ⊗[R]^L (single₀.obj N))) g δ ∈ distTriang DMod ∧
        C.IsGE (-1) := by
  let μ : N →ₗ[R] N := LinearMap.lsmul R N f
  let Tker : Triangle DMod :=
    Triangle.mk
      ((single₀).map (ModuleCat.ofHom μ.ker.subtype))
      ((single₀).map (ModuleCat.ofHom μ.rangeRestrict))
      (triangleOfSESδ
        (testModule_multiplication_kernel_range_shortExact (R := R) (f := f) N))
  have hTker : Tker ∈ distTriang DMod := by
    -- This is the kernel-to-image triangle for multiplication by `f` on `N[0]`.
    simpa [Tker, μ] using
      testModule_multiplication_kernel_range_triangle_distinguished
        (R := R) (f := f) N
  let T₁₂ : Triangle DMod := ((derivedTensorProduct M).mapTriangle.obj Tker).rotate
  have hT₁₂ : T₁₂ ∈ distTriang DMod := by
    -- Rotating the tensorized kernel-to-image triangle puts `im(·f)` in the middle.
    exact rot_of_distTriang _ ((derivedTensorProduct M).map_distinguished Tker hTker)
  let Trange : Triangle DMod :=
    Triangle.mk
      ((single₀).map (ModuleCat.ofHom μ.range.subtype))
      ((single₀).map (ModuleCat.ofHom μ.range.mkQ))
      (triangleOfSESδ
        (testModule_range_quotient_shortExact (R := R) (f := f) N))
  have hTrange : Trange ∈ distTriang DMod := by
    -- This is the quotient triangle `im(·f) → N → N / im(·f)`.
    simpa [Trange, μ] using
      testModule_range_quotient_triangle_distinguished
        (R := R) (f := f) N
  let T₂₃ : Triangle DMod := (derivedTensorProduct M).mapTriangle.obj Trange
  have hT₂₃ : T₂₃ ∈ distTriang DMod := by
    -- Tensoring preserves distinguished triangles for these degree-zero module rows.
    exact (derivedTensorProduct M).map_distinguished Trange hTrange
  obtain ⟨C, g, δ, hT₁₃⟩ :=
    distinguished_cocone_triangle (f • 𝟙 (M ⊗[R]^L (single₀.obj N)))
  have hcomp :
      T₁₂.mor₁ ≫ T₂₃.mor₁ = f • 𝟙 (M ⊗[R]^L (single₀.obj N)) := by
    -- Route correction: factor multiplication by `f` through its image on the module side first,
    -- then transport that factorization through `N[0]` and `M ⊗_R^L -`.
    calc
      T₁₂.mor₁ ≫ T₂₃.mor₁ =
          (derivedTensorProduct M).map
            (((single₀).map (ModuleCat.ofHom μ.rangeRestrict)) ≫
              ((single₀).map (ModuleCat.ofHom μ.range.subtype))) := by
            rfl
      _ = (derivedTensorProduct M).map ((single₀).map (ModuleCat.ofHom μ)) := by
            congr 1
            ext x
            rfl
      _ = (derivedTensorProduct M).map (f • 𝟙 (single₀.obj N)) := by
            rw [testModule_ofHom_lsmul_eq_smul_id (R := R) (f := f) N]
      _ = f • 𝟙 (M ⊗[R]^L (single₀.obj N)) := by
            rw [Functor.map_smul, Functor.map_id]
  let O := someOctahedron hcomp hT₁₂ hT₂₃ hT₁₃
  let eKernel :
      (M ⊗[R]^L (single₀.obj (ModuleCat.of R (LinearMap.ker μ)))) ≅
        (M ⊗[R]^L (single₀.obj (ModuleCat.of R (Submodule.torsionBy R N f)))) :=
    (derivedTensorProduct M).mapIso
      ((single₀).mapIso (testModule_kernel_iso_torsionBy (R := R) (f := f) N))
  let eQuot :
      (M ⊗[R]^L (single₀.obj (ModuleCat.of R (N ⧸ LinearMap.range μ)))) ≅
        (M ⊗[R]^L
          (single₀.obj
            (ModuleCat.of R (N ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R N)))))) :=
    (derivedTensorProduct M).mapIso
      ((single₀).mapIso
        (testModule_range_quotient_iso_principal_quotient (R := R) (f := f) N))
  have hKernelGE0 :
      (M ⊗[R]^L (single₀.obj (ModuleCat.of R (LinearMap.ker μ)))).IsGE 0 := by
    have hTorsionGE0 :
        (M ⊗[R]^L (single₀.obj (ModuleCat.of R (Submodule.torsionBy R N f)))).IsGE 0 :=
      torsion_test_tensor_isGE_zero_of_quotient
        (R := R) (f := f) M hquotient N
    -- Transport the quotient-side torsion bound back across the kernel identification `eKernel`.
    rw [DerivedCategory.isGE_iff] at hTorsionGE0 ⊢
    intro i hi
    exact (hTorsionGE0 i hi).of_iso ((H i).mapIso eKernel.symm)
  have hT₁₂obj₁ : T₁₂.obj₁.IsGE (-1) := by
    -- The first octahedral outer term is the shifted kernel tensor term.
    letI : (M ⊗[R]^L (single₀.obj (ModuleCat.of R (LinearMap.ker μ)))).IsGE 0 := hKernelGE0
    simpa [T₁₂, Tker] using
      (DerivedCategory.TStructure.t.isGE_shift
        (M ⊗[R]^L (single₀.obj (ModuleCat.of R (LinearMap.ker μ)))) 0 1 (-1) (by omega))
  have hQuotGE0 :
      (M ⊗[R]^L (single₀.obj (ModuleCat.of R (N ⧸ LinearMap.range μ)))).IsGE 0 := by
    have hPrincipalGE0 :
        (M ⊗[R]^L
          (single₀.obj
            (ModuleCat.of R (N ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R N)))))).IsGE 0 :=
      principal_quotient_test_tensor_isGE_zero_of_quotient
        (R := R) (f := f) M hquotient N
    -- Transport the quotient-side principal-quotient bound back across `eQuot`.
    rw [DerivedCategory.isGE_iff] at hPrincipalGE0 ⊢
    intro i hi
    exact (hPrincipalGE0 i hi).of_iso ((H i).mapIso eQuot.symm)
  have hC : C.IsGE (-1) := by
    -- The octahedral comparison triangle has outer terms in degrees `≥ -1` and `≥ 0`,
    -- so the cone term itself lies in degrees `≥ -1`.
    exact
      DerivedCategory.TStructure.t.isGE₂ O.triangle O.mem (-1) hT₁₂obj₁
        (DerivedCategory.TStructure.t.isGE_of_ge O.triangle.obj₃ (-1) 0 (by omega) hQuotGE0)
  exact ⟨C, g, δ, hT₁₃, hC⟩

/-- Helper for Lemma 15.103.7: the localization and quotient hypotheses force every degree-zero
tensor test object `M ⊗_R^L N[0]` to lie in degrees `≥ 0`. -/
private lemma test_tensor_isGE_zero_of_localizationAway_and_quotient
    (M : DMod)
    (hlocalization : HasTorAmplitudeIn (M ⊗[R]^L[Rf]) 0 0)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0)
    (N : ModuleCat R) :
    (M ⊗[R]^L (single₀.obj N)).IsGE 0 := by
  obtain ⟨C, g, δ, hT, hC⟩ :=
    tensor_single_multiplication_cone_isGE_neg_one_of_quotient
      (R := R) (f := f) M hquotient N
  -- Once the multiplication cone is known to be concentrated in degrees `≥ -1`, the localized
  -- negative-homology vanishing from the localization hypothesis feeds directly into
  -- Lemma `15.103.6`.
  exact
    isGE_zero_of_localized_isZero_and_cone_isGE_neg_one
      (R := R) (f := f) (M := M ⊗[R]^L (single₀.obj N))
      (C := C) (g := g) (δ := δ) hT
      (fun i hi ↦
        localized_homology_isZero_of_localizationAway_torAmplitude_zero_zero
          (R := R) (f := f) M hlocalization N i hi.ne)
      hC

/-- Canonical companion to Lemma 15.103.7: under the source hypotheses, `M` has tor-amplitude in
`[0, 0]`. -/
theorem hasTorAmplitudeIn_zero_zero_of_isLE_zero_of_localizationAway_and_quotient
    (M : DMod)
    (hM : M.IsLE 0)
    (hlocalization : HasTorAmplitudeIn (M ⊗[R]^L[Rf]) 0 0)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0) :
    HasTorAmplitudeIn M 0 0 := by
  intro N i hi
  have hGE :
      (M ⊗[R]^L (single₀.obj N)).IsGE 0 :=
    test_tensor_isGE_zero_of_localizationAway_and_quotient
      (R := R) (f := f) M hlocalization hquotient N
  have hLE :
      (M ⊗[R]^L (single₀.obj N)).IsLE 0 :=
    tensor_single_isLE_zero_of_isLE_zero (R := R) M hM N
  have hi_ne : i ≠ 0 := by
    intro hi_zero
    exact hi (by simp [hi_zero])
  rcases lt_or_gt_of_ne hi_ne with hi_neg | hi_pos
  · -- Negative degrees vanish because the tested tensor object is already in `D^{≥ 0}`.
    rw [DerivedCategory.isGE_iff] at hGE
    exact hGE i hi_neg
  · -- Positive degrees vanish because the same tested tensor object lies in `D^{≤ 0}`.
    rw [DerivedCategory.isLE_iff] at hLE
    exact hLE i hi_pos

-- Proof sketch: translate the source-facing localization and quotient hypotheses to
-- `HasTorAmplitudeIn _ 0 0` via `hasTorAmplitudeIn_zero_zero_iff_exists_flat_module`, apply the
-- canonical tor-amplitude companion above, and then translate the conclusion back to the source
-- wording by the same bridge.
/-- Lemma 15.103.7: if `M` has no positive cohomology, the derived localization
`M \otimes_R^{\mathbf L} R_f` is isomorphic to a flat module placed in degree `0`, and the
derived reduction `M \otimes_R^{\mathbf L} R/fR` is isomorphic to a flat module placed in degree
`0`, then `M` itself is isomorphic in `D(R)` to a flat `R`-module placed in degree `0`. -/
@[stacks 0H85]
theorem isFlatModuleInDegreeZero_of_localizationAway_and_quotient
    (M : DMod)
    (hM : M.IsLE 0)
    (hlocalization :
      ∃ N : ModuleCat Rf, Module.Flat Rf N ∧
        IsIsomorphic (M ⊗[R]^L[Rf]) ((single₀Rf (f := f)).obj N))
    (hquotient :
      ∃ N : ModuleCat Rbar, Module.Flat Rbar N ∧
        IsIsomorphic (M ⊗[R]^L[Rbar]) ((single₀Rbar (f := f)).obj N)) :
    ∃ N : ModuleCat R, Module.Flat R N ∧ IsIsomorphic M ((single₀).obj N) := by
  -- Route correction: keep the source-facing proof on the tor-amplitude route and isolate the
  -- remaining work inside the two structural helper lemmas above.
  have hlocalization_amp : HasTorAmplitudeIn (M ⊗[R]^L[Rf]) 0 0 := by
    -- Translate the localized flat-module formulation back to the canonical tor-amplitude owner.
    exact
      (hasTorAmplitudeIn_zero_zero_iff_exists_flat_module (R := Rf)
        (M := M ⊗[R]^L[Rf])).2 (by
          simpa [single₀Rf] using hlocalization)
  have hquotient_amp : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0 := by
    -- Do the same translation for the quotient hypothesis over `R / fR`.
    exact
      (hasTorAmplitudeIn_zero_zero_iff_exists_flat_module (R := Rbar)
        (M := M ⊗[R]^L[Rbar])).2 (by
          simpa [single₀Rbar] using hquotient)
  have htor : HasTorAmplitudeIn M 0 0 :=
    hasTorAmplitudeIn_zero_zero_of_isLE_zero_of_localizationAway_and_quotient
      (R := R) (f := f) M hM hlocalization_amp hquotient_amp
  -- Translate the recovered tor-amplitude statement back to the textbook flat-module wording.
  exact
    (hasTorAmplitudeIn_zero_zero_iff_exists_flat_module (R := R) (M := M)).1 htor

end

end CategoryTheory
