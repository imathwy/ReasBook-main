import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_14
import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_15
import StacksProject_2024.stacks_project.Chap13.Lemma_13_30_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_7
import StacksProject_2024.stacks_project.Chap13.Lemma_13_33_7
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_56_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_17
import StacksProject_2024.stacks_project.Chap15.«15_74_0_2»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_74_4
import StacksProject_2024.stacks_project.Chap19.Theorem_19_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape
open Opposite
open scoped DerivedInternalHom
open scoped DerivedTensorProduct
open scoped TensorProduct

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling:
- primary domain: the Stacks-project object `T(K, f)` and its vanishing criterion in `D(A)`;
- sampled owner-side declarations:
  `(ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory`,
  `DerivedCategory.singleFunctor`,
  `Functor.ofOpSequence`,
  `CategoryTheory.IsDerivedLimit`;
- best owner abstraction: keep the source-facing owner `T(K, f)` visible, realized through the
  canonical internal-Hom owner on `D(A)` under an ambient monoidal-closed structure, while the
  localization-away predicate remains the canonical owner-independent vanishing criterion;
- primitive data: `f : A`, `K : D(A)`, and the restriction-of-scalars functor `D(A_f) ⥤ D(A)`;
- derived API: the Milnor tower model of `T(K, f)`, the equivalence theorem to the vanishing
  predicate, and the module-level specialization `ModuleCat.moduleLocalizationAwayTVanishing`.

Layer triage:
- `source-facing`: `localizationAwayT H f K`, the textbook `T(K, f)`;
- `core/canonical`: the owner-independent predicate
  `localizationAwayDerivedHomVanishingCondition f K`;
- `bridge/view`: `localizationAwayTower`, `localizationAwayT_isDerivedLimit`, the vanishing
  equivalence, and the degree-zero module specialization. -/

/-- Lemma 15.92.1 source-facing owner: after restriction of scalars along `A → A_f`, every
morphism from an object of `D(A_f)` to `K` is zero. -/
def localizationAwayDerivedHomVanishingCondition (f : A) (K : DMod) : Prop :=
  ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
    Subsingleton
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶ K)

/-- The constant tower `\cdots \xrightarrow{f} K \xrightarrow{f} K \xrightarrow{f} K` in `D(A)`,
with transition maps given by multiplication by `f`. -/
abbrev localizationAwayTower (f : A) (K : DMod) : ℕᵒᵖ ⥤ DMod :=
  let X : ℕ → DMod := fun _ ↦ K
  let step : (n : ℕ) → X (n + 1) ⟶ X n := fun _ ↦ f • 𝟙 K
  Functor.ofOpSequence step

section Monoidal

variable (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local instance : MonoidalCategory DMod := inferInstance

/-- Helper for Lemma 15.92.1: the canonical localization functor `Q` inherits the monoidal
structure from the homotopy-category quotient. -/
private noncomputable instance derivedCategory_q_monoidal
    (R : Type u) [CommRing R] :
    (DerivedCategory.Q :
      CochainComplex (ModuleCat R) ℤ ⥤ DerivedCategory (ModuleCat R)).Monoidal := by
  -- Re-express `Q` as the homotopy quotient followed by `Qh`, where the monoidal structure is
  -- already available from the owner construction.
  change (((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat R)))).Monoidal
  infer_instance

/-- Helper for Lemma 15.92.1: the derived category of modules carries the induced monoidal
structure once the monoidal structure on `Q` is fixed. -/
private instance derivedModule_monoidal
    (R : Type u) [CommRing R] :
    MonoidalCategory (DerivedCategory (ModuleCat R)) := inferInstance

/-- Helper for Lemma 15.92.1: the localization map `A → A_f` is an epimorphism of commutative
rings. Equivalently, restriction of scalars along this map is fully faithful. -/
instance localizationAway_epi (f : A) :
    Epi (CommRingCat.ofHom (algebraMap A (Localization.Away f))) := by
  letI : Algebra.IsEpi A (Localization.Away f) := by
    refine (algebra_isEpi_iff_includeLeft_eq_includeRight).2 ?_
    -- Both tensor-factor maps agree on the image of `A`, so localization extensionality
    -- identifies them on all of `A_f`.
    simpa using
      (IsLocalization.algHom_ext (W := Submonoid.powers f)
        (Algebra.ext_id
          (TensorProduct A (Localization.Away f) (Localization.Away f))
          (Algebra.TensorProduct.includeLeft.comp (Algebra.algHom A A (Localization.Away f)))
          (Algebra.TensorProduct.includeRight.comp (Algebra.algHom A A (Localization.Away f)))))
  exact
    (CommRingCat.epi_iff_epi (R := A) (S := Localization.Away f)).2
      (inferInstance : Algebra.IsEpi A (Localization.Away f))

/-- Helper for Lemma 15.92.1: the localization restriction/coextension adjunction has invertible
unit on `A_f`-modules, since restriction of scalars along `A → A_f` is fully faithful. -/
noncomputable def localizationAway_module_unit_iso (f : A) :
    𝟭 (ModuleCat (Localization.Away f)) ≅
      ModuleCat.restrictScalars (algebraMap A (Localization.Away f)) ⋙
        ModuleCat.coextendScalars (algebraMap A (Localization.Away f)) := by
  let moduleAdj := ModuleCat.restrictCoextendScalarsAdj (algebraMap A (Localization.Away f))
  let hff :
      (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).FullyFaithful :=
    restrictScalars_fullyFaithful_of_epi (algebraMap A (Localization.Away f))
  letI :
      (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).Full := by
    exact hff.full
  letI :
      (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).Faithful := by
    exact hff.faithful
  letI : IsIso moduleAdj.unit := moduleAdj.unit_isIso_of_L_fully_faithful
  -- This packages the underived localization idempotence needed for the later derived comparison.
  exact asIso moduleAdj.unit

/-- Helper for Lemma 15.92.1: the module-level localization/coextension unit lifts objectwise to
cochain complexes. -/
noncomputable def localizationAway_complex_unit_iso (f : A) :
    𝟭 (CochainComplex (ModuleCat (Localization.Away f)) ℤ) ≅
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
        (up ℤ)) ⋙
        ((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)) := by
  -- Lift the underived unit isomorphism to the homological-complex level.
  exact
    (Functor.mapHomologicalComplexIdIso (ModuleCat (Localization.Away f)) (up ℤ)).symm ≪≫
      NatIso.mapHomologicalComplex (localizationAway_module_unit_iso (A := A) f) (up ℤ)

/-- Helper for Lemma 15.92.1: scalar extension back to `A_f` after restriction of scalars is
already the identity on `A_f`-modules. -/
noncomputable def localizationAway_module_counit_iso (f : A) :
    ModuleCat.restrictScalars (algebraMap A (Localization.Away f)) ⋙
      ModuleCat.extendScalars (algebraMap A (Localization.Away f)) ≅
    𝟭 (ModuleCat (Localization.Away f)) := by
  let moduleAdj := ModuleCat.extendRestrictScalarsAdj (algebraMap A (Localization.Away f))
  let hff :
      (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).FullyFaithful :=
    restrictScalars_fullyFaithful_of_epi (algebraMap A (Localization.Away f))
  letI :
      (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).Full := by
    exact hff.full
  letI :
      (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).Faithful := by
    exact hff.faithful
  -- Since restriction is fully faithful for the localization epimorphism, the counit is an
  -- isomorphism on every localized module.
  letI : IsIso moduleAdj.counit := moduleAdj.counit_isIso_of_R_fully_faithful
  exact asIso moduleAdj.counit

/-- Helper for Lemma 15.92.1: the module-level localization/extension counit lifts objectwise to
cochain complexes. -/
noncomputable def localizationAway_complex_counit_iso (f : A) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
      (up ℤ)) ⋙
      ((ModuleCat.extendScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
        (up ℤ)) ≅
    𝟭 (CochainComplex (ModuleCat (Localization.Away f)) ℤ) := by
  -- Lift the underived counit isomorphism to cochain complexes termwise.
  exact NatIso.mapHomologicalComplex (localizationAway_module_counit_iso (A := A) f) (up ℤ)

/-- Helper for Lemma 15.92.1: exact scalar extension along `A → A_f` is additive on module
categories. -/
local instance localizationAway_extendScalars_additive (f : A) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap A (Localization.Away f))).left_adjoint_additive

/-- Helper for Lemma 15.92.1: exact scalar extension to `A_f` preserves finite limits because the
localization map is flat. -/
local instance localizationAway_extendScalars_preservesFiniteLimits (f : A) :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr
      (show Module.Flat A (Localization.Away f) from inferInstance))

/-- Helper for Lemma 15.92.1: exact scalar extension carries the free rank-one `A`-module to the
localized ring module. -/
noncomputable def localizationAway_extendScalars_ring_iso (f : A) :
    (ModuleCat.extendScalars (algebraMap A (Localization.Away f))).obj (ModuleCat.of A A) ≅
      ModuleCat.of (Localization.Away f) (Localization.Away f) := by
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) ≃ₗ[Localization.Away f]
        Localization.Away f :=
    { __ := AddEquiv.refl _
      map_smul' := fun _ _ ↦ rfl }
  letI :
      IsScalarTower A (Localization.Away f)
        ↑((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eTensor :
      (ModuleCat.extendScalars (algebraMap A (Localization.Away f))).obj (ModuleCat.of A A) ≅
        ModuleCat.of (Localization.Away f) ((Localization.Away f) ⊗[A] A) := by
    -- Rewrite exact scalar extension of the base ring as the standard tensor-product module.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl A A)).toModuleIso
  -- Collapse the right tensor factor by the standard tensor-right-unit isomorphism.
  exact eTensor ≪≫
    (Algebra.TensorProduct.rid
      A
      (Localization.Away f)
      (Localization.Away f)).toLinearEquiv.toModuleIso

/-- Helper for Lemma 15.92.1: exact coextension along `A → A_f` is additive on module
categories. -/
local instance localizationAway_coextendScalars_additive (f : A) :
    (ModuleCat.coextendScalars.{u, u, u} (algebraMap A (Localization.Away f))).Additive :=
  (ModuleCat.restrictCoextendScalarsAdj.{u, u, u}
    (algebraMap A (Localization.Away f))).right_adjoint_additive

/-- Helper for Lemma 15.92.1: exact scalar extension sends the degree-zero complex `A[0]` to the
degree-zero complex `A_f[0]`. -/
noncomputable def localizationAway_single_extendScalars_iso (f : A) :
    ((ModuleCat.extendScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      ((single₀).obj (ModuleCat.of A A))) ≅
      ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f))) := by
  -- First replace exact derived scalar extension by the standard derived-tensor owner, compute
  -- that owner on `A[0]`, and finally collapse the extended rank-one module to `A_f`.
  calc
    ((ModuleCat.extendScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        ((single₀).obj (ModuleCat.of A A))) ≅
        (CategoryTheory.derivedTensorWithAlgebra
          (algebraMap A (Localization.Away f))).obj
          ((single₀).obj (ModuleCat.of A A)) :=
      (CategoryTheory.extendScalars_mapDerivedCategory_iso
        (R := A) (R' := Localization.Away f)).app _
    _ ≅
        ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away f))).obj
            (ModuleCat.of A A))) :=
      CategoryTheory.derivedTensorWithAlgebra_single_iso
        (R := A) (R' := Localization.Away f) (ModuleCat.of A A)
    _ ≅
        ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) :=
      (DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).mapIso
        (localizationAway_extendScalars_ring_iso (A := A) f)

/-- Helper for Lemma 15.92.1: restricting scalars sends the localized degree-zero complex to the
degree-zero complex of the localized ring viewed as an `A`-module. -/
noncomputable def localizationAway_restrict_single_iso (f : A) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f)))) ≅
      ((single₀).obj (ModuleCat.of A (Localization.Away f))) := by
  let σ := algebraMap A (Localization.Away f)
  let M : ModuleCat (Localization.Away f) := ModuleCat.of (Localization.Away f) (Localization.Away f)
  let eLinear :
      ↑((ModuleCat.restrictScalars σ).obj M) ≃ₗ[A] Localization.Away f :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ by simpa [σ, Algebra.smul_def] }
  let eM :
      ((ModuleCat.restrictScalars σ).obj M) ≅ ModuleCat.of A (Localization.Away f) :=
    eLinear.toModuleIso
  -- Since restriction of scalars is exact, the standard `singleFunctor` comparison already gives
  -- the required bridge on the derived category, and the underlying `A`-module is the canonical
  -- owner `ModuleCat.of A (Localization.Away f)`.
  exact
    ((((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ
          (ModuleCat (Localization.Away f)) (0 : ℤ)).app M)) ≪≫
      (ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor
          (ModuleCat (Localization.Away f)) (0 : ℤ)).obj M) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars σ)
          (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        ((ModuleCat.restrictScalars σ).obj M)).symm) ≪≫
      (single₀).mapIso eM

/-- Helper for Lemma 15.92.1: after identifying a localized complex with scalar extension of its
restricted complex via the localization counit, restricting the tensor by `A_f[0]` agrees with
tensoring the restricted complex by the restricted degree-zero localization object. -/
noncomputable def restrict_localization_single_tensor_complex_iso
    (f : A) (L : CochainComplex (ModuleCat (Localization.Away f)) ℤ) :
    (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
      (up ℤ)).obj
      (HomologicalComplex.tensorObj
        ((CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f)))
        L)) ≅
      HomologicalComplex.tensorObj
        (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj
          ((CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
            (ModuleCat.of (Localization.Away f) (Localization.Away f))))
        (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj L) :=
  let σ := algebraMap A (Localization.Away f)
  let singleAway :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
      (ModuleCat.of (Localization.Away f) (Localization.Away f))
  let res := ((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ))
  let counit := (localizationAway_complex_counit_iso (A := A) f).app L
  -- First rewrite `L` as the exact scalar extension of its restricted complex.
  (res.mapIso
      (((tensoringLeft (CochainComplex (ModuleCat (Localization.Away f)) ℤ)).obj
          singleAway).mapIso counit.symm)) ≪≫
    -- Then use the fixed cochain-level base-change comparison from Lemma `15.59.3`.
    (restrictScalars_tensorObj_extendScalars_iso σ singleAway (res.obj L))

/-- The textbook object `T(K, f)`, realized canonically as the derived internal Hom
`R\mathrm{Hom}_A(A_f, K)` in `D(A)`. -/
abbrev localizationAwayT (f : A) (K : DMod) : DMod := by
  letI := H
  exact (ihom ((single₀).obj (ModuleCat.of A (Localization.Away f)))).obj K

/-- Helper for Lemma 15.92.1: right derived tensoring with `A[0]` is naturally the identity
functor on `D(A)`. -/
private noncomputable def ringSingle_rightDerivedTensor_natIso :
    CategoryTheory.derivedTensorProduct ((single₀).obj (ModuleCat.of A A)) ≅ 𝟭 DMod := by
  refine NatIso.ofComponents
    (fun K ↦
      -- Commute the fixed `A[0]` tensor factor to the left and then collapse it by the tensor
      -- unit comparison from `15.74.0.2`.
      (derivedTensorProduct_comm K ((single₀).obj (ModuleCat.of A A))) ≪≫
        singleZeroDerivedTensorIso K)
    ?_
  intro K L g
  -- Both component isomorphisms are built from natural monoidal comparisons, so the resulting
  -- functor isomorphism is natural in `g`.
  simp only [singleZeroDerivedTensorIso, derivedTensorProduct_comm,
    derivedCategory_tensorObj_iso_derivedTensorProduct,
    tensoringRightIsoDerivedTensorProduct_hom_app,
    tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit, Category.assoc]

/-- Helper for Lemma 15.92.1: the derived internal-Hom functor out of `A[0]` is naturally the
identity functor on `D(A)`. -/
private noncomputable def ringSingle_internalHom_natIso :
    letI := H
    ihom ((single₀).obj (ModuleCat.of A A)) ≅ 𝟭 DMod := by
  letI := H
  let adjRing :
      CategoryTheory.derivedTensorProduct ((single₀).obj (ModuleCat.of A A)) ⊣
        ihom ((single₀).obj (ModuleCat.of A A)) :=
    H.derivedTensorAdj ((single₀).obj (ModuleCat.of A A))
  let adjId : 𝟭 DMod ⊣ 𝟭 DMod := (Adjunction.id : 𝟭 DMod ⊣ 𝟭 DMod)
  -- Route correction: instead of unfolding `RHom(A[0], -)` directly, identify its left adjoint
  -- with the identity and transport the right adjoint by uniqueness.
  exact
    Adjunction.rightAdjointUniq
      (adjRing.ofNatIsoLeft (ringSingle_rightDerivedTensor_natIso (A := A)))
      adjId

/-- Helper for Lemma 15.92.1: for every `K`, the object `RHom_A(A[0], K)` is canonically
isomorphic to `K`. -/
noncomputable def ringSingle_rhom_iso (K : DMod) :
    RHom[H]((single₀).obj (ModuleCat.of A A), K) ≅ K := by
  letI := H
  -- Evaluate the natural internal-Hom/unit comparison at `K`.
  simpa using (ringSingle_internalHom_natIso (A := A) (H := H)).app K

/-- Helper for Lemma 15.92.1: on the degree-zero ring object `A[0]`, the morphism induced by
multiplication by `f` is the scalar endomorphism `f • 𝟙`. -/
private theorem ringSingle_map_mul_eq_smul (f : A) :
    (single₀).map (ModuleCat.ofHom (LinearMap.mulRight A f)) =
      f • 𝟙 ((single₀).obj (ModuleCat.of A A)) := by
  -- First identify the module endomorphism `a ↦ f * a` with scalar multiplication on the free
  -- rank-one module, then apply functoriality of `single₀`.
  have hmul :
      ModuleCat.ofHom (LinearMap.mulRight A f) = f • 𝟙 (ModuleCat.of A A) := by
    apply ModuleCat.hom_injective
    ext a
    simp [LinearMap.mulRight_apply, mul_comm]
  rw [hmul]
  simpa using (single₀.map_smul f (𝟙 (ModuleCat.of A A)))

/-- Helper for Lemma 15.92.1: the source-faithful sequential diagram
`A[0] --f--> A[0] --f--> ...` in `D(A)`. -/
private abbrev localizationAway_ringSingle_step (f : A) :
    ∀ n : ℕ, (single₀).obj (ModuleCat.of A A) ⟶ (single₀).obj (ModuleCat.of A A) :=
  fun _ ↦ (single₀).map (ModuleCat.ofHom (LinearMap.mulRight A f))

/-- Helper for Lemma 15.92.1: the canonical direct system on `A[0]` with transition `f • 𝟙`. -/
private abbrev localizationAway_ringSingle_sequence (f : A) : ℕ ⥤ DMod :=
  Functor.ofSequence (localizationAway_ringSingle_step (A := A) f)

/-- Helper for Lemma 15.92.1: the source-variable internal-Hom tower obtained from the explicit
`A[0] --f--> A[0] --f--> ...` presentation. -/
private abbrev localizationAway_ringSingle_internalHomTower
    (f : A) (K : DMod) : ℕᵒᵖ ⥤ DMod := by
  letI := H
  exact
    (localizationAway_ringSingle_sequence (A := A) f).op ⋙
      ((MonoidalClosed.internalHom).flip.obj K)

/-- Helper for Lemma 15.92.1: the successor map in the explicit `A[0]`-sequence is literally
the scalar endomorphism `f • 𝟙`. -/
private theorem localizationAway_ringSingle_sequence_map_succ
    (f : A) (n : ℕ) :
    (localizationAway_ringSingle_sequence (A := A) f).map (homOfLE (Nat.le_succ n)) =
      f • 𝟙 ((single₀).obj (ModuleCat.of A A)) := by
  -- Expose the `Functor.ofSequence` successor map and rewrite it through the scalar-action
  -- description of multiplication by `f` on `A[0]`.
  simpa [localizationAway_ringSingle_sequence, localizationAway_ringSingle_step,
    Functor.ofSequence_map_homOfLE_succ] using ringSingle_map_mul_eq_smul (A := A) f

/-- Helper for Lemma 15.92.1: each stage of the source-faithful internal-Hom tower is canonically
the fixed object `K`. -/
private noncomputable def localizationAway_ringSingle_internalHomTower_obj_iso
    (f : A) (K : DMod) (n : ℕ) :
    (localizationAway_ringSingle_internalHomTower (A := A) H f K).obj (op n) ≅ K := by
  letI := H
  -- Every stage is `RHom_A(A[0], K)`, so the ring-object comparison collapses it back to `K`.
  change RHom[H]((single₀).obj (ModuleCat.of A A), K) ≅ K
  exact ringSingle_rhom_iso (A := A) (H := H) K

/-- Helper for Lemma 15.92.1: the successor map in the source-faithful internal-Hom tower is
precomposition by the scalar endomorphism `f • 𝟙` of `A[0]`. -/
private theorem localizationAway_ringSingle_internalHomTower_map_succ
    (f : A) (K : DMod) (n : ℕ) :
    (localizationAway_ringSingle_internalHomTower (A := A) H f K).map
        (homOfLE (Nat.le_succ n)).op =
      (MonoidalClosed.pre
        (f • 𝟙 ((single₀).obj (ModuleCat.of A A)))).app K := by
  letI := H
  -- Unfold the composite tower once and rewrite the source successor map by the explicit
  -- scalar description on `A[0]`.
  simp [localizationAway_ringSingle_internalHomTower,
    localizationAway_ringSingle_sequence_map_succ (A := A) f n]

/-- Helper for Lemma 15.92.1: the target Milnor tower is literally the constant `f`-tower on
`K`, so its successor map is `f • 𝟙_K`. -/
private theorem localizationAwayTower_map_succ
    (f : A) (K : DMod) (n : ℕ) :
    (localizationAwayTower f K).map (homOfLE (Nat.le_succ n)).op =
      f • 𝟙 K := by
  -- Unfold the owner-level inverse system once so later comparisons can target the explicit
  -- scalar endomorphism on `K`.
  simpa [localizationAwayTower, Functor.ofOpSequence_map_homOfLE_succ]

/-- Helper for Lemma 15.92.1: before using localization idempotence, morphisms into `T(K,f)` are
just the adjoint transposes of morphisms out of tensoring with `A_f[0]`. -/
noncomputable def localizationAwayT_hom_equiv_tensor
    (f : A) (X K : DMod) :
    (X ⟶ localizationAwayT H f K) ≃
      ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ X) ⟶ K) := by
  -- First isolate the owner-level tensor/internal-Hom adjunction; the localization-specific
  -- comparison is deferred to a separate bridge.
  letI := H
  simpa [localizationAwayT] using
    ((MonoidalClosed.internalHomAdjunction₂.homEquiv :
      ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ X) ⟶ K) ≃
        (X ⟶ (ihom ((single₀).obj (ModuleCat.of A (Localization.Away f)))).obj K))).symm

/-- Helper for Lemma 15.92.1: after restricting scalars back to `A`, derived localization is the
same as tensoring by the degree-zero localization object `A_f[0]`. -/
noncomputable def localizationAway_restrict_derivedTensorWithAlgebra_iso
    (f : A) (X : DMod) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      ((CategoryTheory.derivedTensorWithAlgebra (algebraMap A (Localization.Away f))).obj X)) ≅
      ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ X)) := by
  let σ := algebraMap A (Localization.Away f)
  let K := DerivedCategory.Q.objPreimage X
  let singleAway :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
      (ModuleCat.of (Localization.Away f) (Localization.Away f))
  let extK :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
    (((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj K)
  let res := (ModuleCat.restrictScalars σ).mapDerivedCategory
  let resC := ((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ))
  let ext :
      (ModuleCat.extendScalars σ).mapDerivedCategory.obj X ≅
        DerivedCategory.Q.obj extK :=
    ((ModuleCat.extendScalars σ).mapDerivedCategory).mapIso
        (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
      (ModuleCat.extendScalars σ).mapDerivedCategoryFactors.app K
  -- Route correction: normalize the restricted derived tensor object through the explicit
  -- exact scalar-extension model, then use the underived tensor/base-change comparison on the
  -- chosen preimage before returning to `D(A)`.
  calc
    res.obj ((CategoryTheory.derivedTensorWithAlgebra σ).obj X) ≅
        res.obj ((ModuleCat.extendScalars σ).mapDerivedCategory.obj X) :=
      res.mapIso
        ((CategoryTheory.extendScalars_mapDerivedCategory_iso
          (R := A) (R' := Localization.Away f)).symm.app X)
    _ ≅ res.obj (DerivedCategory.Q.obj extK) :=
      res.mapIso ext
    _ ≅ DerivedCategory.Q.obj (resC.obj extK) :=
      (ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app extK
    _ ≅ DerivedCategory.Q.obj
        (resC.obj (HomologicalComplex.tensorObj singleAway extK)) :=
      DerivedCategory.Q.mapIso (resC.mapIso ((λ_ extK).symm))
    _ ≅ DerivedCategory.Q.obj
        (HomologicalComplex.tensorObj (resC.obj singleAway) K) :=
      DerivedCategory.Q.mapIso
        (restrictScalars_tensorObj_extendScalars_iso σ singleAway K)
    _ ≅ (DerivedCategory.Q.obj (resC.obj singleAway) ⊗ DerivedCategory.Q.obj K) :=
      (Functor.Monoidal.μIso
        (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)
        (resC.obj singleAway)
        K).symm
    _ ≅ (((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ X) :=
      ((((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app singleAway).symm ≪≫
          ((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ
              (ModuleCat (Localization.Away f)) (0 : ℤ)).app
              (ModuleCat.of (Localization.Away f) (Localization.Away f))).symm ≪≫
          localizationAway_restrict_single_iso (A := A) f) ⊗ᵢ
        DerivedCategory.Q.objObjPreimageIso X)

/-- Helper for Lemma 15.92.1: the pointwise localization/tensor comparison above is natural in
the source object, so it upgrades to a functor isomorphism of left adjoints. -/
private theorem localizationAway_restrict_derivedTensorWithAlgebra_iso_naturality
    (f : A) {X Y : DMod} (g : X ⟶ Y) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.map
        ((CategoryTheory.derivedTensorWithAlgebra
          (algebraMap A (Localization.Away f))).map g)) ≫
      (localizationAway_restrict_derivedTensorWithAlgebra_iso (A := A) f Y).hom =
        (localizationAway_restrict_derivedTensorWithAlgebra_iso (A := A) f X).hom ≫
          (CategoryTheory.derivedTensorProduct
            ((single₀).obj (ModuleCat.of A (Localization.Away f)))).map g := by
  -- Proof comment: every factor in the pointwise comparison is functorial in `X`, so the
  -- naturality square is the composite of the owner naturality squares already used to build it.
  simp [localizationAway_restrict_derivedTensorWithAlgebra_iso, Category.assoc]

/-- Helper for Lemma 15.92.1: after restricting scalars back to `A`, derived localization is
functorially the same as tensoring by the degree-zero localization object `A_f[0]`. -/
private noncomputable def localizationAway_restrict_derivedTensorWithAlgebra_natIso
    (f : A) :
    ((CategoryTheory.derivedTensorWithAlgebra (algebraMap A (Localization.Away f))) ⋙
      (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory) ≅
      CategoryTheory.derivedTensorProduct
        ((single₀).obj (ModuleCat.of A (Localization.Away f))) := by
  -- Proof comment: package the source-faithful pointwise tensor/base-change comparison as a
  -- natural isomorphism so `Adjunction.rightAdjointUniq` can consume it later.
  refine NatIso.ofComponents
    (fun X ↦ localizationAway_restrict_derivedTensorWithAlgebra_iso (A := A) f X) ?_
  intro X Y g
  exact localizationAway_restrict_derivedTensorWithAlgebra_iso_naturality (A := A) f g

/-- Helper for Lemma 15.92.1: the tensor-adjunction description of maps into `T(K,f)` specializes
directly to restricted sources from `D(A_f)`. -/
noncomputable def localized_source_hom_equiv_to_localizationAwayT_tensor
    (f : A) (K : DMod) (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
      localizationAwayT H f K) ≃
      ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗
        ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)) ⟶ K) :=
  -- This is just the previous currying equivalence evaluated at the restricted localized source.
  localizationAwayT_hom_equiv_tensor (A := A) H f
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) K

/-- Helper for Lemma 15.92.1: package the restriction of a chosen localized complex preimage as
an explicit `Q.obj` in `D(A)`. -/
noncomputable def restrict_localization_preimage_iso
    (f : A) (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    DerivedCategory.Q.obj
        ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj (DerivedCategory.Q.objPreimage E))) ≅
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        E) := by
  let σ := algebraMap A (Localization.Away f)
  -- Package the standard restriction comparison for the chosen complex representative of `E`.
  exact
    ((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage E)).symm ≪≫
      ((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso
        (DerivedCategory.Q.objObjPreimageIso E)

/-- Helper for Lemma 15.92.1: package the localized degree-zero object as an explicit `Q.obj`
after restricting scalars to `A`. -/
noncomputable def restrict_localization_single_preimage_iso
    (f : A) :
    DerivedCategory.Q.obj
        ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj
          ((CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
            (ModuleCat.of (Localization.Away f) (Localization.Away f))))) ≅
      ((single₀).obj (ModuleCat.of A (Localization.Away f))) := by
  let σ := algebraMap A (Localization.Away f)
  let M : ModuleCat (Localization.Away f) := ModuleCat.of (Localization.Away f) (Localization.Away f)
  -- Normalize the restricted degree-zero localization object to the owner used in `D(A)`.
  exact
    ((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj M)).symm ≪≫
      ((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ
          (ModuleCat (Localization.Away f)) (0 : ℤ)).app M).symm ≪≫
      localizationAway_restrict_single_iso (A := A) f

/-- Helper for Lemma 15.92.1: package the localized tensor preimage as the actual tensor object in
`D(A_f)`. -/
noncomputable def localization_single_tensor_preimage_iso
    (f : A) (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    DerivedCategory.Q.obj
        (HomologicalComplex.tensorObj
          ((CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
            (ModuleCat.of (Localization.Away f) (Localization.Away f)))
          (DerivedCategory.Q.objPreimage E)) ≅
      (((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f))) ⊗ E) := by
  let M : ModuleCat (Localization.Away f) := ModuleCat.of (Localization.Away f) (Localization.Away f)
  let L := DerivedCategory.Q.objPreimage E
  letI :
      (DerivedCategory.Q :
        CochainComplex (ModuleCat (Localization.Away f)) ℤ ⥤
          DerivedCategory (ModuleCat (Localization.Away f))).Monoidal :=
    derivedCategory_q_monoidal (R := Localization.Away f)
  -- Move from the chosen complex preimage of the tensor to the actual tensor object in `D(A_f)`.
  exact
    (Functor.Monoidal.μIso
      (DerivedCategory.Q :
        CochainComplex (ModuleCat (Localization.Away f)) ℤ ⥤
          DerivedCategory (ModuleCat (Localization.Away f)))
      ((CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj M)
      L).symm ≪≫
      (((DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat (Localization.Away f)) (0 : ℤ)).app M) ⊗ᵢ
          DerivedCategory.Q.objObjPreimageIso E)

/-- Helper for Lemma 15.92.1: tensoring a restricted localized source by the restricted degree-zero
localization object identifies with restricting the localized tensor object. -/
noncomputable def restrict_localization_single_tensor_iso
    (f : A) (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        E))) ≅
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) ⊗ E)) := by
  let σ := algebraMap A (Localization.Away f)
  let L := DerivedCategory.Q.objPreimage E
  let singleAway :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (0 : ℤ)).obj
      (ModuleCat.of (Localization.Away f) (Localization.Away f))
  -- Move both tensor factors to explicit `Q.obj` forms, transport the cochain tensor comparison,
  -- and then return to the restricted tensor object in `D(A)`.
  exact
    ((restrict_localization_single_preimage_iso (A := A) f).symm ⊗ᵢ
      (restrict_localization_preimage_iso (A := A) f E).symm) ≪≫
      (Functor.Monoidal.μIso
        (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)
        ((((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)).obj singleAway))
        ((((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)).obj L))) ≪≫
      DerivedCategory.Q.mapIso
        ((restrict_localization_single_tensor_complex_iso (A := A) f L).symm) ≪≫
      ((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app
        (HomologicalComplex.tensorObj singleAway L)).symm ≪≫
      ((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso
        (localization_single_tensor_preimage_iso (A := A) f E)

/-- Helper for Lemma 15.92.1: tensoring a restricted object from `D(A_f)` by the degree-zero
localization object `A_f[0]` does not change it. -/
noncomputable def localizationAway_left_tensor_restricted_iso
    (f : A) (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        E))) ≅
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        E) := by
  -- Route correction: isolate the source-faithful localization-idempotence bridge before the
  -- witness construction, instead of continuing the earlier functor-level coextension route.
  let σ := algebraMap A (Localization.Away f)
  -- First identify the restricted tensor with the restriction of the localized tensor object,
  -- then collapse the localized tensor by the left unitor in `D(A_f)`.
  exact
    restrict_localization_single_tensor_iso (A := A) f E ≪≫
      ((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso (λ_ E)

/-- Helper for Lemma 15.92.1: morphisms from a restricted localized object into `K` identify with
morphisms into the underlying `A`-object `T(K,f)`. -/
noncomputable def localized_source_hom_equiv_to_localizationAwayT
    (f : A) (K : DMod) (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
      K) ≃
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
        localizationAwayT H f K) := by
  -- Route correction: the first verified step is the tensor/internal-Hom adjunction above; the
  -- remaining source-faithful blocker is to identify tensoring a restricted localized source by
  -- `A_f[0]` with the source itself.
  let resE :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  let eTensor :
      (resE ⟶ localizationAwayT H f K) ≃
        ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ resE) ⟶ K) :=
    localized_source_hom_equiv_to_localizationAwayT_tensor (A := A) H f K E
  let eTransport :
      (resE ⟶ K) ≃
        ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ resE) ⟶ K) :=
    (localizationAway_left_tensor_restricted_iso (A := A) f E).symm.homCongr (Iso.refl K)
  -- Once tensoring by `A_f[0]` is identified with the identity on restricted sources, the desired
  -- equivalence is just transport across that iso followed by the tensor/internal-Hom adjunction.
  exact eTransport.trans eTensor.symm

/-- Helper for Lemma 15.92.1: choose a K-injective cochain-complex representative of the derived
object `K`. -/
private noncomputable abbrev localizationAway_k_injective_resolution :
    CochainComplex.FunctorialComplexApproximation (ModuleCat A) :=
  Classical.choose (CochainComplex.exists_functorial_kInjective_resolution (ModuleCat A))

/-- Helper for Lemma 15.92.1: choose a K-injective cochain-complex representative of the derived
object `K`. -/
private noncomputable abbrev localizationAway_k_injective_preimage
    (K : DMod) : CochainComplex (ModuleCat A) ℤ :=
  localizationAway_k_injective_resolution (A := A).toFunctor.obj (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.92.1: the chosen cochain representative above is K-injective. -/
private theorem localizationAway_k_injective_preimage_isKInjective
    (K : DMod) :
    (localizationAway_k_injective_preimage (A := A) K).IsKInjective := by
  -- The chosen functorial replacement lands in K-injective complexes on every input.
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution (ModuleCat A))).2
        (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.92.1: the canonical map from the chosen `Q.objPreimage` model of `K`
to its chosen K-injective replacement. -/
private noncomputable abbrev localizationAway_k_injective_preimage_map
    (K : DMod) :
    DerivedCategory.Q.objPreimage K ⟶ localizationAway_k_injective_preimage (A := A) K :=
  localizationAway_k_injective_resolution (A := A).ι.app (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.92.1: the canonical comparison from the chosen `Q.objPreimage` model of
`K` to its K-injective replacement is a quasi-isomorphism. -/
private theorem localizationAway_k_injective_preimage_map_quasiIso
    (K : DMod) :
    QuasiIso (localizationAway_k_injective_preimage_map (A := A) K) := by
  -- The fixed functorial approximation comes equipped with a quasi-isomorphism from each input
  -- complex to its K-injective replacement.
  exact
    localizationAway_k_injective_resolution (A := A).quasiIso_app
      (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.92.1: the chosen K-injective replacement still computes the original
derived object `K`. -/
private theorem localizationAway_k_injective_preimage_q_map_isIso
    (K : DMod) :
    IsIso (DerivedCategory.Q.map (localizationAway_k_injective_preimage_map (A := A) K)) := by
  -- The localization functor inverts every quasi-isomorphism, in particular the chosen
  -- comparison into the K-injective replacement.
  exact
    DerivedCategory.Q_isInverted _
      (localizationAway_k_injective_preimage_map (A := A) K)

/-- Helper for Lemma 15.92.1: the chosen K-injective replacement represents the same derived
object as the original `Q.objPreimage` model of `K`. -/
private noncomputable abbrev localizationAway_k_injective_preimage_iso
    (K : DMod) :
    DerivedCategory.Q.obj (localizationAway_k_injective_preimage (A := A) K) ≅ K :=
  letI :
      IsIso (DerivedCategory.Q.map (localizationAway_k_injective_preimage_map (A := A) K)) :=
    localizationAway_k_injective_preimage_q_map_isIso (A := A) K
  (asIso (DerivedCategory.Q.map (localizationAway_k_injective_preimage_map (A := A) K))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K

/-- Helper for Lemma 15.92.1: the chosen K-injective representative of `K` can be coextended
termwise to a concrete object of `D(A_f)`. -/
noncomputable def localizationAwayT_coextend_preimage
    (f : A) (K : DMod) :
    DerivedCategory (ModuleCat (Localization.Away f)) :=
  let σ := algebraMap A (Localization.Away f)
  -- Route correction: the source proof computes the right adjoint on a K-injective model of `K`,
  -- so the coextended representative must use the chosen K-injective replacement rather than an
  -- arbitrary `Q.objPreimage`.
  DerivedCategory.Q.obj
    (((ModuleCat.coextendScalars σ).mapHomologicalComplex (up ℤ)).obj
      (localizationAway_k_injective_preimage (A := A) K))

/-- Helper for Lemma 15.92.1: exact restriction of scalars on cochain complexes computes its own
pointwise left derived functor at every localized complex. -/
private theorem restrictScalars_computesLeftDerivedAt
    (f : A) (L : CochainComplex (ModuleCat (Localization.Away f)) ℤ) :
    let F :
        CochainComplex (ModuleCat (Localization.Away f)) ℤ ⥤ DMod :=
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
        (up ℤ)) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod))
    F.ComputesLeftDerivedAt
      (HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ))
      L := by
  let σ := algebraMap A (Localization.Away f)
  let F₀ : ModuleCat (Localization.Away f) ⥤ ModuleCat A := ModuleCat.restrictScalars σ
  let F :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ ⥤ DMod :=
    (F₀.mapHomologicalComplex (up ℤ)) ⋙
      (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)
  let Qis :
      MorphismProperty (CochainComplex (ModuleCat (Localization.Away f)) ℤ) :=
    HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ)
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactors.hom
        Qis := by
    -- Exact restriction already inverts quasi-isomorphisms, so its derived-category lift is its
    -- own left derived functor.
    simpa [F₀, Qis] using
      (Functor.isLeftDerivedFunctor_of_inverts
        Qis
        F₀.mapDerivedCategory
        F₀.mapDerivedCategoryFactors)
  letI : F.HasLeftDerivedFunctor Qis :=
    Functor.HasLeftDerivedFunctor.mk'
      F₀.mapDerivedCategory
      F₀.mapDerivedCategoryFactors.hom
  have hComparison :
      IsIso (F₀.mapDerivedCategoryFactors.hom.app L) := by
    let hInverts : Qis.IsInvertedBy F := by
      intro X Y g hg
      change IsIso
        (DerivedCategory.Q.map (((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)).map g))
      exact DerivedCategory.Q_isInverted _ (((ModuleCat.restrictScalars σ).mapHomologicalComplex
        (up ℤ)).map g)
    have :
        IsIso F₀.mapDerivedCategoryFactors.hom := by
      exact
        Functor.isIso_of_isLeftDerivedFunctor_of_inverts
          F₀.mapDerivedCategory
          F₀.mapDerivedCategoryFactors.hom
          hInverts
    infer_instance
  -- The exact-functor comparison already is the total-left-derived counit component at `L`.
  simpa [F, F₀, Qis] using hComparison

/-- Helper for Lemma 15.92.1: a K-injective complex computes the pointwise right derived value of
coextension along `A → A_f`. -/
noncomputable def coextend_k_injective_rightDerived_iso
    (f : A) (I : CochainComplex (ModuleCat A) ℤ) [I.IsKInjective] :
    let F :
        HomotopyCategory (ModuleCat A) (up ℤ) ⥤
          DerivedCategory (ModuleCat (Localization.Away f)) :=
      (((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomotopyCategory
        (up ℤ)) ⋙
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat (Localization.Away f)) (up ℤ) ⥤
            DerivedCategory (ModuleCat (Localization.Away f))))
    let _ :
        F.ComputesRightDerivedAt
          (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
          ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I) :=
      kInjective_computesRightDerivedFunctorAt F I
    DerivedCategory.Q.obj
        (((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj I) ≅
      rightDerivedValue
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
        F
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I) := by
  let F :
      HomotopyCategory (ModuleCat A) (up ℤ) ⥤
        DerivedCategory (ModuleCat (Localization.Away f)) :=
    (((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomotopyCategory
      (up ℤ)) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat (Localization.Away f)) (up ℤ) ⥤
          DerivedCategory (ModuleCat (Localization.Away f))))
  letI :
      F.ComputesRightDerivedAt
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I) :=
    kInjective_computesRightDerivedFunctorAt F I
  let hId :
      HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
        (𝟙 ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I)) :=
    MorphismProperty.id_mem _ _
  -- The identity denominator on a K-injective model gives the canonical pointwise right-derived
  -- comparison isomorphism.
  simpa [F] using
    (asIso
      (rightDerivedValueLeg
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
        F
        (𝟙 ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I))
        hId))

/-- Helper for Lemma 15.92.1: reorient the K-injective right-derived comparison so it can be
used directly as the target-side transport in the Chapter 13 Hom equivalence. -/
noncomputable def coextend_k_injective_rightDerived_value_iso
    (f : A) (I : CochainComplex (ModuleCat A) ℤ) [I.IsKInjective] :
    let F :
        HomotopyCategory (ModuleCat A) (up ℤ) ⥤
          DerivedCategory (ModuleCat (Localization.Away f)) :=
      (((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomotopyCategory
        (up ℤ)) ⋙
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat (Localization.Away f)) (up ℤ) ⥤
            DerivedCategory (ModuleCat (Localization.Away f))))
    let _ :
        F.ComputesRightDerivedAt
          (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
          ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I) :=
      kInjective_computesRightDerivedFunctorAt F I
    rightDerivedValue
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
        F
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj I) := by
  -- This is just the previously constructed pointwise right-derived computation, read in the
  -- direction needed for later Hom-set transports.
  exact (coextend_k_injective_rightDerived_iso (A := A) f I).symm

/-- Helper for Lemma 15.92.1: exact restriction already computes its own pointwise left-derived
value on every localized cochain complex. -/
noncomputable def restrictScalars_leftDerived_value_iso
    (f : A) (L : CochainComplex (ModuleCat (Localization.Away f)) ℤ) :
    let F :
        CochainComplex (ModuleCat (Localization.Away f)) ℤ ⥤ DMod :=
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
        (up ℤ)) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod))
    let _ :
        F.ComputesLeftDerivedAt
          (HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ))
          L :=
      restrictScalars_computesLeftDerivedAt (A := A) f L
    leftDerivedValue
        (HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ))
        F
        L ≅
      DerivedCategory.Q.obj
        ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj L)) := by
  let σ := algebraMap A (Localization.Away f)
  let F :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ ⥤ DMod :=
    (((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)) ⋙
      (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod))
  have hCompute :
      F.ComputesLeftDerivedAt
        (HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ))
        L := by
    simpa [F, σ] using restrictScalars_computesLeftDerivedAt (A := A) f L
  letI :
      F.ComputesLeftDerivedAt
        (HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ))
        L :=
    hCompute
  -- Since restriction is exact, the identity-denominator projection already computes the
  -- left-derived value and lands in the concrete restricted complex.
  let hProjectionIso :
      IsIso
        (leftDerivedValueProjection
          (HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ))
          F
          (𝟙 L)
          (MorphismProperty.id_mem _ _)) := by
    infer_instance
  exact
    @asIso _ _ _ _
      (leftDerivedValueProjection
        (HomologicalComplex.quasiIso (ModuleCat (Localization.Away f)) (up ℤ))
        F
        (𝟙 L)
        (MorphismProperty.id_mem _ _))
      hProjectionIso

/-- Helper for Lemma 15.92.1: restricting the coextended chosen preimage is just the derived
image of the restricted coextended complex. -/
noncomputable def localizationAwayT_coextend_preimage_restrict_iso
    (f : A) (K : DMod) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      (localizationAwayT_coextend_preimage (A := A) f K)) ≅
      DerivedCategory.Q.obj
        ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
          (up ℤ)).obj
          (((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomologicalComplex
            (up ℤ)).obj
            (localizationAway_k_injective_preimage (A := A) K)))) := by
  let σ := algebraMap A (Localization.Away f)
  let C :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
    (((ModuleCat.coextendScalars σ).mapHomologicalComplex (up ℤ)).obj
      (localizationAway_k_injective_preimage (A := A) K))
  -- Normalize the restriction of the derived object back to the `Q`-image of the restricted
  -- cochain complex using the standard exact-functor comparison.
  simpa [localizationAwayT_coextend_preimage, C] using
    ((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app C)

/-- Helper for Lemma 15.92.1: an isomorphism of sequential inverse systems induces an isomorphism
of any chosen product objects for their stage families. -/
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

/-- Helper for Lemma 15.92.1: the product isomorphism attached to a tower isomorphism preserves
each stage projection. -/
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

/-- Helper for Lemma 15.92.1: the product isomorphism attached to a tower isomorphism intertwines
the Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  apply Pi.hom_ext
  intro n
  -- Compare the two Milnor endomorphisms after the `n`th projection and reduce to the naturality
  -- square of the tower isomorphism.
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
          rw [Preadditive.comp_sub, tower_product_iso_hom_comp_π, tower_product_iso_hom_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (Opposite.op n)).hom) := by
          congr 1
          rw [Category.assoc]
          exact congrArg
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

/-- Helper for Lemma 15.92.1: a derived-limit witness transports across an isomorphism of towers
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
  let p : (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys :=
    tower_product_iso e
  let T : Triangle DMod :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DMod :=
    Triangle.mk (ι ≫ p.hom) (derivedLimitDifferenceMap Lsys) (p.inv ≫ δ)
  have hIso : T ≅ T' := by
    -- Repackage the original Milnor triangle through the product comparison isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T']
    · simpa [T, T'] using (tower_product_iso_hom_comm_difference e).symm
    · simp [T, T']
  have hT' : T' ∈ distTriang DMod := by
    -- Distinguished triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ⟨ι ≫ p.hom, p.inv ≫ δ, hT'⟩⟩

/-- Helper for Lemma 15.92.1: once a Milnor triangle is known for a fixed tower, the limiting
object can be replaced by any isomorphic object. -/
private theorem isDerivedLimit_of_object_iso
    {Ksys : SequentialInverseSystem DMod} {K L : DMod}
    (e : K ≅ L)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Ksys L := by
  rcases hK with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let T : Triangle DMod :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DMod :=
    Triangle.mk (e.inv ≫ ι) (derivedLimitDifferenceMap Ksys)
      (δ ≫ (shiftFunctor DMod (1 : ℤ)).map e.hom)
  have hIso : T ≅ T' := by
    -- Only the first vertex changes, so the comparison triangle is induced by the chosen
    -- isomorphism of limiting objects.
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [T, T']
    · simp [T, T']
    · simp [T, T']
  have hT' : T' ∈ distTriang DMod := by
    -- Distinguished triangles are stable under isomorphism, so the transported Milnor triangle
    -- is still distinguished.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hP, ⟨e.inv ≫ ι, δ ≫ (shiftFunctor DMod (1 : ℤ)).map e.hom, hT'⟩⟩

/-- Helper for Lemma 15.92.1: a source-natural family of Hom-set equivalences into two objects
determines an isomorphism between those objects. -/
private noncomputable def iso_of_source_nat_hom_equiv
    {S T : DMod}
    (e : ∀ X : DMod, (X ⟶ S) ≃ (X ⟶ T))
    (hNat :
      ∀ {X Y : DMod} (a : X ⟶ Y) (g : Y ⟶ S),
        e X (a ≫ g) = a ≫ e Y g) :
    S ≅ T := by
  -- The forward map is the image of the identity under the representing Hom-equivalence.
  refine
    { hom := e S (𝟙 S)
      inv := (e T).symm (𝟙 T)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- Proof comment: compare both sides after applying the source Hom-equivalence at `S`.
    apply (e S).injective
    calc
      e S (e S (𝟙 S) ≫ (e T).symm (𝟙 T))
          = e S (𝟙 S) ≫ e T ((e T).symm (𝟙 T)) := by
              simpa using hNat (a := e S (𝟙 S)) (g := (e T).symm (𝟙 T))
      _ = e S (𝟙 S) := by simp
  · -- Proof comment: the same source-naturality argument with the inverse morphism proves the
    -- second triangle identity.
    apply (e T).injective
    calc
      e T ((e T).symm (𝟙 T) ≫ e S (𝟙 S))
          = (e T).symm (𝟙 T) ≫ e S (𝟙 S) := by
              simpa using hNat (a := (e T).symm (𝟙 T)) (g := 𝟙 S)
      _ = 𝟙 T := by simp

/-- Helper for Lemma 15.92.1: morphisms into the coextended K-injective model are computed by
ordinary adjunction against restriction of scalars, because the coextended target is itself
K-injective. -/
private noncomputable def localizationAway_coextend_model_hom_equiv
    (f : A) (K : DMod) (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    (E ⟶ localizationAwayT_coextend_preimage (A := A) f K) ≃
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        E) ⟶ K) := by
  let σ := algebraMap A (Localization.Away f)
  let I := localizationAway_k_injective_preimage (A := A) K
  let J :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
    (((ModuleCat.coextendScalars σ).mapHomologicalComplex (up ℤ)).obj I)
  let LE :
      CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
    DerivedCategory.Q.objPreimage E
  let KQAf := HomotopyCategory.quotient (ModuleCat (Localization.Away f)) (up ℤ)
  let KQA := HomotopyCategory.quotient (ModuleCat A) (up ℤ)
  let resC :=
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ))
  let resD :=
    (ModuleCat.restrictScalars σ).mapDerivedCategory
  letI : I.IsKInjective := localizationAway_k_injective_preimage_isKInjective (A := A) K
  letI : J.IsKInjective := coextendScalars_isKInjective σ I
  let sourceIso :
      DerivedCategory.Qh.obj (KQAf.obj LE) ≅ E :=
    (DerivedCategory.quotientCompQhIso (ModuleCat (Localization.Away f))).app LE ≪≫
      DerivedCategory.Q.objObjPreimageIso E
  let targetIso :
      DerivedCategory.Qh.obj (KQAf.obj J) ≅
        localizationAwayT_coextend_preimage (A := A) f K := by
    -- Proof comment: the repaired coextend model is literally the `Q`-image of the coextended
    -- K-injective complex `J`.
    simpa [localizationAwayT_coextend_preimage, I, J] using
      (DerivedCategory.quotientCompQhIso (ModuleCat (Localization.Away f))).app J
  let eLeft :
      (KQAf.obj LE ⟶ KQAf.obj J) ≃
        (E ⟶ localizationAwayT_coextend_preimage (A := A) f K) :=
    (Equiv.ofBijective
        DerivedCategory.Qh.map
        (IsKInjective.Qh_map_bijective (KQAf.obj LE) J)).trans
      (Iso.homCongr sourceIso targetIso)
  let sourceIsoRight :
      DerivedCategory.Qh.obj (KQA.obj (resC.obj LE)) ≅
        resD.obj E :=
    (DerivedCategory.quotientCompQhIso (ModuleCat A)).app (resC.obj LE) ≪≫
      (((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app LE).symm) ≪≫
      resD.mapIso (DerivedCategory.Q.objObjPreimageIso E)
  let targetIsoRight :
      DerivedCategory.Qh.obj (KQA.obj I) ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat A)).app I ≪≫
      localizationAway_k_injective_preimage_iso (A := A) K
  let eRight :
      (KQA.obj (resC.obj LE) ⟶ KQA.obj I) ≃
        (resD.obj E ⟶ K) :=
    (Equiv.ofBijective
        DerivedCategory.Qh.map
        (IsKInjective.Qh_map_bijective (KQA.obj (resC.obj LE)) I)).trans
      (Iso.homCongr sourceIsoRight targetIsoRight)
  let eAdj :
      (KQAf.obj LE ⟶ KQAf.obj J) ≃
        (KQA.obj (resC.obj LE) ⟶ KQA.obj I) := by
    -- Proof comment: after passing to homotopy categories, the ordinary
    -- restriction/coextension adjunction gives the desired Hom-set identification.
    simpa [I, J, LE, resC] using
      (((ModuleCat.restrictCoextendScalarsAdj σ).mapHomotopyCategory (up ℤ)).homEquiv
        (KQAf.obj LE)
        (KQA.obj I))
  exact eLeft.symm.trans (eAdj.trans eRight)

/-- Helper for Lemma 15.92.1: after applying the derived tensor/restriction adjunction, the
coextended K-injective model and `T(K,f)` define the same Hom-functor on source objects. -/
private noncomputable def localizationAway_coextend_model_target_hom_equiv
    (f : A) (K X : DMod) :
    (X ⟶
        ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          (localizationAwayT_coextend_preimage (A := A) f K))) ≃
      (X ⟶ localizationAwayT H f K) := by
  let σ := algebraMap A (Localization.Away f)
  let E := (CategoryTheory.derivedTensorWithAlgebra σ).obj X
  let eAdj :
      (X ⟶
          ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj
            (localizationAwayT_coextend_preimage (A := A) f K))) ≃
        (E ⟶ localizationAwayT_coextend_preimage (A := A) f K) :=
    (derivedTensorWithAlgebraAdjunction (R := A) (A := Localization.Away f)).homEquiv X
      (localizationAwayT_coextend_preimage (A := A) f K)
  let eModel :
      (E ⟶ localizationAwayT_coextend_preimage (A := A) f K) ≃
        (((ModuleCat.restrictScalars σ).mapDerivedCategory.obj E) ⟶ K) :=
    localizationAway_coextend_model_hom_equiv (A := A) f K E
  let eRestrict :
      (((ModuleCat.restrictScalars σ).mapDerivedCategory.obj E) ⟶ K) ≃
        ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ X) ⟶ K) :=
    (localizationAway_restrict_derivedTensorWithAlgebra_iso (A := A) f X).homCongr (Iso.refl K)
  let eTensor :
      ((((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗ X) ⟶ K) ≃
        (X ⟶ localizationAwayT H f K) :=
    (localizationAwayT_hom_equiv_tensor (A := A) H f X K).symm
  -- Proof comment: follow the source proof literally: tensor-left adjunction, then the
  -- coextend-model comparison, then the explicit identification of restricted derived tensor with
  -- tensoring by `A_f[0]`, and finally the internal-Hom adjunction for `T(K,f)`.
  exact eAdj.trans (eModel.trans (eRestrict.trans eTensor))

/-- Helper for Lemma 15.92.1: coextension on homotopy categories provides the canonical source
functor whose total right derived functor computes `RHom_A(A_f, -)`. -/
private abbrev localizationAway_coextend_homotopy_to_derived
    (f : A) :
    HomotopyCategory (ModuleCat A) (up ℤ) ⥤
      DerivedCategory (ModuleCat (Localization.Away f)) :=
  (((ModuleCat.coextendScalars (algebraMap A (Localization.Away f))).mapHomotopyCategory
    (up ℤ)) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat (Localization.Away f)) (up ℤ) ⥤
        DerivedCategory (ModuleCat (Localization.Away f)))

/-- Helper for Lemma 15.92.1: K-injective resolutions globalize the coextension computation to a
canonical total right derived functor. -/
private instance localizationAway_coextend_hasRightDerivedFunctor
    (f : A) :
    (localizationAway_coextend_homotopy_to_derived (A := A) f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)) := by
  refine hasRightDerivedFunctor_of_kInjective_resolutions
    (F := localizationAway_coextend_homotopy_to_derived (A := A) f) ?_
  intro K
  let R := localizationAway_k_injective_resolution (A := A)
  refine ⟨R.toFunctor.obj K, ?_, R.ι.app K, R.quasiIso_app K⟩
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution (ModuleCat A))).2 K

/-- Helper for Lemma 15.92.1: the canonical total right derived coextension functor on `D(A)`. -/
private noncomputable abbrev localizationAway_coextend_totalRightDerived
    (f : A) :
    DMod ⥤ DerivedCategory (ModuleCat (Localization.Away f)) :=
  Functor.totalRightDerived
    (localizationAway_coextend_homotopy_to_derived (A := A) f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod)
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))

/-- Helper for Lemma 15.92.1: evaluating the canonical total right derived coextension functor at
`Qh.obj I` recovers the pointwise right-derived value computed from the same homotopy object. -/
private noncomputable def localizationAway_coextend_totalRightDerived_value_iso
    (f : A) (I : CochainComplex (ModuleCat A) ℤ) :
    (localizationAway_coextend_totalRightDerived (A := A) f).obj
        ((DerivedCategory.Qh :
          HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod).obj
          ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I)) ≅
      rightDerivedValue
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
        (localizationAway_coextend_homotopy_to_derived (A := A) f)
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I) := by
  -- The total right derived functor is defined by the pointwise right-derived colimit, so
  -- evaluating it at `Qh.obj I` returns that same colimit object.
  simpa [Functor.totalRightDerived, localizationAway_coextend_totalRightDerived,
    localizationAway_coextend_homotopy_to_derived] using
    ((DerivedCategory.Qh :
        HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod).leftKanExtensionObjIsoColimit
      (localizationAway_coextend_homotopy_to_derived (A := A) f)
      ((DerivedCategory.Qh :
        HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod).obj
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj I)))

/-- Helper for Lemma 15.92.1: the chosen coextended K-injective model agrees pointwise with the
value of the canonical total right derived coextension functor, after restricting scalars back to
`A`. -/
private noncomputable def localizationAway_concrete_coextend_model_iso
    (f : A) (K : DMod) :
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      (localizationAwayT_coextend_preimage (A := A) f K)) ≅
      (((localizationAway_coextend_totalRightDerived (A := A) f) ⋙
        (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).obj
        K) := by
  let σ := algebraMap A (Localization.Away f)
  let I := localizationAway_k_injective_preimage (A := A) K
  let KQ := HomotopyCategory.quotient (ModuleCat A) (up ℤ)
  let QhA : HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod := DerivedCategory.Qh
  let eK : QhA.obj (KQ.obj I) ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat A)).app I ≪≫
      localizationAway_k_injective_preimage_iso (A := A) K
  have eRF :
      localizationAwayT_coextend_preimage (A := A) f K ≅
        (localizationAway_coextend_totalRightDerived (A := A) f).obj K := by
    calc
      localizationAwayT_coextend_preimage (A := A) f K ≅
          rightDerivedValue
            (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
            (localizationAway_coextend_homotopy_to_derived (A := A) f)
            (KQ.obj I) := by
        -- The chosen K-injective replacement computes the right-derived value of coextension.
        simpa [localizationAwayT_coextend_preimage, I,
          localizationAway_coextend_homotopy_to_derived] using
          (coextend_k_injective_rightDerived_value_iso (A := A) f I).symm
      _ ≅
          (localizationAway_coextend_totalRightDerived (A := A) f).obj
            (QhA.obj (KQ.obj I)) := by
        -- Replace the pointwise right-derived value by the canonical total derived functor value.
        simpa [QhA] using
          (localizationAway_coextend_totalRightDerived_value_iso (A := A) f I).symm
      _ ≅
          (localizationAway_coextend_totalRightDerived (A := A) f).obj K :=
        (localizationAway_coextend_totalRightDerived (A := A) f).mapIso eK
  -- Restrict scalars only after identifying the concrete K-injective model with the canonical
  -- total right derived value.
  simpa [Functor.comp_obj] using
    ((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso eRF

/-- Helper for Lemma 15.92.1: the source-Hom equivalence comparing the restricted coextended model
with `T(K,f)` is natural in the source object. -/
private theorem localizationAway_coextend_model_target_hom_equiv_naturality
    (f : A) (K : DMod) {X Y : DMod} (a : X ⟶ Y)
    (g :
      Y ⟶
        ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          (localizationAwayT_coextend_preimage (A := A) f K))) :
    localizationAway_coextend_model_target_hom_equiv (A := A) H f K X (a ≫ g) =
      a ≫ localizationAway_coextend_model_target_hom_equiv (A := A) H f K Y g := by
  -- Proof comment: every factor in the defining chain of Hom-equivalences is source-natural, so
  -- the composite comparison preserves precomposition by `a`.
  simp [localizationAway_coextend_model_target_hom_equiv, Category.assoc]

/-- Helper for Lemma 15.92.1: once the all-source comparison is packaged, the restricted
coextended chosen K-injective model is canonically isomorphic to `T(K, f)`. -/
theorem coextend_k_injective_represents_localizationAwayT
    (f : A) (K : DMod) :
    IsIsomorphic
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        (localizationAwayT_coextend_preimage (A := A) f K))
      (localizationAwayT H f K) := by
  -- Route correction: the pointwise source-Hom comparison already has the exact Yoneda shape, so
  -- it suffices to certify source naturality and invoke `iso_of_source_nat_hom_equiv`.
  refine ⟨iso_of_source_nat_hom_equiv
    (S := ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      (localizationAwayT_coextend_preimage (A := A) f K)))
    (T := localizationAwayT H f K)
    (localizationAway_coextend_model_target_hom_equiv (A := A) H f K)
    (localizationAway_coextend_model_target_hom_equiv_naturality
      (A := A) H f K)⟩

/-- Helper for Lemma 15.92.1: the final derived-limit statement for `T(K,f)` reduces to the
source-faithful Milnor calculation on the explicit restricted coextension model. -/
private theorem localizationAwayT_isDerivedLimit_of_representation
    (f : A) (K : DMod)
    (hModel :
      IsDerivedLimit
        (localizationAwayTower f K)
        ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          (localizationAwayT_coextend_preimage (A := A) f K))) :
    IsDerivedLimit (localizationAwayTower f K) (localizationAwayT H f K) := by
  -- Once the explicit restricted coextension model is known to satisfy the Milnor triangle, the
  -- representation isomorphism transports that derived-limit witness to `T(K,f)`.
  classical
  rcases coextend_k_injective_represents_localizationAwayT (A := A) H f K with ⟨e⟩
  exact isDerivedLimit_of_object_iso e hModel

/-- Helper for Lemma 15.92.1: under the canonical comparison
`RHom_A(A[0], K) ≅ K`, precomposition by `f • 𝟙_{A[0]}` becomes the scalar endomorphism
`f • 𝟙_K`. -/
private theorem ringSingle_rhom_iso_conjugates_pre_mul_to_smul
    (f : A) (K : DMod) :
    ((MonoidalClosed.pre
        (f • 𝟙 ((single₀).obj (ModuleCat.of A A)))).app K) ≫
      (ringSingle_rhom_iso (A := A) (H := H) K).hom =
        (ringSingle_rhom_iso (A := A) (H := H) K).hom ≫
          (f • 𝟙 K) := by
  letI := H
  -- Route correction: the remaining blocker is the source-variable compatibility of the
  -- `RHom_A(A[0], K) ≅ K` identification, not the later Milnor transport.
  -- Proof comment: both endomorphisms of `RHom_A(A[0], K)` are the scalar endomorphism `f • 𝟙`,
  -- so the statement reduces to naturality of the comparison `RHom_A(A[0], -) ≅ 𝟭`.
  calc
    ((MonoidalClosed.pre
        (f • 𝟙 ((single₀).obj (ModuleCat.of A A)))).app K) ≫
        (ringSingle_rhom_iso (A := A) (H := H) K).hom =
      ((ihom ((single₀).obj (ModuleCat.of A A))).map (f • 𝟙 K)) ≫
        (ringSingle_rhom_iso (A := A) (H := H) K).hom := by
          simp [Functor.map_smul]
    _ =
      (ringSingle_rhom_iso (A := A) (H := H) K).hom ≫
        (f • 𝟙 K) := by
          simpa [ringSingle_rhom_iso] using
            (ringSingle_internalHom_natIso (A := A) (H := H)).hom.naturality (f • 𝟙 K)

/-- Helper for Lemma 15.92.1: the stagewise identifications
`RHom_A(A[0], K) ≅ K` are compatible with the successor maps of the source-faithful internal-Hom
tower and the constant `f`-tower. -/
private theorem localizationAway_ringSingle_internalHomTower_component_naturality
    (f : A) (K : DMod) (n : ℕ) :
    (localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K (n + 1)).hom ≫
      (localizationAwayTower f K).map (homOfLE (Nat.le_succ n)).op =
        (localizationAway_ringSingle_internalHomTower (A := A) H f K).map
            (homOfLE (Nat.le_succ n)).op ≫
          (localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K n).hom := by
  -- Proof comment: rewrite both successor maps to their explicit scalar/precomposition forms and
  -- then apply the source-variable conjugation lemma.
  calc
    (localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K (n + 1)).hom ≫
        (localizationAwayTower f K).map (homOfLE (Nat.le_succ n)).op =
      (localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K (n + 1)).hom ≫
        (f • 𝟙 K) := by
          rw [localizationAwayTower_map_succ]
    _ =
      ((MonoidalClosed.pre
          (f • 𝟙 ((single₀).obj (ModuleCat.of A A)))).app K) ≫
        (localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K n).hom := by
          simpa [localizationAway_ringSingle_internalHomTower_obj_iso, Category.assoc] using
            (ringSingle_rhom_iso_conjugates_pre_mul_to_smul (A := A) (H := H) f K).symm
    _ =
      (localizationAway_ringSingle_internalHomTower (A := A) H f K).map
          (homOfLE (Nat.le_succ n)).op ≫
        (localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K n).hom := by
          rw [localizationAway_ringSingle_internalHomTower_map_succ]

/-- Helper for Lemma 15.92.1: the source-faithful internal-Hom tower attached to
`A[0] --f--> A[0] --f--> ...` is canonically isomorphic to the constant `f`-tower on `K`. -/
private noncomputable def localizationAway_ringSingle_internalHomTower_iso_localizationAwayTower
    (f : A) (K : DMod) :
    localizationAway_ringSingle_internalHomTower (A := A) H f K ≅
      localizationAwayTower f K := by
  -- Proof comment: assemble the stagewise `RHom_A(A[0], K) ≅ K` comparisons into a tower
  -- isomorphism; successor-map compatibility is exactly the previous lemma.
  refine NatIso.ofComponents
    (fun n ↦ localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K (Opposite.unop n))
    ?_
  intro i j g
  simpa using
    (NatTrans.ofOpSequence
      (fun n ↦ (localizationAway_ringSingle_internalHomTower_obj_iso (A := A) H f K n).hom)
      (localizationAway_ringSingle_internalHomTower_component_naturality (A := A) H f K)).naturality g

/-- Helper for Lemma 15.92.1: the explicit homotopy-colimit presentation
`A[0] --f--> A[0] --f--> ... -> A_f[0]` yields the derived-limit witness for the associated
source-variable internal-Hom tower. -/
private theorem localizationAway_ringSingle_internalHomTower_isDerivedLimit
    (f : A) (K : DMod) :
    IsDerivedLimit
      (localizationAway_ringSingle_internalHomTower (A := A) H f K)
      (localizationAwayT H f K) := by
  -- Route correction: the remaining source-faithful blocker is the homotopy-colimit
  -- identification of the explicit `A[0] --f--> A[0] --f--> ...` sequence with `A_f[0]`.
  --
  -- TODO: build the termwise colimit complex of the degree-zero sequence
  -- `A --f--> A --f--> ...`, identify its `Q`-image with the restricted localization object
  -- `A_f[0]`, invoke the Chapter 13 homotopy-colimit theorem for that sequence, and then apply
  -- the Chapter 15 `derivedInternalHom_isDerivedLimit_of_homotopyColimit` package.
  sorry

/-- Helper for Lemma 15.92.1: the source-faithful proof route reduces the final statement to the
specialized hocolim/Milnor calculation for the explicit `A[0] --f--> A[0] --f--> ...` system. -/
private theorem localizationAwayT_isDerivedLimit_via_ringSingle_hocolim
    (f : A) (K : DMod) :
    IsDerivedLimit (localizationAwayTower f K) (localizationAwayT H f K) := by
  -- Route correction: the main theorem now factors into the source-faithful hocolim/Milnor
  -- calculation plus one clean transport across the explicit tower isomorphism.
  exact
    isDerivedLimit_of_tower_iso
      (localizationAway_ringSingle_internalHomTower_iso_localizationAwayTower
        (A := A) H f K)
      (localizationAway_ringSingle_internalHomTower_isDerivedLimit (A := A) H f K)

/-- Helper for Lemma 15.92.1: the underlying `A`-object `T(K,f)` comes from an actual object of
`D(A_f)`. -/
private noncomputable def localizationAwayT_restriction_witness
    (f : A) (K : DMod) :
    Σ' E : DerivedCategory (ModuleCat (Localization.Away f)),
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ≅
        localizationAwayT H f K := by
  let E := localizationAwayT_coextend_preimage (A := A) f K
  classical
  let e :
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ≅
        localizationAwayT H f K :=
    Classical.choice (coextend_k_injective_represents_localizationAwayT (A := A) H f K)
  -- The witness now factors through the dedicated comparison theorem for the coextended
  -- K-injective model, so the remaining blocker is isolated away from this packaging lemma.
  exact ⟨E, e⟩

-- Proof sketch: use the standard two-term resolution of `A_f` and identify the resulting derived
-- internal Hom with the Milnor triangle for the constant tower with transition `f • 𝟙`.
/-- Lemma 15.92.1: the textbook object `T(K, f)` is a derived limit of the constant tower
`\cdots \xrightarrow{f} K \xrightarrow{f} K \xrightarrow{f} K`. -/
theorem localizationAwayT_isDerivedLimit (f : A) (K : DMod) :
    IsDerivedLimit (localizationAwayTower f K) (localizationAwayT H f K) := by
  -- The final theorem is now reduced to the single source-faithful blocker theorem above, so the
  -- open work sits on the explicit hocolim/Milnor bridge rather than on the public statement.
  exact localizationAwayT_isDerivedLimit_via_ringSingle_hocolim (A := A) H f K

-- Proof sketch: by derived adjunction, morphisms from an object of `D(A_f)` to `K` after
-- restriction of scalars are the same source-facing data as morphisms into `T(K, f)`, so the
-- universal vanishing condition is equivalent to `T(K, f)` being zero.
/-- The textbook vanishing statement `T(K, f) = 0` is equivalent to the owner-independent
localization-away derived-Hom vanishing condition. -/
theorem localizationAwayT_isZero_iff
    (f : A) (K : DMod) :
    IsZero (localizationAwayT H f K) ↔
      localizationAwayDerivedHomVanishingCondition f K := by
  constructor
  · intro hzero E
    -- Rewrite maps into `K` as maps into `T(K,f)` and use that maps into a zero object are
    -- automatically subsingleton.
    let e := localized_source_hom_equiv_to_localizationAwayT (A := A) H f K E
    have hsub_target :
        Subsingleton
          (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
            E) ⟶ localizationAwayT H f K) := by
      exact ⟨fun g h ↦ hzero.eq_of_tgt g h⟩
    letI :
        Subsingleton
          (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
            E) ⟶ localizationAwayT H f K) := hsub_target
    exact e.injective.subsingleton
  · intro hvanish
    obtain ⟨E, e⟩ := localizationAwayT_restriction_witness (A := A) H f K
    have hsub_source :
        Subsingleton
          (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
            E) ⟶ localizationAwayT H f K) := by
      letI :
          Subsingleton
            (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
              E) ⟶ K) := hvanish E
      exact
        (localized_source_hom_equiv_to_localizationAwayT (A := A) H f K E).symm.injective.subsingleton
    have hsub_end :
        Subsingleton ((localizationAwayT H f K) ⟶ localizationAwayT H f K) := by
      -- Transport the subsingleton statement along the restriction witness.
      letI :
          Subsingleton
            (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
              E) ⟶ localizationAwayT H f K) := hsub_source
      have hmap_inj :
          Function.Injective
            (fun g : (localizationAwayT H f K) ⟶ localizationAwayT H f K ↦ e.hom ≫ g) := by
        intro g₁ g₂ h
        simpa [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) h
      exact hmap_inj.subsingleton
    -- An object whose identity endomorphism is zero is zero.
    rw [IsZero.iff_id_eq_zero]
    letI : Subsingleton ((localizationAwayT H f K) ⟶ localizationAwayT H f K) := hsub_end
    exact Subsingleton.elim _ _

/-- Rewriting the owner-independent vanishing condition in terms of the source-facing object
`T(K, f)`. -/
theorem localizationAwayDerivedHomVanishingCondition_iff
    (f : A) (K : DMod) :
    localizationAwayDerivedHomVanishingCondition f K ↔
      IsZero (localizationAwayT H f K) := by
  simpa using (localizationAwayT_isZero_iff H f K).symm

end Monoidal

end

end CategoryTheory.DerivedCategory

namespace ModuleCat

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The module-level vanishing condition `T(M, f) = 0`, expressed by specializing the derived
owner from Lemma `15.92.1` to the degree-zero object `M[0]`. -/
def moduleLocalizationAwayTVanishing (M : ModuleCat A) (f : A) : Prop :=
  CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f ((single₀).obj M)

section Monoidal

variable (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
local instance : MonoidalCategory DMod := inferInstance

/-- The module-level vanishing condition is exactly the vanishing of the degree-zero specialization
of `T(K, f)`. -/
theorem moduleLocalizationAwayTVanishing_iff (M : ModuleCat A) (f : A) :
    moduleLocalizationAwayTVanishing M f ↔
      IsZero (CategoryTheory.DerivedCategory.localizationAwayT H f ((single₀).obj M)) := by
  simpa [moduleLocalizationAwayTVanishing] using
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
      H f ((single₀).obj M)

end Monoidal

end

end ModuleCat
