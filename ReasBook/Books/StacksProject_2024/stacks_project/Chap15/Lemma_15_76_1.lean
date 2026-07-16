import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_13
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape Limits
open CategoryTheory.ObjectProperty.IsStableUnderRetracts
open scoped TensorProduct

universe u

noncomputable section

variable {R : Type u} [CommRing R]

section

variable (I : Ideal R)

local notation "ModR" => ModuleCat.{u} R
local notation "ModRI" => ModuleCat.{u} (R ⧸ I)
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)

/- Domain-style sampling:
- primary domain: bounded-above acyclic cochain complexes of `R`-modules, together with reduction
  modulo `I` and the owner retract-stability/direct-summand condition on the allowed termwise
  module class;
- sampled owner declarations:
  `CochainComplex.MinusWithTermsIn`,
  `ObjectProperty.map`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`,
  `HomologicalComplex.Acyclic`,
  `ObjectProperty.IsStableUnderRetracts`;
- best owner abstraction: the bounded-above termwise-`PClass` owner
  `CochainComplex.MinusWithTermsIn PClass`, the reduced owner
  `CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`, the canonical retract-stability owner
  `PClass.IsStableUnderRetracts` for the source direct-summand condition, and the reduction
  owner on cochain complexes `ReduceModI.mapHomologicalComplex (up ℤ)`;
- primitive data: the lifted complex `P : CochainComplex.MinusWithTermsIn PClass` and the target
  reduced complex `E : CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`;
- derived API: the acyclicity of the underlying cochain complexes of `P` and `E`, and the
  existence of a reduction isomorphism
  `((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ (E : CpxRI)`.

Source/core/bridge triage:
- `source-facing`: the existence statement of Lemma `15.76.1`;
- `core/canonical`: `CochainComplex.MinusWithTermsIn PClass`, `HomologicalComplex.Acyclic`, and
  the reduction/base-change owners `ReduceModI`, `ReduceModI.mapHomologicalComplex (up ℤ)`,
  together with the chapter owner `PClass.IsStableUnderRetracts`;
- `bridge/view`: the comparison isomorphism
  `e : ((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ (E : CpxRI)`. -/

-- Proof sketch: start above the top nonzero degree of `E` and descend inductively. At each step,
-- split the already constructed acyclic tail into cycles and boundaries, use the retract-stability
-- owner `PClass.IsStableUnderRetracts` for the source direct-summand condition to keep the cycle
-- objects inside `PClass`, lift the next differential from a projective module, and then upgrade
-- surjectivity modulo `I` to actual surjectivity by hypothesis.
/-- Helper for Lemma 15.76.1: a fixed concrete zero module in `ModuleCat R`, used to avoid
universe noise when the source proof chooses the zero object as the initial lift. -/
abbrev zero_module : ModR :=
  ModuleCat.of R PUnit

/-- Helper for Lemma 15.76.1: an `R`-linear equivalence between quotient modules over `R ⧸ I`
automatically respects the quotient scalar action. -/
lemma linearEquiv_over_quotient_map_smul
    {M N : Type*}
    [AddCommGroup M] [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M]
    [AddCommGroup N] [Module (R ⧸ I) N] [Module R N] [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) (a : R ⧸ I) (x : M) :
    e (a • x) = a • e x := by
  -- Reduce the quotient scalar to a representative in `R`, then reuse the original `R`-linearity.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
  have hr : ((Ideal.Quotient.mk I) r : R ⧸ I) = r • (1 : R ⧸ I) := by
    change ((Ideal.Quotient.mk I) r : R ⧸ I) = ((Ideal.Quotient.mk I) r : R ⧸ I) * 1
    simpa using (mul_one ((Ideal.Quotient.mk I) r)).symm
  have hx : ((Ideal.Quotient.mk I) r : R ⧸ I) • x = r • x := by
    rw [hr]
    simpa [smul_assoc]
  have hy : ((Ideal.Quotient.mk I) r : R ⧸ I) • e x = r • e x := by
    rw [hr]
    simpa [smul_assoc]
  rw [hx, hy]
  simpa using e.map_smul r x

/-- Helper for Lemma 15.76.1: any `R`-linear equivalence between quotient modules upgrades to an
`(R ⧸ I)`-linear equivalence because the quotient scalars factor through `R`. -/
noncomputable def linearEquiv_over_quotient
    {M N : Type*}
    [AddCommGroup M] [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M]
    [AddCommGroup N] [Module (R ⧸ I) N] [Module R N] [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) :
    M ≃ₗ[R ⧸ I] N :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := linearEquiv_over_quotient_map_smul (I := I) e }

/-- Helper for Lemma 15.76.1: the kernel of a surjection onto a `PClass`-projective object again
lies in `PClass`, because the associated short exact sequence splits and hence identifies the middle
term with a biproduct whose left summand is the kernel. -/
lemma module_class_of_kernel_of_surjective_to_projective
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    {P Z : ModR} (f : P ⟶ Z)
    (hP : PClass P) (hZ : PClass Z)
    (hsurj : Function.Surjective f.hom) :
    PClass (kernel f) := by
  let S : ShortComplex ModR := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  -- The canonical kernel short complex is exact because `kernel.ι f` is the kernel of `f`.
  have hS_exact : S.Exact := by
    exact ShortComplex.exact_of_f_is_kernel S (kernelIsKernel f)
  have hS_epi : Epi f := (ModuleCat.epi_iff_surjective f).2 hsurj
  have hS_shortExact : S.ShortExact := by
    exact ShortComplex.ShortExact.mk' hS_exact inferInstance inferInstance
  letI : Projective Z := hprojective hZ
  let splitting : S.Splitting := ShortComplex.ShortExact.splittingOfProjective hS_shortExact
  have hBiprod : PClass ((kernel f) ⊞ Z) := by
    -- The splitting rewrites the middle term as `kernel f ⊞ Z`, so the biproduct inherits the
    -- `PClass` property from `P`.
    exact ObjectProperty.prop_of_iso PClass
      (show P ≅ (kernel f) ⊞ Z from splitting.isoBinaryBiproduct) hP
  -- Retract-stability now extracts the kernel summand from the biproduct presentation.
  exact of_biprod_left PClass hBiprod

/-- Helper for Lemma 15.76.1: reducing an `R`-module modulo `I` is the same as tensoring with
`R ⧸ I`. -/
noncomputable def reduceModI_obj_iso_tensor (M : ModR) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅
      ModuleCat.of (R ⧸ I) ((R ⧸ I) ⊗[R] M) := by
  letI :
      IsScalarTower R (R ⧸ I)
        ↑((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (ModuleCat.of (R ⧸ I) (R ⧸ I))) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ rfl
  let e :
      ↑((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (R ⧸ I) (R ⧸ I))) ≃ₗ[R ⧸ I] (R ⧸ I) :=
    { __ := AddEquiv.refl (R ⧸ I)
      map_smul' := fun _ _ ↦ rfl }
  -- Normalize `ReduceModI.obj` to the tensor presentation used by `ModuleCat.extendScalars`.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso

/-- Helper for Lemma 15.76.1: after the tensor normalization, reduction modulo `I` is the usual
quotient module `M / IM`. -/
noncomputable def reduceModI_obj_iso_quotient (M : ModR) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅
      ModuleCat.of (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  let f :
      (R ⧸ I) →ₗ[R ⧸ I] M →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    (LinearMap.ringLmapEquivSelf (R ⧸ I) (R ⧸ I)
      (M →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)))).symm
      ((I • (⊤ : Submodule R M)).mkQ)
  let e₀ : ((R ⧸ I) ⊗[R] M) →ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    TensorProduct.AlgebraTensorModule.lift f
  have e₀_apply (y : M) : e₀ ((1 : R ⧸ I) ⊗ₜ[R] y) = (I • (⊤ : Submodule R M)).mkQ y := by
    simp [e₀, f]
  have e₀_restrictScalars :
      e₀.restrictScalars R = (TensorProduct.quotTensorEquivQuotSMul M I).toLinearMap := by
    -- Compare both `R`-linear maps on pure tensors, where they have the same quotient formula.
    apply TensorProduct.ext'
    intro q y
    refine Quotient.inductionOn q ?_
    intro a
    change e₀ (Ideal.Quotient.mk I a ⊗ₜ[R] y) =
      TensorProduct.quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I a ⊗ₜ[R] y)
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp [e₀, f]
    simpa using (algebraMap_smul (R ⧸ I) a (Submodule.Quotient.mk y))
  let e : ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    LinearEquiv.ofBijective e₀
      ⟨by
          intro u v huv
          have huv' : e₀.restrictScalars R u = e₀.restrictScalars R v := huv
          rw [e₀_restrictScalars] at huv'
          exact (TensorProduct.quotTensorEquivQuotSMul M I).injective huv'
        , by
          intro z
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
          exact ⟨(1 : R ⧸ I) ⊗ₜ[R] y, e₀_apply y⟩⟩
  -- Compose the tensor model with the quotient-linear equivalence.
  exact reduceModI_obj_iso_tensor (I := I) M ≪≫ e.toModuleIso

/-- Helper for Lemma 15.76.1: the standard quotient/tensor equivalence is natural in the module
map. -/
lemma quotientMapByIdeal_lTensor_naturality
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul M I =
      TensorProduct.quotTensorEquivQuotSMul N I ∘ₗ f.lTensor (R ⧸ I) := by
  -- Route correction: freeze the tensor-to-quotient transport first, so later proofs can compare
  -- `ReduceModI.map` with a concrete quotient map instead of unfolding scalar extension again.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 15.76.1: after identifying reduction modulo `I` with quotient modules,
`ReduceModI.map` becomes the usual quotient map modulo `I`. -/
lemma reduceModI_obj_iso_quotient_inv_mkQ
    (M : ModR) (x : M) :
    ((reduceModI_obj_iso_quotient (I := I) M).inv).hom
        ((I • (⊤ : Submodule R M)).mkQ x) =
      ((reduceModI_obj_iso_tensor (I := I) M).inv).hom
        ((1 : R ⧸ I) ⊗ₜ[R] x) := by
  let f :
      (R ⧸ I) →ₗ[R ⧸ I] M →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    (LinearMap.ringLmapEquivSelf (R ⧸ I) (R ⧸ I)
      (M →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)))).symm
      ((I • (⊤ : Submodule R M)).mkQ)
  let e₀ : ((R ⧸ I) ⊗[R] M) →ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    TensorProduct.AlgebraTensorModule.lift f
  have e₀_apply (y : M) : e₀ ((1 : R ⧸ I) ⊗ₜ[R] y) = (I • (⊤ : Submodule R M)).mkQ y := by
    simp [e₀, f]
  have e₀_restrictScalars :
      e₀.restrictScalars R = (TensorProduct.quotTensorEquivQuotSMul M I).toLinearMap := by
    -- Compare both `R`-linear maps on pure tensors, where they have the same quotient formula.
    apply TensorProduct.ext'
    intro q y
    refine Quotient.inductionOn q ?_
    intro a
    change e₀ (Ideal.Quotient.mk I a ⊗ₜ[R] y) =
      TensorProduct.quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I a ⊗ₜ[R] y)
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp [e₀, f]
    simpa using (algebraMap_smul (R ⧸ I) a (Submodule.Quotient.mk y))
  let e : ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    LinearEquiv.ofBijective e₀
      ⟨by
          intro u v huv
          have huv' : e₀.restrictScalars R u = e₀.restrictScalars R v := huv
          rw [e₀_restrictScalars] at huv'
          exact (TensorProduct.quotTensorEquivQuotSMul M I).injective huv'
        , by
          intro z
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
          exact ⟨(1 : R ⧸ I) ⊗ₜ[R] y, e₀_apply y⟩⟩
  have he_apply :
      e ((1 : R ⧸ I) ⊗ₜ[R] x) = (I • (⊤ : Submodule R M)).mkQ x := e₀_apply x
  have hquot_injective :
      Function.Injective (((reduceModI_obj_iso_quotient (I := I) M).hom).hom) := by
    intro u v huv
    have huv' :=
      congrArg (((reduceModI_obj_iso_quotient (I := I) M).inv).hom) huv
    simpa using huv'
  -- Compare both candidate preimages after applying the forward quotient-model isomorphism.
  apply hquot_injective
  calc
    (((reduceModI_obj_iso_quotient (I := I) M).hom).hom)
        (((reduceModI_obj_iso_quotient (I := I) M).inv).hom
          ((I • (⊤ : Submodule R M)).mkQ x))
      = (I • (⊤ : Submodule R M)).mkQ x := by
          simpa using
            (reduceModI_obj_iso_quotient (I := I) M).inv_hom_id_apply
              ((I • (⊤ : Submodule R M)).mkQ x)
    _ = e ((1 : R ⧸ I) ⊗ₜ[R] x) := by
          exact he_apply.symm
    _ = (((reduceModI_obj_iso_quotient (I := I) M).hom).hom)
          (((reduceModI_obj_iso_tensor (I := I) M).inv).hom
            ((1 : R ⧸ I) ⊗ₜ[R] x)) := by
          simpa [reduceModI_obj_iso_quotient, e] using e₀_apply x

/-- Helper for Lemma 15.76.1: after identifying reduction modulo `I` with quotient modules,
`ReduceModI.map` becomes the usual quotient map modulo `I`. -/
lemma reduceModI_obj_iso_tensor_naturality_on_tmul
    {P Z : ModR} (f : P ⟶ Z) (q : R ⧸ I) (x : P) :
    (((reduceModI_obj_iso_tensor (I := I) Z).hom).hom
        (((ReduceModI).map f).hom
          (((reduceModI_obj_iso_tensor (I := I) P).inv).hom (q ⊗ₜ[R] x)))) =
      f.hom.lTensor (R ⧸ I) (q ⊗ₜ[R] x) := by
  letI :
      IsScalarTower R (R ⧸ I)
        ↑((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (ModuleCat.of (R ⧸ I) (R ⧸ I))) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ rfl
  let e :
      ↑((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (R ⧸ I) (R ⧸ I))) ≃ₗ[R ⧸ I] (R ⧸ I) :=
    { __ := AddEquiv.refl (R ⧸ I)
      map_smul' := fun _ _ ↦ rfl }
  -- Normalize scalar extension to the explicit tensor presentation before evaluating on a pure
  -- tensor, where both comparison isomorphisms are the identity and the middle map is `lTensor`.
  change
    (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R Z))
        ((LinearMap.baseChange (R ⧸ I) f.hom)
          (((TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R P)).symm)
            (q ⊗ₜ[R] x))) =
      f.hom.lTensor (R ⧸ I) (q ⊗ₜ[R] x)
  calc
    (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R Z))
        ((LinearMap.baseChange (R ⧸ I) f.hom)
          (((TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R P)).symm)
            (q ⊗ₜ[R] x))) =
      (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R Z))
        (q ⊗ₜ[R] f.hom x) := by
          have hsymm :
              ((TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R P)).symm)
                (q ⊗ₜ[R] x) = q ⊗ₜ[R] x := by
            change q ⊗ₜ[R] x = q ⊗ₜ[R] x
            rfl
          rw [hsymm]
          rw [LinearMap.baseChange_tmul]
          change q ⊗ₜ[R] f.hom x = q ⊗ₜ[R] f.hom x
          rfl
    _ = q ⊗ₜ[R] f.hom x := by
          simpa [e] using
            (TensorProduct.AlgebraTensorModule.congr_tmul e (LinearEquiv.refl R Z) q (f.hom x))

/-- Helper for Lemma 15.76.1: after identifying reduction modulo `I` with quotient modules,
the conjugated reduction map sends the quotient class of `x` to the quotient class of `f x`. -/
lemma reduceModI_obj_iso_quotient_naturality_on_mkQ
    {P Z : ModR} (f : P ⟶ Z) (x : P) :
    ((((reduceModI_obj_iso_quotient (I := I) P).inv ≫
        ((ReduceModI).map f) ≫
        (reduceModI_obj_iso_quotient (I := I) Z).hom).hom).restrictScalars R)
      ((I • (⊤ : Submodule R P)).mkQ x) =
        (I • (⊤ : Submodule R Z)).mkQ (f.hom x) := by
  -- Route correction: first move the quotient class `mkQ x` to the pure tensor `1 ⊗ₜ x`, then
  -- compute the scalar-extension map on that representative before returning to quotient modules.
  change
    (((reduceModI_obj_iso_quotient (I := I) Z).hom).hom
        (((ReduceModI).map f).hom
          (((reduceModI_obj_iso_quotient (I := I) P).inv).hom
            ((I • (⊤ : Submodule R P)).mkQ x)))) =
      (I • (⊤ : Submodule R Z)).mkQ (f.hom x)
  rw [reduceModI_obj_iso_quotient_inv_mkQ (I := I) P x]
  change
    TensorProduct.quotTensorEquivQuotSMul Z I
        ((((reduceModI_obj_iso_tensor (I := I) Z).hom).hom)
          (((ReduceModI).map f).hom
            (((reduceModI_obj_iso_tensor (I := I) P).inv).hom
              ((1 : R ⧸ I) ⊗ₜ[R] x)))) =
      (I • (⊤ : Submodule R Z)).mkQ (f.hom x)
  rw [reduceModI_obj_iso_tensor_naturality_on_tmul (I := I) f (1 : R ⧸ I) x]
  have hnat :=
    LinearMap.congr_fun (quotientMapByIdeal_lTensor_naturality (I := I) f.hom)
      ((1 : R ⧸ I) ⊗ₜ[R] x)
  calc
    TensorProduct.quotTensorEquivQuotSMul Z I
        (f.hom.lTensor (R ⧸ I) ((1 : R ⧸ I) ⊗ₜ[R] x)) =
      (f.hom.quotientMapByIdeal I)
        (TensorProduct.quotTensorEquivQuotSMul P I ((1 : R ⧸ I) ⊗ₜ[R] x)) := by
          exact hnat.symm
    _ = (I • (⊤ : Submodule R Z)).mkQ (f.hom x) := by
          have hmktmul :
              TensorProduct.quotTensorEquivQuotSMul P I ((1 : R ⧸ I) ⊗ₜ[R] x) =
                (I • (⊤ : Submodule R P)).mkQ x := by
            change TensorProduct.quotTensorEquivQuotSMul P I
                ((Ideal.Quotient.mk I (1 : R)) ⊗ₜ[R] x) =
              (I • (⊤ : Submodule R P)).mkQ x
            rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
            simp
          rw [hmktmul]
          simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 15.76.1: after identifying reduction modulo `I` with quotient modules,
`ReduceModI.map` becomes the usual quotient map modulo `I`. -/
lemma reduceModI_obj_iso_quotient_naturality
    {P Z : ModR} (f : P ⟶ Z) :
    (((reduceModI_obj_iso_quotient (I := I) P).inv ≫
        ((ReduceModI).map f) ≫
        (reduceModI_obj_iso_quotient (I := I) Z).hom).hom).restrictScalars R =
      f.hom.quotientMapByIdeal I :=
by
  -- The transport comparison is already proved on quotient representatives, so extensionality on
  -- `Submodule.mkQ` closes the full linear-map equality without reopening tensor computations.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) x
  -- Re-run the representative computation inside the extensionality proof to avoid a universe-
  -- elaboration glitch when reusing the pointwise theorem as a term.
  change
    ((((reduceModI_obj_iso_quotient (I := I) P).inv ≫
        ((ReduceModI).map f) ≫
        (reduceModI_obj_iso_quotient (I := I) Z).hom).hom).restrictScalars R)
      ((I • (⊤ : Submodule R P)).mkQ x) =
    (f.hom.quotientMapByIdeal I) ((I • (⊤ : Submodule R P)).mkQ x)
  change
    (((reduceModI_obj_iso_quotient (I := I) Z).hom).hom
        (((ReduceModI).map f).hom
          (((reduceModI_obj_iso_quotient (I := I) P).inv).hom
            ((I • (⊤ : Submodule R P)).mkQ x)))) =
      (f.hom.quotientMapByIdeal I) ((I • (⊤ : Submodule R P)).mkQ x)
  rw [reduceModI_obj_iso_quotient_inv_mkQ (I := I) P x]
  change
    TensorProduct.quotTensorEquivQuotSMul Z I
        ((((reduceModI_obj_iso_tensor (I := I) Z).hom).hom)
          (((ReduceModI).map f).hom
            (((reduceModI_obj_iso_tensor (I := I) P).inv).hom
              ((1 : R ⧸ I) ⊗ₜ[R] x)))) =
      (f.hom.quotientMapByIdeal I) ((I • (⊤ : Submodule R P)).mkQ x)
  rw [reduceModI_obj_iso_tensor_naturality_on_tmul (I := I) f (1 : R ⧸ I) x]
  have hnat :=
    LinearMap.congr_fun (quotientMapByIdeal_lTensor_naturality (I := I) f.hom)
      ((1 : R ⧸ I) ⊗ₜ[R] x)
  calc
    TensorProduct.quotTensorEquivQuotSMul Z I
        (f.hom.lTensor (R ⧸ I) ((1 : R ⧸ I) ⊗ₜ[R] x)) =
      (f.hom.quotientMapByIdeal I)
        (TensorProduct.quotTensorEquivQuotSMul P I ((1 : R ⧸ I) ⊗ₜ[R] x)) := by
          exact hnat.symm
    _ = (f.hom.quotientMapByIdeal I) ((I • (⊤ : Submodule R P)).mkQ x) := by
          change (f.hom.quotientMapByIdeal I)
              (TensorProduct.quotTensorEquivQuotSMul P I
                ((Ideal.Quotient.mk I (1 : R)) ⊗ₜ[R] x)) =
            (f.hom.quotientMapByIdeal I) ((I • (⊤ : Submodule R P)).mkQ x)
          rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
          simp

/-- Helper for Lemma 15.76.1: after subtracting the chosen section part, a point lies in the
kernel of the split surjection. -/
lemma sub_section_mem_ker_of_rightInverse_local
    {P Z : ModR}
    (q : P →ₗ[R] Z)
    (s : Z →ₗ[R] P)
    (hs : q.comp s = LinearMap.id)
    (z : P) :
    z - s (q z) ∈ LinearMap.ker q := by
  -- Applying `q` removes the corrected section term because `q ∘ s = id`.
  change q (z - s (q z)) = 0
  have hs_apply : q (s (q z)) = q z := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : Z →ₗ[R] Z => f (q z)) hs
  simpa [hs_apply]

/-- Helper for Lemma 15.76.1: evaluating a quotient map on a quotient class matches quotienting
after applying the underlying linear map. -/
lemma quotientMapByIdeal_apply_mkQ_local
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (x : M) :
    f.quotientMapByIdeal I ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := by
  -- Expand the induced quotient map through the defining `mapQ_mkQ` square.
  simpa [LinearMap.quotientMapByIdeal] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) f) x

/-- Helper for Lemma 15.76.1: if an element of `I • P` is corrected by subtracting its section
part, the result comes from `I • ker q`. -/
lemma sub_section_mem_map_smul_top_ker_of_rightInverse_local
    {P Z : ModR}
    (q : P →ₗ[R] Z)
    (s : Z →ₗ[R] P)
    (hs : q.comp s = LinearMap.id)
    {z : P}
    (hz : z ∈ I • (⊤ : Submodule R P)) :
    z - s (q z) ∈
      Submodule.map (LinearMap.ker q).subtype (I • (⊤ : Submodule R (LinearMap.ker q))) := by
  -- Keep the corrected term `z - s (q z)` as the induction invariant on `I • ⊤`.
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro a ha x hx
    refine ⟨a • ⟨x - s (q x), sub_section_mem_ker_of_rightInverse_local q s hs x⟩, ?_, ?_⟩
    · simpa using
        (Submodule.smul_mem_smul
          (I := I)
          (N := (⊤ : Submodule R (LinearMap.ker q)))
          ha
          (by simp) :
          a • ⟨x - s (q x), sub_section_mem_ker_of_rightInverse_local q s hs x⟩ ∈
            I • (⊤ : Submodule R (LinearMap.ker q)))
    · simp [smul_sub, LinearMap.map_smul]
  · intro x y hx hy
    -- The induction invariant is additive because both `q` and `s` are linear.
    simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      Submodule.add_mem _ hx hy

/-- Helper for Lemma 15.76.1: quotienting a kernel element of a split lift lands in the kernel of
the prescribed quotient-side map. -/
lemma quotient_mk_mem_ker_of_mem_ker_general
    {P Z : ModR}
    (q : P ⟶ Z)
    (qbar :
      (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R]
        (Z ⧸ (I • (⊤ : Submodule R Z))))
    (hqbar : q.hom.quotientMapByIdeal I = qbar)
    (x : LinearMap.ker q.hom) :
    (I • (⊤ : Submodule R P)).mkQ x.1 ∈ LinearMap.ker qbar := by
  -- Evaluate the quotient-side kernel condition on the ambient quotient representative of `x`.
  change qbar ((I • (⊤ : Submodule R P)).mkQ x.1) = 0
  rw [← hqbar, quotientMapByIdeal_apply_mkQ_local]
  simpa [x.2]

/-- Helper for Lemma 15.76.1: the split kernel quotient descends to the reduced kernel for an
arbitrary split map of `R`-modules. -/
noncomputable def split_reduction_kernel_map_general
    {P Z : ModR}
    (q : P ⟶ Z)
    (s : Z ⟶ P)
    (qbar :
      (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R]
        (Z ⧸ (I • (⊤ : Submodule R Z))))
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hqbar : q.hom.quotientMapByIdeal I = qbar) :
    ((LinearMap.ker q.hom) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q.hom)))) →ₗ[R]
      LinearMap.ker qbar := by
  let toReducedKernel : LinearMap.ker q.hom →ₗ[R] LinearMap.ker qbar :=
    LinearMap.codRestrict (LinearMap.ker qbar)
      (((I • (⊤ : Submodule R P)).mkQ).comp (LinearMap.ker q.hom).subtype)
      (quotient_mk_mem_ker_of_mem_ker_general (I := I) q qbar hqbar)
  have hkill :
      I • (⊤ : Submodule R (LinearMap.ker q.hom)) ≤ LinearMap.ker toReducedKernel := by
    intro x hx
    -- Elements coming from `I • ker q` already vanish in the ambient quotient.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy
      apply Subtype.ext
      change (I • (⊤ : Submodule R P)).mkQ (a • y.1) = 0
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      simpa using
        (Submodule.smul_mem_smul
          (I := I)
          (N := (⊤ : Submodule R P))
          ha
          (by simp) :
          a • y.1 ∈ I • (⊤ : Submodule R P))
    · intro x y hx hy
      apply Subtype.ext
      have hx0 : (toReducedKernel x).1 = 0 := by
        simpa using congrArg Subtype.val hx
      have hy0 : (toReducedKernel y).1 = 0 := by
        simpa using congrArg Subtype.val hy
      simp [hx0, hy0]
  -- Descend the ambient quotient-class map across the quotient of `ker q`.
  exact Submodule.liftQ (I • (⊤ : Submodule R (LinearMap.ker q.hom))) toReducedKernel hkill

/-- Helper for Lemma 15.76.1: the descended split-kernel map is computed by quotienting the
ambient representative. -/
lemma split_reduction_kernel_map_general_mkQ
    {P Z : ModR}
    (q : P ⟶ Z)
    (s : Z ⟶ P)
    (qbar :
      (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R]
        (Z ⧸ (I • (⊤ : Submodule R Z))))
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hqbar : q.hom.quotientMapByIdeal I = qbar)
    (z : LinearMap.ker q.hom) :
    split_reduction_kernel_map_general (I := I) q s qbar hs hqbar
        ((I • (⊤ : Submodule R (LinearMap.ker q.hom))).mkQ z) =
      ⟨(I • (⊤ : Submodule R P)).mkQ z.1,
        quotient_mk_mem_ker_of_mem_ker_general (I := I) q qbar hqbar z⟩ := by
  -- Unfold once and evaluate the descended quotient map on the chosen representative.
  rw [split_reduction_kernel_map_general]
  rfl

/-- Helper for Lemma 15.76.1: every quotient-side kernel class has a corrected representative in
the lifted kernel. -/
lemma split_reduction_kernel_map_general_surjective
    {P Z : ModR}
    (q : P ⟶ Z)
    (s : Z ⟶ P)
    (qbar :
      (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R]
        (Z ⧸ (I • (⊤ : Submodule R Z))))
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hqbar : q.hom.quotientMapByIdeal I = qbar) :
    Function.Surjective (split_reduction_kernel_map_general (I := I) q s qbar hs hqbar) := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y.1
  have hqx_zero : (I • (⊤ : Submodule R Z)).mkQ (q.hom x) = 0 := by
    -- The quotient-side kernel condition says that the quotient class of `q x` vanishes.
    have hy_zero : qbar ((I • (⊤ : Submodule R P)).mkQ x) = 0 := by
      simpa [hx] using y.2
    simpa [← hqbar, quotientMapByIdeal_apply_mkQ_local] using hy_zero
  have hqx_mem : q.hom x ∈ I • (⊤ : Submodule R Z) :=
    (Submodule.Quotient.mk_eq_zero _).1 hqx_zero
  have hsqx_mem : s.hom (q.hom x) ∈ I • (⊤ : Submodule R P) := by
    exact (Submodule.smul_top_le_comap_smul_top I s.hom) hqx_mem
  let z : LinearMap.ker q.hom :=
    ⟨x - s.hom (q.hom x),
      sub_section_mem_ker_of_rightInverse_local q.hom s.hom hs x⟩
  refine ⟨(I • (⊤ : Submodule R (LinearMap.ker q.hom))).mkQ z, ?_⟩
  rw [split_reduction_kernel_map_general_mkQ (I := I) q s qbar hs hqbar z]
  apply Subtype.ext
  have hsqx_zero : (I • (⊤ : Submodule R P)).mkQ (s.hom (q.hom x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hsqx_mem
  calc
    (I • (⊤ : Submodule R P)).mkQ z.1
        = (I • (⊤ : Submodule R P)).mkQ x
            - (I • (⊤ : Submodule R P)).mkQ (s.hom (q.hom x)) := by
              simp [z]
    _ = y.1 - 0 := by rw [hx, hsqx_zero]
    _ = y.1 := by simp

/-- Helper for Lemma 15.76.1: if the descended split-kernel class is trivial, the original class
already lies in `I • ker q`. -/
lemma split_reduction_kernel_map_general_injective
    {P Z : ModR}
    (q : P ⟶ Z)
    (s : Z ⟶ P)
    (qbar :
      (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R]
        (Z ⧸ (I • (⊤ : Submodule R Z))))
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hqbar : q.hom.quotientMapByIdeal I = qbar) :
    Function.Injective (split_reduction_kernel_map_general (I := I) q s qbar hs hqbar) := by
  intro x y hxy
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (LinearMap.ker q.hom))) x
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (LinearMap.ker q.hom))) y
  rw [split_reduction_kernel_map_general_mkQ (I := I) q s qbar hs hqbar z,
    split_reduction_kernel_map_general_mkQ (I := I) q s qbar hs hqbar w] at hxy
  apply (Submodule.Quotient.eq _).2
  have hambient :
      (I • (⊤ : Submodule R P)).mkQ z.1 =
        (I • (⊤ : Submodule R P)).mkQ w.1 := by
    exact congrArg Subtype.val hxy
  have hdiff_mem :
      z.1 - w.1 ∈ I • (⊤ : Submodule R P) :=
    (Submodule.Quotient.eq _).1 hambient
  have hmap_mem :
      z.1 - w.1 ∈
        Submodule.map (LinearMap.ker q.hom).subtype
          (I • (⊤ : Submodule R (LinearMap.ker q.hom))) := by
    -- Because `z - w` still lies in the kernel, the split correction lands in `I • ker q`.
    simpa [map_sub, z.2, w.2] using
      sub_section_mem_map_smul_top_ker_of_rightInverse_local
        (I := I) q.hom s.hom hs (z := z.1 - w.1) hdiff_mem
  rcases hmap_mem with ⟨u, huI, huval⟩
  have huzw : u = z - w := by
    apply Subtype.ext
    simpa using huval
  simpa [huzw] using huI

/-- Helper for Lemma 15.76.1: for an arbitrary split surjection, the quotient of the lifted
kernel identifies with the reduced kernel of the quotient-side map. -/
noncomputable def kernel_quotient_equiv_of_split_reduction_general
    {P Z : ModR}
    (q : P ⟶ Z)
    (s : Z ⟶ P)
    (qbar :
      (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R]
        (Z ⧸ (I • (⊤ : Submodule R Z))))
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hqbar : q.hom.quotientMapByIdeal I = qbar) :
    ((LinearMap.ker q.hom) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q.hom)))) ≃ₗ[R]
      LinearMap.ker qbar := by
  -- Package the descended map once surjectivity and injectivity have been established.
  exact LinearEquiv.ofBijective
    (split_reduction_kernel_map_general (I := I) q s qbar hs hqbar)
    ⟨split_reduction_kernel_map_general_injective (I := I) q s qbar hs hqbar,
      split_reduction_kernel_map_general_surjective (I := I) q s qbar hs hqbar⟩

/-- Helper for Lemma 15.76.1: the cocycle object in degree `n` of a cochain complex over
`R ⧸ I`. -/
abbrev cocycle (E : CpxRI) (n : ℤ) :=
  kernel (E.d n (n + 1))

/-- Helper for Lemma 15.76.1: the differential `d^n` lands in the next cocycle object. -/
lemma d_comp_to_next_cocycle_zero (E : CpxRI) (n : ℤ) :
    E.d n (n + 1) ≫ E.d (n + 1) (n + 2) = 0 := by
  -- This is the usual `d ∘ d = 0` identity in the cochain complex.
  simpa using E.d_comp_d n (n + 1) (n + 2)

/-- Helper for Lemma 15.76.1: the canonical map from degree `n` to the next cocycle object. -/
abbrev to_next_cocycle (E : CpxRI) (n : ℤ) : E.X n ⟶ kernel (E.d (n + 1) (n + 2)) :=
  kernel.lift (E.d (n + 1) (n + 2)) (E.d n (n + 1))
    (d_comp_to_next_cocycle_zero (I := I) E n)

/-- Helper for Lemma 15.76.1: the cocycle inclusion in degree `n` is annihilated by the canonical
map to the next cocycle object. -/
lemma cocycle_to_next_cocycle_zero (E : CpxRI) (n : ℤ) :
    kernel.ι (E.d n (n + 1)) ≫ to_next_cocycle (I := I) E n = 0 := by
  -- After composing with the kernel inclusion on the target, this is just `d ∘ d = 0`.
  apply (cancel_mono (kernel.ι (E.d (n + 1) (n + 2)))).1
  simpa [Category.assoc, to_next_cocycle] using kernel.condition (E.d n (n + 1))

/-- Helper for Lemma 15.76.1: the inclusion of cocycles in degree `n` is the kernel of the
canonical map to the next cocycle object. -/
def cocycle_inclusion_is_kernel
    (E : CpxRI) (n : ℤ) :
    IsLimit
      (KernelFork.ofι (kernel.ι (E.d n (n + 1)))
        (cocycle_to_next_cocycle_zero (I := I) E n)) := by
  -- The cocycle object is definitionally the kernel of the differential `d^n`.
  refine KernelFork.IsLimit.ofι' (kernel.ι (E.d n (n + 1)))
    (cocycle_to_next_cocycle_zero (I := I) E n) ?_
  · intro W k hk
    -- Cancel the monomorphism `kernel.ι (d^(n+1))` to move back to the differential `d^n`.
    refine ⟨kernel.lift (E.d n (n + 1)) k ?_, by rw [kernel.lift_ι]⟩
    have hk' := congrArg (fun t ↦ t ≫ kernel.ι (E.d (n + 1) (n + 2))) hk
    simpa [Category.assoc, to_next_cocycle] using hk'

/-- Helper for Lemma 15.76.1: the cocycle sequence
`cocycle E n ⟶ E.X n ⟶ cocycle E (n + 1)` is exact at the middle term. -/
lemma cocycle_exact (E : CpxRI) (n : ℤ) :
    (ShortComplex.mk (kernel.ι (E.d n (n + 1))) (to_next_cocycle (I := I) E n)
      (cocycle_to_next_cocycle_zero (I := I) E n)).Exact := by
  let S : ShortComplex ModRI :=
    ShortComplex.mk (kernel.ι (E.d n (n + 1))) (to_next_cocycle (I := I) E n)
      (cocycle_to_next_cocycle_zero (I := I) E n)
  -- The previous lemma identifies the first map with the kernel of the second.
  have hkernel : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S] using cocycle_inclusion_is_kernel (I := I) E n
  exact ShortComplex.exact_of_f_is_kernel S hkernel

/-- Helper for Lemma 15.76.1: in an acyclic complex, every cocycle in degree `n + 1` is the
image of a term in degree `n`. -/
lemma surjective_to_next_cocycle_of_acyclic
    (E : CpxRI) (n : ℤ) (hacyclic : E.Acyclic) :
    Function.Surjective (to_next_cocycle (I := I) E n).hom := by
  have hExactAt : E.ExactAt (n + 1) := by
    -- Acyclicity identifies degreewise exactness for the original complex.
    exact (HomologicalComplex.acyclic_iff E).mp hacyclic (n + 1)
  have hExactSc : (E.sc (n + 1)).Exact := by
    -- Rewrite that exactness as exactness of the short complex `Eⁿ → Eⁿ⁺¹ → Eⁿ⁺²`.
    exact (HomologicalComplex.exactAt_iff E (n + 1)).mp hExactAt
  have hRangeKer' :
      LinearMap.range (E.d ((up ℤ).prev (n + 1)) (n + 1)).hom =
        LinearMap.ker (E.d (n + 1) ((up ℤ).next (n + 1))).hom := by
    -- In `ModuleCat`, exactness is exactly the `range = ker` statement on underlying maps.
    simpa [HomologicalComplex.sc] using ShortComplex.Exact.moduleCat_range_eq_ker hExactSc
  have hRangeKer :
      LinearMap.range (E.d n (n + 1)).hom =
        LinearMap.ker (E.d (n + 1) (n + 2)).hom := by
    have hprev : (up ℤ).prev (n + 1) = n := by
      simpa using (CochainComplex.prev ℤ (n + 1))
    have hnext : (up ℤ).next (n + 1) = n + 2 := by
      simpa [add_assoc] using (CochainComplex.next ℤ (n + 1))
    rw [hprev, hnext] at hRangeKer'
    exact hRangeKer'
  have hι_injective :
      Function.Injective (kernel.ι (E.d (n + 1) (n + 2))).hom := by
    simpa using
      (ModuleCat.mono_iff_injective (kernel.ι (E.d (n + 1) (n + 2)))).1 inferInstance
  intro y
  let y' : LinearMap.ker (E.d (n + 1) (n + 2)).hom :=
    ((ModuleCat.kernelIsoKer (E.d (n + 1) (n + 2))).hom).hom y
  have hy_val : (kernel.ι (E.d (n + 1) (n + 2))).hom y = y'.1 := by
    -- Evaluating the concrete kernel comparison identifies the categorical kernel element with its
    -- underlying vector in `ker dⁿ⁺¹`.
    change (kernel.ι (E.d (n + 1) (n + 2))).hom y =
      ((ModuleCat.ofHom (LinearMap.ker (E.d (n + 1) (n + 2)).hom).subtype).hom
        (((ModuleCat.kernelIsoKer (E.d (n + 1) (n + 2))).hom).hom y))
    exact
      (congrArg
        (fun g : kernel (E.d (n + 1) (n + 2)) ⟶ E.X (n + 1) => g.hom y)
        (ModuleCat.kernelIsoKer_hom_ker_subtype (f := E.d (n + 1) (n + 2)))).symm
  have hy_range : y'.1 ∈ LinearMap.range (E.d n (n + 1)).hom := by
    have hy_ker : y'.1 ∈ LinearMap.ker (E.d (n + 1) (n + 2)).hom := by
      -- A cocycle is, by definition, annihilated by the next differential.
      simpa [LinearMap.mem_ker] using y'.2
    exact hRangeKer.symm ▸ hy_ker
  rcases hy_range with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Compare the two cocycles after applying the kernel inclusion back to `E.X (n + 1)`.
  apply hι_injective
  calc
    (kernel.ι (E.d (n + 1) (n + 2))).hom ((to_next_cocycle (I := I) E n).hom x)
        = (E.d n (n + 1)).hom x := by
            simpa [to_next_cocycle]
    _ = y'.1 := hx
    _ = (kernel.ι (E.d (n + 1) (n + 2))).hom y := hy_val.symm

/-- Helper for Lemma 15.76.1: in an acyclic complex, the cocycle sequence
`cocycle E n ⟶ E.X n ⟶ cocycle E (n + 1)` is short exact. -/
lemma cocycle_shortExact_of_acyclic
    (E : CpxRI) (n : ℤ) (hacyclic : E.Acyclic) :
    (ShortComplex.mk (kernel.ι (E.d n (n + 1))) (to_next_cocycle (I := I) E n)
      (cocycle_to_next_cocycle_zero (I := I) E n)).ShortExact := by
  let S : ShortComplex ModRI :=
    ShortComplex.mk (kernel.ι (E.d n (n + 1))) (to_next_cocycle (I := I) E n)
      (cocycle_to_next_cocycle_zero (I := I) E n)
  -- Combine the kernel description with the acyclic surjectivity statement to obtain
  -- the short exact sequence that drives the descending cocycle recursion.
  have hExact : S.Exact := by
    simpa [S] using cocycle_exact (I := I) E n
  have hEpi : Epi S.g := by
    exact (ModuleCat.epi_iff_surjective S.g).2
      (by simpa [S] using surjective_to_next_cocycle_of_acyclic (I := I) E n hacyclic)
  exact ShortComplex.ShortExact.mk' hExact inferInstance hEpi

/-- Helper for Lemma 15.76.1: the surjectivity of `to_next_cocycle` is preserved after
identifying the source and target with chosen quotient models. -/
lemma surjective_to_next_cocycle_conjugate
    (E : CpxRI) (n : ℤ) {P Z : ModRI}
    (ep : P ≅ E.X n) (ez : Z ≅ kernel (E.d (n + 1) (n + 2)))
    (hacyclic : E.Acyclic) :
    Function.Surjective
      ((ep.hom ≫
        to_next_cocycle (I := I) E n ≫
        ez.inv).hom) := by
  -- Move the target point across `ez`, solve surjectivity for `to_next_cocycle`, and then
  -- pull the chosen preimage back across `ep`.
  intro z
  obtain ⟨x, hx⟩ := surjective_to_next_cocycle_of_acyclic (I := I) E n hacyclic (ez.hom.hom z)
  refine ⟨ep.inv.hom x, ?_⟩
  change ez.inv.hom (((to_next_cocycle (I := I) E n).hom) (ep.hom.hom (ep.inv.hom x))) = z
  simpa [hx]

/-- Helper for Lemma 15.76.1: if some reduced module comes from `PClass`, then `PClass`
contains the zero `R`-module because the zero object is a retract of every object. -/
lemma module_class_zero_of_reduced_term
    (PClass : ObjectProperty ModR)
    [PClass.IsStableUnderRetracts]
    {Y : ModRI}
    (hY : (PClass.map ReduceModI) Y) :
    PClass (ModuleCat.of R PUnit) := by
  rcases hY with ⟨P, hP, -⟩
  -- Retract-stability moves membership along the canonical retraction `0 ↪ P ↠ 0`.
  exact PClass.prop_of_retract ((ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).retract P) hP

/-- Helper for Lemma 15.76.1: every term of the reduced bounded-above complex has a chosen lift in
`PClass`. -/
lemma exists_term_lift_of_minusWithTermsIn
    (PClass : ObjectProperty ModR)
    (E : CochainComplex.MinusWithTermsIn (PClass.map ReduceModI))
    (n : ℤ) :
    ∃ P : ModR, PClass P ∧ Nonempty (((ReduceModI).obj P) ≅ (E : CpxRI).X n) := by
  -- Unpack the `ObjectProperty.map` witness stored by `E.term_mem n`.
  simpa using E.term_mem n

/-- Helper for Lemma 15.76.1: if the reduced complex is zero above `b`, then the next cocycle
object is already zero, hence canonically isomorphic to the reduction of the zero `R`-module. -/
noncomputable def cocycle_succ_iso_zero_of_isStrictlyLE
    (E : CpxRI) {b : ℤ} (hb : E.IsStrictlyLE b) :
    ((ReduceModI).obj (zero_module (R := R))) ≅ kernel (E.d (b + 1) (b + 2)) := by
  letI : E.IsStrictlyLE b := hb
  have hsourceZero : IsZero (E.X (b + 1)) := by
    exact E.isZero_of_isStrictlyLE b (b + 1) (by omega)
  have hcocycleZero : IsZero (kernel (E.d (b + 1) (b + 2))) := by
    -- The successor cocycle sits as a subobject of the already vanishing source term.
    exact Limits.IsZero.of_mono (kernel.ι (E.d (b + 1) (b + 2))) hsourceZero
  have hreducedZero : IsZero ((ReduceModI).obj (zero_module (R := R))) := by
    -- Reduction preserves the zero object.
    exact Functor.map_isZero ReduceModI
      (ModuleCat.isZero_of_subsingleton (zero_module (R := R)))
  exact hreducedZero.isoZero ≪≫ hcocycleZero.isoZero.symm

/-- Helper for Lemma 15.76.1: after replacing the reduced source and target by the concrete
quotient-module models, the cocycle map in degree `n` is still surjective. -/
lemma surjective_to_next_cocycle_in_quotient_model
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2)))
    (hacyclic : E.Acyclic) :
    Function.Surjective
      ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom) := by
  -- With the quotient-model identifications fixed once, this is exactly the conjugated
  -- surjectivity statement for `to_next_cocycle`.
  simpa using
    surjective_to_next_cocycle_conjugate (I := I) E n epq ezq hacyclic

/-- Helper for Lemma 15.76.1: a cocycle map written on quotient-module models lifts to an
`R`-linear map between the chosen source terms. -/
lemma exists_lift_to_next_cocycle_in_quotient_model
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (hP : PClass P)
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2))) :
    ∃ q : P ⟶ Z,
      q.hom.quotientMapByIdeal I =
        ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R := by
  let qbar :
      (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R] (Z ⧸ (I • (⊤ : Submodule R Z))) :=
    ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R
  let qbarLift : P →ₗ[R] (Z ⧸ (I • (⊤ : Submodule R Z))) :=
    qbar.comp (I • (⊤ : Submodule R P)).mkQ
  let qmk : Z ⟶ ModuleCat.of R (Z ⧸ (I • (⊤ : Submodule R Z))) :=
    ModuleCat.ofHom (I • (⊤ : Submodule R Z)).mkQ
  let qlift : P ⟶ ModuleCat.of R (Z ⧸ (I • (⊤ : Submodule R Z))) :=
    ModuleCat.ofHom qbarLift
  letI : Projective P := hprojective hP
  -- Lift the quotient-side cocycle map through the canonical quotient projection of `Z`.
  let q : P ⟶ Z := Projective.factorThru qlift qmk
  have hq : q ≫ qmk = qlift := by
    exact Projective.factorThru_comp qlift qmk
  have hqsmul :
      I • (⊤ : Submodule R P) ≤
        Submodule.comap q.hom (I • (⊤ : Submodule R Z)) := by
    exact Submodule.smul_top_le_comap_smul_top I q.hom
  have hcomp :
      ((I • (⊤ : Submodule R P)).mapQ (I • (⊤ : Submodule R Z)) q.hom hqsmul).comp
          (I • (⊤ : Submodule R P)).mkQ =
        (I • (⊤ : Submodule R Z)).mkQ.comp q.hom :=
    Submodule.mapQ_mkQ (I • (⊤ : Submodule R P)) (I • (⊤ : Submodule R Z)) q.hom
  have hqhom :
      (I • (⊤ : Submodule R Z)).mkQ.comp q.hom = qbarLift := by
    exact congrArg ModuleCat.Hom.hom hq
  refine ⟨q, ?_⟩
  -- Compare the induced quotient map and the prescribed cocycle map on quotient representatives.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) x
  simpa [LinearMap.quotientMapByIdeal, qbar, qbarLift] using
    (DFunLike.congr_fun hcomp x).trans (DFunLike.congr_fun hqhom x)

/-- Helper for Lemma 15.76.1: surjectivity is invariant under conjugation by linear
equivalences. -/
lemma surjective_conjugate_iff_of_linearEquiv
    {A : Type*} [CommRing A]
    {M M' N N' : Type*}
    [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M']
    [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N']
    (f : M →ₗ[A] N) (eM : M ≃ₗ[A] M') (eN : N ≃ₗ[A] N') :
    Function.Surjective f ↔
      Function.Surjective (eN.toLinearMap.comp (f.comp eM.symm.toLinearMap)) := by
  constructor
  · intro hsurj y'
    -- Transport a target point back across `eN`, solve surjectivity for `f`, and push the
    -- chosen preimage forward across `eM`.
    obtain ⟨x, hx⟩ := hsurj (eN.symm y')
    refine ⟨eM x, ?_⟩
    change eN (f (eM.symm (eM x))) = y'
    simpa [hx]
  · intro hsurj y
    -- Pull the point `eN y` back along the conjugated map, then cancel `eN` to recover a
    -- preimage for `y`.
    obtain ⟨x', hx'⟩ := hsurj (eN y)
    refine ⟨eM.symm x', ?_⟩
    change eN (f (eM.symm x')) = eN y at hx'
    exact eN.injective hx'

/-- Helper for Lemma 15.76.1: conjugating `ReduceModI.map f` by the fixed quotient-model
isomorphisms preserves surjectivity. -/
lemma reduceModI_obj_iso_quotient_surjective_transport
    {P Z : ModR} (f : P ⟶ Z) :
    Function.Surjective (((ReduceModI).map f).hom) ↔
      Function.Surjective
        ((((reduceModI_obj_iso_quotient (I := I) P).inv ≫
            (ReduceModI).map f ≫
            (reduceModI_obj_iso_quotient (I := I) Z).hom).hom).restrictScalars R) := by
  let eP := reduceModI_obj_iso_quotient (I := I) P
  let eZ := reduceModI_obj_iso_quotient (I := I) Z
  constructor
  · intro hsurj y
    -- Move the target point back through the quotient-model isomorphism, solve surjectivity for
    -- `ReduceModI.map f`, and then push the chosen preimage forward through the source model.
    obtain ⟨x, hx⟩ := hsurj (eZ.inv.hom y)
    refine ⟨eP.hom x, ?_⟩
    change
      eZ.hom (((ReduceModI).map f).hom (eP.inv.hom (eP.hom x))) = y
    simpa using congrArg eZ.hom hx
  · intro hsurj y
    -- Solve surjectivity for the conjugated quotient-model map at `eZ.hom y`, then cancel the
    -- target isomorphism to recover a preimage for `y`.
    obtain ⟨x, hx⟩ := hsurj (eZ.hom y)
    refine ⟨eP.inv.hom x, ?_⟩
    -- Apply the inverse quotient-model isomorphism to the solved conjugated equation.
    have hx' := congrArg eZ.inv.hom hx
    change
      eZ.inv.hom (eZ.hom (((ReduceModI).map f).hom (eP.inv.hom x))) =
        eZ.inv.hom (eZ.hom y) at hx'
    simpa using hx'

/-- Helper for Lemma 15.76.1: the quotient map on `P / IP` induced by an `R`-linear morphism. -/
abbrev quotient_model_map_by_ideal
    {P Z : ModR} (f : P ⟶ Z) :
    (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R] (Z ⧸ (I • (⊤ : Submodule R Z))) :=
  f.hom.quotientMapByIdeal I

/-- Helper for Lemma 15.76.1: once a chosen lift has the prescribed quotient-model cocycle map,
the standing surjectivity-modulo-`I` hypothesis upgrades it to an actual surjection. -/
lemma surjective_reduceModI_map_iff_quotientMapByIdeal
    {P Z : ModR} (f : P ⟶ Z) :
    Function.Surjective (((ReduceModI).map f).hom) ↔
      Function.Surjective (f.hom.quotientMapByIdeal I) := by
  -- Proof comment: the fixed quotient-model isomorphisms preserve surjectivity, and the
  -- conjugated map is exactly `quotientMapByIdeal`.
  simpa [reduceModI_obj_iso_quotient_naturality (I := I) (P := P) (Z := Z) f] using
    (reduceModI_obj_iso_quotient_surjective_transport (I := I) (P := P) (Z := Z) f)

/-- Helper for Lemma 15.76.1: once a chosen lift has the prescribed quotient-model cocycle map,
the standing surjectivity-modulo-`I` hypothesis upgrades it to an actual surjection. -/
lemma surjective_of_quotient_model_cocycle_lift
    (PClass : ObjectProperty ModR)
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (hP : PClass P) (hZ : PClass Z)
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2)))
    (hacyclic : E.Acyclic)
    (q : P ⟶ Z)
    (hq :
      q.hom.quotientMapByIdeal I =
        ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R) :
    Function.Surjective q.hom := by
  -- Route correction: transport surjectivity through the fixed quotient-model isomorphisms first,
  -- then feed the resulting reduced surjectivity directly into the standing `hsurj` hypothesis.
  have hquot_model :
        Function.Surjective
        (((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R) := by
    simpa using
      surjective_to_next_cocycle_in_quotient_model (I := I) E n epq ezq hacyclic
  have hquot :
      Function.Surjective (q.hom.quotientMapByIdeal I) := by
    simpa [hq] using hquot_model
  have hred :
      Function.Surjective (((ReduceModI).map q).hom) := by
    have hiff :
        Function.Surjective (((ReduceModI).map q).hom) ↔
          Function.Surjective (q.hom.quotientMapByIdeal I) :=
      surjective_reduceModI_map_iff_quotientMapByIdeal (I := I) (P := P) (Z := Z) q
    exact hiff.2 hquot
  -- The module-class hypothesis upgrades surjectivity modulo `I` to actual surjectivity.
  exact hsurj (P₁ := P) (P₂ := Z) q hP hZ hred

/-- Helper for Lemma 15.76.1: after transporting degree `n` into a quotient model and the next
cocycle into a quotient model, the degree-`n` cocycle inclusion still lands in the kernel. -/
  lemma quotient_model_cocycle_inclusion_comp_zero
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2))) :
    kernel.ι (E.d n (n + 1)) ≫ epq.inv ≫
        (epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv) = 0 := by
  -- The quotient-model isomorphisms cancel, leaving the already proved cocycle-kernel relation.
  calc
    kernel.ι (E.d n (n + 1)) ≫ epq.inv ≫
        (epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv)
        = kernel.ι (E.d n (n + 1)) ≫ to_next_cocycle (I := I) E n ≫ ezq.inv := by
            simp [Category.assoc]
    _ = 0 := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ ezq.inv) (cocycle_to_next_cocycle_zero (I := I) E n)

/-- Helper for Lemma 15.76.1: the quotient-model representative of the cocycle map in degree
`n`. -/
abbrev quotient_model_to_next_cocycle_map
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2))) :
    ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ⟶
      ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) :=
  ModuleCat.ofHom ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom)

/-- Helper for Lemma 15.76.1: the previous cocycle object gives a concrete kernel fork for the
quotient-model cocycle map. -/
abbrev quotient_model_cocycle_kernel_fork
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2))) :
    KernelFork (quotient_model_to_next_cocycle_map (I := I) E n epq ezq) :=
  KernelFork.ofι
    (kernel.ι (E.d n (n + 1)) ≫ epq.inv)
    (by
      simpa [quotient_model_to_next_cocycle_map, Category.assoc] using
        quotient_model_cocycle_inclusion_comp_zero (I := I) E n epq ezq)

/-- Helper for Lemma 15.76.1: after transporting degree `n` into a quotient model, the source
kernel fork is still represented by `cocycle E n`. -/
def quotient_model_cocycle_kernel_fork_isLimit
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2))) :
    IsLimit (quotient_model_cocycle_kernel_fork (I := I) E n epq ezq) := by
  -- Route correction: compare the transported quotient-model map with the canonical cocycle
  -- kernel only once, so later descent steps can consume a named kernel comparison instead of
  -- repeating transport through `epq` and `ezq`.
  refine KernelFork.IsLimit.ofι'
    (kernel.ι (E.d n (n + 1)) ≫ epq.inv)
    (by
      simpa [quotient_model_cocycle_kernel_fork, quotient_model_to_next_cocycle_map,
        Category.assoc] using
        quotient_model_cocycle_inclusion_comp_zero (I := I) E n epq ezq)
    ?_
  intro W k hk
  have hk' : k ≫ epq.hom ≫ to_next_cocycle (I := I) E n = 0 := by
    -- Compose with `ezq.hom` to remove the target transport and return to the canonical cocycle
    -- map in the complex.
    simpa [quotient_model_to_next_cocycle_map, Category.assoc] using
      congrArg (fun t ↦ t ≫ ezq.hom) hk
  refine ⟨(cocycle_inclusion_is_kernel (I := I) E n).lift (KernelFork.ofι (k ≫ epq.hom) hk'),
    ?_⟩
  -- The universal morphism is determined after cancelling the source isomorphism `epq.hom`.
  apply (cancel_mono epq.hom).1
  calc
    (cocycle_inclusion_is_kernel (I := I) E n).lift (KernelFork.ofι (k ≫ epq.hom) hk') ≫
        kernel.ι (E.d n (n + 1)) ≫ epq.inv ≫ epq.hom
        =
      (cocycle_inclusion_is_kernel (I := I) E n).lift (KernelFork.ofι (k ≫ epq.hom) hk') ≫
        kernel.ι (E.d n (n + 1)) := by
          simp [Category.assoc]
    _ = k ≫ epq.hom := by
          simpa [Category.assoc] using
            (cocycle_inclusion_is_kernel (I := I) E n).fac
              (KernelFork.ofι (k ≫ epq.hom) hk')
              WalkingParallelPair.zero

/-- Helper for Lemma 15.76.1: the kernel of the quotient-model cocycle map is canonically the
previous cocycle object. -/
noncomputable def quotient_model_to_next_cocycle_kernel_iso
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2))) :
    kernel (quotient_model_to_next_cocycle_map (I := I) E n epq ezq) ≅
      kernel (E.d n (n + 1)) :=
  IsLimit.conePointUniqueUpToIso
    (kernelIsKernel (quotient_model_to_next_cocycle_map (I := I) E n epq ezq))
    (quotient_model_cocycle_kernel_fork_isLimit (I := I) E n epq ezq)

/-- Helper for Lemma 15.76.1: the quotient-model kernel comparison intertwines the kernel
inclusion with the cocycle inclusion. -/
lemma quotient_model_to_next_cocycle_kernel_iso_hom_comp
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2))) :
    kernel.ι (quotient_model_to_next_cocycle_map (I := I) E n epq ezq) ≫ epq.hom =
      (quotient_model_to_next_cocycle_kernel_iso (I := I) E n epq ezq).hom ≫
        kernel.ι (E.d n (n + 1)) := by
  -- The cone-point comparison is characterized by the kernel-fork leg, and composing with
  -- `epq.hom` removes the source transport.
  have hcomp :
      (quotient_model_to_next_cocycle_kernel_iso (I := I) E n epq ezq).hom ≫
          (quotient_model_cocycle_kernel_fork (I := I) E n epq ezq).ι =
        kernel.ι (quotient_model_to_next_cocycle_map (I := I) E n epq ezq) := by
    simpa [quotient_model_to_next_cocycle_kernel_iso, quotient_model_cocycle_kernel_fork] using
      IsLimit.conePointUniqueUpToIso_hom_comp
        (kernelIsKernel (quotient_model_to_next_cocycle_map (I := I) E n epq ezq))
        (quotient_model_cocycle_kernel_fork_isLimit (I := I) E n epq ezq)
        WalkingParallelPair.zero
  calc
    kernel.ι (quotient_model_to_next_cocycle_map (I := I) E n epq ezq) ≫ epq.hom =
      ((quotient_model_to_next_cocycle_kernel_iso (I := I) E n epq ezq).hom ≫
        (quotient_model_cocycle_kernel_fork (I := I) E n epq ezq).ι) ≫ epq.hom := by
          rw [hcomp]
    _ =
      (quotient_model_to_next_cocycle_kernel_iso (I := I) E n epq ezq).hom ≫
        kernel.ι (E.d n (n + 1)) := by
          simp [quotient_model_cocycle_kernel_fork, Category.assoc]

/-- Helper for Lemma 15.76.1: one step of the descending construction chooses a lift of the next
term, upgrades the quotient-side cocycle map to an actual split surjection, and records that its
kernel stays in `PClass`. -/
lemma exists_descent_step_of_lifted_cocycle
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (n : ℤ) {Z : ModR}
    (hZ : PClass Z)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2)))
    (hacyclic : E.Acyclic) :
    ∃ (P : ModR) (hP : PClass P)
      (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
      (q : P ⟶ Z) (s : Z ⟶ P),
      q.hom.comp s.hom = LinearMap.id ∧
      Function.Surjective q.hom ∧
      PClass (kernel q) ∧
      q.hom.quotientMapByIdeal I =
        ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R := by
  -- Choose a degree-`n` lift inside `PClass` from the termwise hypothesis on `E`.
  obtain ⟨P, hP, ⟨epq⟩⟩ := exists_term_lift_of_minusWithTermsIn (I := I) PClass E n
  -- Lift the quotient-side cocycle map to an actual `R`-linear morphism.
  obtain ⟨q, hq⟩ := exists_lift_to_next_cocycle_in_quotient_model
    (I := I) PClass hprojective E n hP epq ezq
  -- Upgrade surjectivity modulo `I` to actual surjectivity using the standing hypothesis.
  have hq_surj : Function.Surjective q.hom := by
    exact surjective_of_quotient_model_cocycle_lift
      (I := I) PClass hsurj E n hP hZ epq ezq hacyclic q hq
  -- The kernel remains in `PClass` because the surjection splits over the projective target.
  have hkernel : PClass (kernel q) := by
    exact module_class_of_kernel_of_surjective_to_projective
      PClass hprojective q hP hZ hq_surj
  letI : Projective Z := hprojective hZ
  letI : Epi q := (ModuleCat.epi_iff_surjective q).2 hq_surj
  let s : Z ⟶ P := Projective.factorThru (𝟙 Z) q
  have hs_cat : s ≫ q = 𝟙 Z := by
    -- The projective lift of the identity provides the splitting of `q`.
    simpa [s] using (Projective.factorThru_comp (𝟙 Z) q)
  have hs : q.hom.comp s.hom = LinearMap.id := by
    -- Read the categorical splitting on underlying linear maps.
    simpa using congrArg ModuleCat.Hom.hom hs_cat
  exact ⟨P, hP, epq, q, s, hs, hq_surj, hkernel, hq⟩

/-- Helper for Lemma 15.76.1: after one descent step, reducing the newly created kernel modulo
`I` first identifies the new categorical kernel with the quotient-model kernel of the descended
cocycle map. -/
noncomputable def descent_step_kernel_model_iso
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2)))
    (q : P ⟶ Z) (s : Z ⟶ P)
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hq :
      q.hom.quotientMapByIdeal I =
        ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R) :
    ((ReduceModI).obj (kernel q)) ≅
      kernel (quotient_model_to_next_cocycle_map (I := I) E n epq ezq) :=
  -- Normalize the reduced categorical kernel to the concrete quotient-kernel model once, so the
  -- later descending recursion can reuse this transport without reopening the quotient algebra.
  (ReduceModI.mapIso (ModuleCat.kernelIsoKer q)) ≪≫
    reduceModI_obj_iso_quotient (I := I) (ModuleCat.of R (LinearMap.ker q.hom)) ≪≫
      (linearEquiv_over_quotient (I := I)
        (kernel_quotient_equiv_of_split_reduction_general
          (I := I) q s
          ((quotient_model_to_next_cocycle_map (I := I) E n epq ezq).hom.restrictScalars R)
          hs
          hq)).toModuleIso ≪≫
        (ModuleCat.kernelIsoKer (quotient_model_to_next_cocycle_map (I := I) E n epq ezq)).symm

/-- Helper for Lemma 15.76.1: after one descent step, reducing the newly created kernel modulo
`I` recovers the previous cocycle object. -/
noncomputable def descent_step_kernel_reduction_iso
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2)))
    (q : P ⟶ Z) (s : Z ⟶ P)
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hq :
      q.hom.quotientMapByIdeal I =
        ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R) :
    ((ReduceModI).obj (kernel q)) ≅ cocycle (I := I) E n :=
  -- First pass through the quotient-model kernel, then use the previously isolated comparison
  -- from that kernel to the cocycle object in degree `n`.
  descent_step_kernel_model_iso (I := I) E n epq ezq q s hs hq ≪≫
    quotient_model_to_next_cocycle_kernel_iso (I := I) E n epq ezq

/-- Helper for Lemma 15.76.1: after one descent step, the reduced kernel comparison followed by
the cocycle inclusion is exactly the reduced kernel inclusion followed by the chosen quotient-model
identification of degree `n`. -/
lemma descent_step_kernel_reduction_iso_hom_comp
    (E : CpxRI) (n : ℤ) {P Z : ModR}
    (epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X n)
    (ezq : ModuleCat.of (R ⧸ I) (Z ⧸ (I • (⊤ : Submodule R Z))) ≅
      kernel (E.d (n + 1) (n + 2)))
    (q : P ⟶ Z) (s : Z ⟶ P)
    (hs : q.hom.comp s.hom = LinearMap.id)
    (hq :
      q.hom.quotientMapByIdeal I =
        ((epq.hom ≫ to_next_cocycle (I := I) E n ≫ ezq.inv).hom).restrictScalars R) :
    (descent_step_kernel_reduction_iso (I := I) E n epq ezq q s hs hq).hom ≫
        kernel.ι (E.d n (n + 1)) =
      ((ReduceModI).map (kernel.ι q)) ≫
        (reduceModI_obj_iso_quotient (I := I) P).hom ≫ epq.hom := by
  -- Route correction: factor the comparison through the quotient-model kernel once, so later
  -- tower-level differential identities do not reopen the categorical-kernel transport.
  calc
    (descent_step_kernel_reduction_iso (I := I) E n epq ezq q s hs hq).hom ≫
        kernel.ι (E.d n (n + 1)) =
      (descent_step_kernel_model_iso (I := I) E n epq ezq q s hs hq).hom ≫
        kernel.ι (quotient_model_to_next_cocycle_map (I := I) E n epq ezq) ≫ epq.hom := by
          simp [descent_step_kernel_reduction_iso, Category.assoc,
            quotient_model_to_next_cocycle_kernel_iso_hom_comp]
    _ =
      ((ReduceModI).map (kernel.ι q)) ≫
        (reduceModI_obj_iso_quotient (I := I) P).hom ≫ epq.hom := by
          -- Unfold the model isomorphism once and use the explicit split-kernel quotient formula.
          ext x
          change
            (epq.hom.hom
              ((kernel.ι
                (quotient_model_to_next_cocycle_map (I := I) E n epq ezq)).hom
                (((descent_step_kernel_model_iso (I := I) E n epq ezq q s hs hq).hom).hom x))) =
              (epq.hom.hom
                (((reduceModI_obj_iso_quotient (I := I) P).hom).hom
                  (((ReduceModI).map (kernel.ι q)).hom x)))
          congr 1
          -- The two quotient-model classes are equal already before applying `epq`.
          -- This is the point where the split-kernel quotient formula replaces the heavy kernel
          -- transport by the ambient quotient class of the kernel representative.
          simp [descent_step_kernel_model_iso, Category.assoc,
            split_reduction_kernel_map_general_mkQ, reduceModI_obj_iso_quotient_naturality]

/-- Helper for Lemma 15.76.1: one source-faithful descent stage at degree `b - m`, storing the
chosen lift `P^(b-m)`, the next cocycle lift `Z^(b-m+1)`, and the split surjection between them.
-/
private structure CocycleLiftStage
    (PClass : ObjectProperty ModR) (b : ℤ) (E : CpxRI) (m : ℕ) where
  P : ModR
  hP : PClass P
  epq : ModuleCat.of (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) ≅ E.X (b - Int.ofNat m)
  Zsucc : ModR
  hZsucc : PClass Zsucc
  ezq :
    ModuleCat.of (R ⧸ I) (Zsucc ⧸ (I • (⊤ : Submodule R Zsucc))) ≅
      cocycle (I := I) E (b + 1 - Int.ofNat m)
  q : P ⟶ Zsucc
  s : Zsucc ⟶ P
  hs : q.hom.comp s.hom = LinearMap.id
  hq_surj : Function.Surjective q.hom
  hkernel : PClass (kernel q)
  hq :
    q.hom.quotientMapByIdeal I =
      ((epq.hom ≫ to_next_cocycle (I := I) E (b - Int.ofNat m) ≫ ezq.inv).hom).restrictScalars R

namespace CocycleLiftStage

variable {PClass : ObjectProperty ModR} {b : ℤ} {E : CpxRI} {m : ℕ}

/-- Helper for Lemma 15.76.1: the kernel created by one descent stage reduces to the previous
cocycle object. -/
private noncomputable def kernel_ezq
    (S : CocycleLiftStage (I := I) PClass b E m) :
    ModuleCat.of (R ⧸ I) ((kernel S.q) ⧸ (I • (⊤ : Submodule R (kernel S.q)))) ≅
      cocycle (I := I) E (b - Int.ofNat m) :=
  (reduceModI_obj_iso_quotient (I := I) (kernel S.q)).symm ≪≫
    descent_step_kernel_reduction_iso (I := I) E (b - Int.ofNat m) S.epq S.ezq S.q S.s S.hs S.hq

/-- Helper for Lemma 15.76.1: the reduced kernel comparison of a stage intertwines the kernel
inclusion with the quotient-model cocycle inclusion in the previous degree. -/
private lemma kernel_ezq_hom_comp
    (S : CocycleLiftStage (I := I) PClass b E m) :
    (kernel_ezq (I := I) S).hom ≫ kernel.ι (E.d (b - Int.ofNat m) (b - Int.ofNat m + 1)) =
      ((ReduceModI).map (kernel.ι S.q)) ≫
        (reduceModI_obj_iso_quotient (I := I) S.P).hom ≫ S.epq.hom := by
  -- Proof comment: this is exactly the one-step compatibility already proved for the descended
  -- kernel, merely repackaged through the stage record.
  simpa [kernel_ezq, cocycle] using
    descent_step_kernel_reduction_iso_hom_comp
      (I := I) E (b - Int.ofNat m) S.epq S.ezq S.q S.s S.hs S.hq

end CocycleLiftStage

/-- Helper for Lemma 15.76.1: the recursive stage index satisfies
`b - (m + 1) + 1 = b - m`. -/
private lemma cocycle_lift_stage_degree_succ (b : ℤ) (m : ℕ) :
    b - Int.ofNat (m + 1) + 1 = b - Int.ofNat m := by
  -- Proof comment: this is the degree shift used when the source proof descends from `n` to
  -- `n - 1`.
  have hm : Int.ofNat (m + 1) = Int.ofNat m + 1 := by
    simp
  rw [hm]
  omega

/-- Helper for Lemma 15.76.1: the successor cocycle degree satisfies
`b + 1 - (m + 1) = b - m`. -/
private lemma cocycle_lift_stage_cocycle_degree_succ (b : ℤ) (m : ℕ) :
    b + 1 - Int.ofNat (m + 1) = b - Int.ofNat m := by
  -- Proof comment: this is the cocycle-degree rewrite matching the source inductive step.
  have hm : Int.ofNat (m + 1) = Int.ofNat m + 1 := by
    simp
  rw [hm]
  omega

/-- Helper for Lemma 15.76.1: the initial stage at the top nonzero degree of `E`, obtained by
descending once from the zero cocycle above the cutoff. -/
private theorem cocycle_lift_stage_zero
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : E.Acyclic)
    (b : ℤ) (hb : E.IsStrictlyLE b) :
    CocycleLiftStage (I := I) PClass b E 0 := by
  have hzeroClass : PClass (zero_module (R := R)) := by
    -- Proof comment: the source base case starts from the zero object above the cutoff.
    exact module_class_zero_of_reduced_term (I := I) PClass (E.term_mem b)
  let ezq0 :
      ModuleCat.of (R ⧸ I)
          ((zero_module (R := R)) ⧸
            (I • (⊤ : Submodule R (zero_module (R := R))))) ≅
        cocycle (I := I) E (b + 1) :=
    (reduceModI_obj_iso_quotient (I := I) (zero_module (R := R))).symm ≪≫
      cocycle_succ_iso_zero_of_isStrictlyLE (I := I) (E := E) hb
  -- Proof comment: the first stage is exactly the one-step descent from the zero cocycle lift.
  obtain ⟨P, hP, epq, q, s, hs, hq_surj, hkernel, hq⟩ :=
    exists_descent_step_of_lifted_cocycle
      (I := I) PClass hprojective hsurj (E := E) b hzeroClass ezq0 hacyclic
  exact
    { P := P
      hP := hP
      epq := by simpa using epq
      Zsucc := zero_module (R := R)
      hZsucc := hzeroClass
      ezq := by simpa using ezq0
      q := q
      s := s
      hs := hs
      hq_surj := hq_surj
      hkernel := hkernel
      hq := by simpa using hq }

/-- Helper for Lemma 15.76.1: the successor stage in the downward induction, obtained by applying
one more descent step to the kernel produced by the previous stage. -/
private theorem cocycle_lift_stage_succ
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : E.Acyclic)
    (b : ℤ) (m : ℕ)
    (S : CocycleLiftStage (I := I) PClass b E m) :
    CocycleLiftStage (I := I) PClass b E (m + 1) := by
  let ezqPrev :
      ModuleCat.of (R ⧸ I) ((kernel S.q) ⧸ (I • (⊤ : Submodule R (kernel S.q)))) ≅
        cocycle (I := I) E (b - Int.ofNat m) :=
    CocycleLiftStage.kernel_ezq (I := I) S
  have ezqStep :
      ModuleCat.of (R ⧸ I) ((kernel S.q) ⧸ (I • (⊤ : Submodule R (kernel S.q)))) ≅
        kernel (E.d (b - Int.ofNat (m + 1) + 1) (b - Int.ofNat (m + 1) + 2)) := by
    -- Proof comment: rewrite the stage indices so the previous kernel becomes the next cocycle
    -- input for the new descent step.
    simpa [cocycle, cocycle_lift_stage_degree_succ (b := b) (m := m)] using ezqPrev
  -- Proof comment: the source induction step chooses the next lifted term surjecting onto that
  -- newly produced kernel.
  obtain ⟨P, hP, epq, q, s, hs, hq_surj, hkernel, hq⟩ :=
    exists_descent_step_of_lifted_cocycle
      (I := I) PClass hprojective hsurj (E := E)
      (b - Int.ofNat (m + 1)) S.hkernel ezqStep hacyclic
  exact
    { P := P
      hP := hP
      epq := epq
      Zsucc := kernel S.q
      hZsucc := S.hkernel
      ezq := by
        simpa [cocycle_lift_stage_cocycle_degree_succ (b := b) (m := m)] using ezqPrev
      q := q
      s := s
      hs := hs
      hq_surj := hq_surj
      hkernel := hkernel
      hq := hq }

/-- Helper for Lemma 15.76.1: the full downward recursion of source-faithful cocycle lifts,
starting above the top nonzero degree and descending one kernel step at a time. -/
private noncomputable def cocycle_lift_stage
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : E.Acyclic)
    (b : ℤ) (hb : E.IsStrictlyLE b) :
    ∀ m : ℕ, CocycleLiftStage (I := I) PClass b E m
  | 0 => cocycle_lift_stage_zero (I := I) PClass hprojective hsurj E hacyclic b hb
  | m + 1 =>
      cocycle_lift_stage_succ (I := I) PClass hprojective hsurj E hacyclic b m
        (cocycle_lift_stage PClass hprojective hsurj E hacyclic b hb m)

/-- Helper for Lemma 15.76.1: if the supported stage index at degree `i` is zero, then `i` is
the top cutoff degree `b`. -/
private lemma cocycle_lift_complex_index_eq_top
    (b i : ℤ) (hi : i ≤ b)
    (hidx : Int.toNat (b - i) = 0) :
    i = b := by
  -- Proof comment: on the supported range `i ≤ b`, the only way the distance `b - i` has
  -- zero natural size is that the distance itself is zero.
  have hidx' : ((Int.toNat (b - i) : ℤ)) = 0 := by
    exact_mod_cast hidx
  rw [Int.toNat_of_nonneg (by omega)] at hidx'
  omega

/-- Helper for Lemma 15.76.1: when the supported stage index at degree `i` is `m + 1`, the next
degree still lies below the cutoff and corresponds to stage `m`. -/
private lemma cocycle_lift_complex_target_index
    (b i : ℤ) (m : ℕ)
    (hidx : Int.toNat (b - i) = m + 1) :
    i + 1 ≤ b ∧ Int.toNat (b - (i + 1)) = m := by
  -- Proof comment: rewrite the supported indices as ordinary integer differences and solve the
  -- resulting arithmetic in one step.
  have hidx' : ((Int.toNat (b - i) : ℤ)) = m + 1 := by
    exact_mod_cast hidx
  rw [Int.toNat_of_nonneg (by omega)] at hidx'
  constructor
  · omega
  · have htarget' : ((Int.toNat (b - (i + 1)) : ℤ)) = m := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    exact_mod_cast htarget'

/-- Helper for Lemma 15.76.1: the extracted raw lift has term `P^(b-m)` equal to the `m`-th
stored stage module, and vanishes above the cutoff. -/
private noncomputable def cocycle_lift_complex_X
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) (i : ℤ) :
    ModR :=
  let S := cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb
  if hi : i ≤ b then (S (Int.toNat (b - i))).P else zero_module (R := R)

/-- Helper for Lemma 15.76.1: on a supported degree `i ≤ b`, the extracted source object really
is the chosen stage module indexed by `Int.toNat (b - i)`. -/
private lemma cocycle_lift_complex_X_eq_stage
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b)
    (i : ℤ) (hi : i ≤ b) (m : ℕ)
    (hidx : Int.toNat (b - i) = m) :
    cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb i =
      (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).P := by
  -- Proof comment: after fixing `i ≤ b`, the `if`-branch and the stage index both normalize
  -- directly.
  unfold cocycle_lift_complex_X
  simp [hi, hidx]

/-- Helper for Lemma 15.76.1: in the interior supported range, the next extracted object is the
preceding stage module. -/
private lemma cocycle_lift_complex_X_next_eq_stage
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b)
    (i : ℤ) (m : ℕ)
    (hidx : Int.toNat (b - i) = m + 1) :
    cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb (i + 1) =
      (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).P := by
  -- Proof comment: the previous arithmetic lemma turns the successor degree into the previous
  -- stage index, and the term formula is then immediate.
  rcases cocycle_lift_complex_target_index (b := b) (i := i) (m := m) hidx with ⟨hnext, htarget⟩
  unfold cocycle_lift_complex_X
  simp [hnext, htarget]

/-- Helper for Lemma 15.76.1: when the supported stage index is zero, the next extracted term is
already the zero module above the cutoff. -/
private lemma cocycle_lift_complex_X_next_eq_zero
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b)
    (i : ℤ) (hi : i ≤ b)
    (hidx : Int.toNat (b - i) = 0) :
    cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb (i + 1) =
      zero_module (R := R) := by
  -- Proof comment: `Int.toNat (b - i) = 0` forces `i = b`, so the next degree is strictly above
  -- the cutoff and therefore vanishes.
  have htop : i = b :=
    cocycle_lift_complex_index_eq_top (b := b) (i := i) hi hidx
  subst htop
  unfold cocycle_lift_complex_X
  simp

/-- Helper for Lemma 15.76.1: the extracted differential is the stage surjection followed by the
previous kernel inclusion on supported interior degrees, the top stage surjection at degree `b`,
and zero above the cutoff. -/
private noncomputable def cocycle_lift_complex_d
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) (i : ℤ) :
    cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb i ⟶
      cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb (i + 1) :=
  let S := cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb
  if hi : i ≤ b then
    match hidx : Int.toNat (b - i) with
    | 0 =>
        (eqToHom
            (cocycle_lift_complex_X_eq_stage
              (I := I) PClass hprojective hsurj E hacyclic b hb i hi 0 hidx)) ≫
          (S 0).q ≫
          eqToHom
            (cocycle_lift_complex_X_next_eq_zero
              (I := I) PClass hprojective hsurj E hacyclic b hb i hi hidx).symm
    | m + 1 =>
        if hnext : i + 1 ≤ b then
          (eqToHom
              (cocycle_lift_complex_X_eq_stage
                (I := I) PClass hprojective hsurj E hacyclic b hb i hi (m + 1) hidx)) ≫
            (S (m + 1)).q ≫
            kernel.ι (S m).q ≫
            eqToHom
              (cocycle_lift_complex_X_next_eq_stage
                (I := I) PClass hprojective hsurj E hacyclic b hb i m hidx).symm
        else
          0
  else
    0

/-- Helper for Lemma 15.76.1: successive extracted differentials compose to zero, because each
interior composite factors through a kernel inclusion and all unsupported branches are zero. -/
private lemma cocycle_lift_complex_d_top
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b)
    (i : ℤ) (hi : i ≤ b)
    (hidx : Int.toNat (b - i) = 0) :
    cocycle_lift_complex_d (I := I) PClass hprojective hsurj E hacyclic b hb i =
      (eqToHom
          (cocycle_lift_complex_X_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb i hi 0 hidx)) ≫
        (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb 0).q ≫
        eqToHom
          (cocycle_lift_complex_X_next_eq_zero
            (I := I) PClass hprojective hsurj E hacyclic b hb i hi hidx).symm := by
  -- Proof comment: the zero-stage branch of `cocycle_lift_complex_d` is definitionally the top
  -- differential of the extracted complex.
  unfold cocycle_lift_complex_d
  simp [hi, hidx]

/-- Helper for Lemma 15.76.1: on a supported interior degree, the extracted differential is the
stage surjection followed by the previous kernel inclusion. -/
private lemma cocycle_lift_complex_d_supported
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b)
    (i : ℤ) (m : ℕ)
    (hi : i ≤ b)
    (hidx : Int.toNat (b - i) = m + 1) :
    cocycle_lift_complex_d (I := I) PClass hprojective hsurj E hacyclic b hb i =
      (eqToHom
          (cocycle_lift_complex_X_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb i hi (m + 1) hidx)) ≫
        (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb (m + 1)).q ≫
        kernel.ι ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).q) ≫
        eqToHom
          (cocycle_lift_complex_X_next_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb i m hidx).symm := by
  rcases cocycle_lift_complex_target_index (b := b) (i := i) (m := m) hidx with ⟨hnext, htarget⟩
  -- Proof comment: the supported interior branch is already the desired normalized expression
  -- once the successor index is rewritten to stage `m`.
  unfold cocycle_lift_complex_d
  simp [hi, hidx, hnext, htarget]

/-- Helper for Lemma 15.76.1: above the cutoff `b`, the extracted differential vanishes. -/
private lemma cocycle_lift_complex_d_above
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b)
    (i : ℤ) (hbi : b < i) :
    cocycle_lift_complex_d (I := I) PClass hprojective hsurj E hacyclic b hb i = 0 := by
  -- Proof comment: once `i` lies above `b`, the outer `if` in the definition takes the
  -- unsupported zero branch.
  unfold cocycle_lift_complex_d
  simp [hbi.not_ge]

/-- Helper for Lemma 15.76.1: successive extracted differentials compose to zero, because each
interior composite factors through a kernel inclusion and all unsupported branches are zero. -/
private theorem cocycle_lift_complex_d_sq
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) (i : ℤ) :
    cocycle_lift_complex_d (I := I) PClass hprojective hsurj E hacyclic b hb i ≫
      cocycle_lift_complex_d (I := I) PClass hprojective hsurj E hacyclic b hb (i + 1) = 0 := by
  by_cases hi : i ≤ b
  · by_cases hzero : Int.toNat (b - i) = 0
    · -- Proof comment: at the top supported degree, the first differential is the top-stage
      -- surjection and the second differential is already zero above the cutoff.
      rw [cocycle_lift_complex_d_top
        (I := I) PClass hprojective hsurj E hacyclic b hb i hi hzero]
      have htop : i = b :=
        cocycle_lift_complex_index_eq_top (b := b) (i := i) hi hzero
      have habove : b < i + 1 := by
        omega
      rw [cocycle_lift_complex_d_above
        (I := I) PClass hprojective hsurj E hacyclic b hb (i := i + 1) habove]
      simp
    · obtain ⟨m, hidx⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      -- Proof comment: on interior supported degrees, normalize both differentials to stage maps
      -- and then the composition vanishes through the kernel inclusion.
      rw [cocycle_lift_complex_d_supported
        (I := I) PClass hprojective hsurj E hacyclic b hb i m hi hidx]
      rcases cocycle_lift_complex_target_index (b := b) (i := i) (m := m) hidx with
        ⟨hnext, htarget⟩
      cases m with
      | zero =>
          rw [cocycle_lift_complex_d_top
            (I := I) PClass hprojective hsurj E hacyclic b hb (i := i + 1) hnext htarget]
          simp [Category.assoc]
      | succ k =>
          rw [cocycle_lift_complex_d_supported
            (I := I) PClass hprojective hsurj E hacyclic b hb (i := i + 1) k hnext htarget]
          simp [Category.assoc]
  · -- Proof comment: once `i` is above the cutoff, both successive differentials are already
    -- zero by the unsupported branch of the definition.
    have hbi : b < i := lt_of_not_ge hi
    have hbi' : b < i + 1 := by
      omega
    rw [cocycle_lift_complex_d_above
      (I := I) PClass hprojective hsurj E hacyclic b hb i hbi]
    rw [cocycle_lift_complex_d_above
      (I := I) PClass hprojective hsurj E hacyclic b hb (i := i + 1) hbi']
    simp

/-- Helper for Lemma 15.76.1: the recursive stage family assembles into one raw bounded-above
cochain complex over `R`. -/
private noncomputable def cocycle_lift_complex
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) :
    CpxR :=
  CochainComplex.of
    (cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb)
    (cocycle_lift_complex_d (I := I) PClass hprojective hsurj E hacyclic b hb)
    (cocycle_lift_complex_d_sq (I := I) PClass hprojective hsurj E hacyclic b hb)

/-- Helper for Lemma 15.76.1: in degree `b - m`, the extracted complex has term exactly the
`m`-th stored stage module. -/
private lemma cocycle_lift_complex_X_supported
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) (m : ℕ) :
    (cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb).X
        (b - Int.ofNat m) =
      (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).P := by
  -- Proof comment: avoid unfolding the whole recursion; only rewrite the extracted `X`-formula
  -- at the supported degree `b - m`.
  change
    cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb
      (b - Int.ofNat m) =
      (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).P
  have hi : b - Int.ofNat m ≤ b := by
    have hm_nonneg : (0 : ℤ) ≤ Int.ofNat m := by
      exact_mod_cast Nat.zero_le m
    omega
  have hidx : Int.toNat (b - (b - Int.ofNat m)) = m := by
    have hrewrite : b - (b - Int.ofNat m) = Int.ofNat m := by
      omega
    rw [hrewrite]
    simpa using Int.toNat_of_nonneg (show (0 : ℤ) ≤ Int.ofNat m by exact_mod_cast Nat.zero_le m)
  exact
    cocycle_lift_complex_X_eq_stage
      (I := I) PClass hprojective hsurj E hacyclic b hb
      (b - Int.ofNat m) hi m hidx

/-- Helper for Lemma 15.76.1: above the cutoff `b`, every term of the extracted complex is zero. -/
private lemma cocycle_lift_complex_X_above
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) {i : ℤ}
    (hbi : b < i) :
    (cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb).X i =
      zero_module (R := R) := by
  -- Proof comment: above the cutoff, the extracted `X`-formula takes the unsupported branch.
  change
    cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb i =
      zero_module (R := R)
  simp [cocycle_lift_complex_X, hbi.not_ge]

/-- Helper for Lemma 15.76.1: the extracted complex is bounded above by the same cutoff `b` as
the reduced complex. -/
private lemma cocycle_lift_complex_isStrictlyLE
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) :
    (cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb).IsStrictlyLE b := by
  -- Proof comment: all degrees strictly above `b` are zero by the explicit term formula.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [cocycle_lift_complex_X_above (I := I) PClass hprojective hsurj E hacyclic b hb hi]
  exact ModuleCat.isZero_of_subsingleton (zero_module (R := R))

/-- Helper for Lemma 15.76.1: every term of the extracted complex still lies in `PClass`. -/
private lemma cocycle_lift_complex_term_mem
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) (i : ℤ) :
    PClass ((cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb).X i) := by
  change
    PClass (cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb i)
  by_cases hi : i ≤ b
  · -- Proof comment: on supported degrees the term is literally the corresponding stage module.
    let m : ℕ := Int.toNat (b - i)
    have hX :
        cocycle_lift_complex_X (I := I) PClass hprojective hsurj E hacyclic b hb i =
          (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).P := by
      exact
        cocycle_lift_complex_X_eq_stage
          (I := I) PClass hprojective hsurj E hacyclic b hb i hi m rfl
    rw [hX]
    exact (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).hP
  · -- Proof comment: above the cutoff the extracted term is the zero module, which belongs to
    -- `PClass` because the reduced complex has some term coming from `PClass`.
    simp [cocycle_lift_complex_X, hi]
    exact module_class_zero_of_reduced_term (I := I) PClass (E.term_mem b)

/-- Helper for Lemma 15.76.1: the normalized top supported short complex
`P^(b-1) → P^b → 0` is exact because the incoming stage map surjects onto the top kernel. -/
private lemma cocycle_lift_stage_shortComplex_exact_top
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b)
    (hzero :
      ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb 1).q ≫
        kernel.ι ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb 0).q)) ≫
          (cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb 0).q = 0) :
    (ShortComplex.mk
      ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb 1).q ≫
        kernel.ι ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb 0).q))
      ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb 0).q)
      hzero).Exact := by
  let S := cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb
  -- Proof comment: exactness here is the source proof's first surjectivity statement:
  -- every top-degree cycle in `P^b` already comes from the previous lifted term `P^(b-1)`.
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hxker : (S 0).q.hom x = 0 := by
    simpa using hx
  let xker : kernel (S 0).q := ⟨x, hxker⟩
  obtain ⟨y, hy⟩ := (S 1).hq_surj xker
  refine ⟨y, ?_⟩
  -- Proof comment: the chosen preimage in `kernel (S 0).q` becomes a preimage in `P^b`
  -- after forgetting the kernel subtype.
  change ((S 1).q.hom y).1 = x
  simpa using congrArg Subtype.val hy

/-- Helper for Lemma 15.76.1: the normalized interior short complex
`P^(b-m-1) → P^(b-m) → P^(b-m+1)` is exact because each stage surjects onto the previous kernel.
-/
private lemma cocycle_lift_stage_shortComplex_exact_succ
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) (m : ℕ)
    (hzero :
      ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb (m + 2)).q ≫
        kernel.ι
          ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb (m + 1)).q)) ≫
            ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb (m + 1)).q ≫
              kernel.ι
                ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).q)) = 0) :
    (ShortComplex.mk
      ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb (m + 2)).q ≫
        kernel.ι
          ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb (m + 1)).q))
      ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb (m + 1)).q ≫
        kernel.ι
          ((cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb m).q))
      hzero).Exact := by
  let S := cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb
  -- Proof comment: in the interior, the outgoing differential factors through the kernel
  -- inclusion of `(S (m + 1)).q`, so every element killed by it is already a lifted cocycle.
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hxval : ((S (m + 1)).q.hom x).1 = 0 := by
    simpa [Category.assoc] using hx
  have hxker : (S (m + 1)).q.hom x = 0 := by
    apply Subtype.ext
    simpa using hxval
  let xker : kernel (S (m + 1)).q := ⟨x, hxker⟩
  obtain ⟨y, hy⟩ := (S (m + 2)).hq_surj xker
  refine ⟨y, ?_⟩
  -- Proof comment: surjectivity onto `kernel (S (m + 1)).q` identifies the incoming range
  -- with the required kernel at the middle term.
  change ((S (m + 2)).q.hom y).1 = x
  simpa using congrArg Subtype.val hy

/-- Helper for Lemma 15.76.1: at each supported degree `b - m`, the extracted complex is exact
after rewriting to the concrete stage short complex coming from the source descent construction. -/
private lemma cocycle_lift_complex_exactAt_supported
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) (m : ℕ) :
    (cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb).ExactAt
      (b - Int.ofNat m) := by
  let K := cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb
  let S := cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb
  cases m with
  | zero =>
      have hprev : (up ℤ).prev b = b - 1 := by
        simpa using (CochainComplex.prev ℤ b)
      have hnext : (up ℤ).next b = b + 1 := by
        simpa [add_assoc] using (CochainComplex.next ℤ b)
      rw [HomologicalComplex.exactAt_iff' (K := K) (i := b - 1) (j := b) (k := b + 1) hprev hnext]
      have hzero :
          ((S 1).q ≫ kernel.ι (S 0).q) ≫ (S 0).q = 0 := by
        simp [Category.assoc]
      let T : ShortComplex ModR :=
        ShortComplex.mk ((S 1).q ≫ kernel.ι (S 0).q) (S 0).q hzero
      have hi_prev : b - 1 ≤ b := by
        omega
      have hidx_prev : Int.toNat (b - (b - 1)) = 0 + 1 := by
        norm_num
      have hi_top : b ≤ b := le_rfl
      have hidx_top : Int.toNat (b - b) = 0 := by
        simp
      have hX₁ :
          K.X (b - 1) = (S 1).P := by
        simpa [K, S] using
          cocycle_lift_complex_X_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb (b - 1) hi_prev 1 hidx_prev
      have hX₂ :
          K.X b = (S 0).P := by
        simpa [K, S] using
          cocycle_lift_complex_X_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb b hi_top 0 hidx_top
      have hX₃ :
          K.X (b + 1) = zero_module (R := R) := by
        simpa [K, S] using
          cocycle_lift_complex_X_next_eq_zero
            (I := I) PClass hprojective hsurj E hacyclic b hb b hi_top hidx_top
      refine ShortComplex.exact_of_iso ?_ ?_
      · refine ShortComplex.isoMk (eqToIso hX₁.symm) (eqToIso hX₂.symm) (eqToIso hX₃.symm) ?_ ?_
        · -- Proof comment: the incoming differential at the top degree is exactly the
          -- normalized stage map `P^(b-1) → P^b`.
          rw [cocycle_lift_complex_d_supported
            (I := I) PClass hprojective hsurj E hacyclic b hb (i := b - 1) (m := 0)
            hi_prev hidx_prev]
          simp [K, Category.assoc]
        · -- Proof comment: the outgoing differential at the cutoff degree is exactly the
          -- top-stage surjection `P^b → 0`.
          rw [cocycle_lift_complex_d_top
            (I := I) PClass hprojective hsurj E hacyclic b hb (i := b) hi_top hidx_top]
          simp [K, Category.assoc]
      · simpa [T, S] using
          cocycle_lift_stage_shortComplex_exact_top
            (I := I) PClass hprojective hsurj E hacyclic b hb hzero
  | succ m =>
      have hprev : (up ℤ).prev (b - Int.ofNat (m + 1)) = b - Int.ofNat (m + 2) := by
        simp
      have hnext : (up ℤ).next (b - Int.ofNat (m + 1)) = b - Int.ofNat m := by
        have hm : (b - Int.ofNat (m + 1)) + 1 = b - Int.ofNat m := by
          omega
        simpa [hm, add_assoc] using (CochainComplex.next ℤ (b - Int.ofNat (m + 1)))
      rw [HomologicalComplex.exactAt_iff'
        (K := K)
        (i := b - Int.ofNat (m + 2))
        (j := b - Int.ofNat (m + 1))
        (k := b - Int.ofNat m)
        hprev hnext]
      have hzero :
          ((S (m + 2)).q ≫ kernel.ι (S (m + 1)).q) ≫
              ((S (m + 1)).q ≫ kernel.ι (S m).q) = 0 := by
        simp [Category.assoc]
      let T : ShortComplex ModR :=
        ShortComplex.mk
          ((S (m + 2)).q ≫ kernel.ι (S (m + 1)).q)
          ((S (m + 1)).q ≫ kernel.ι (S m).q)
          hzero
      have hi_prev : b - Int.ofNat (m + 2) ≤ b := by
        omega
      have hi_curr : b - Int.ofNat (m + 1) ≤ b := by
        omega
      have hi_next : b - Int.ofNat m ≤ b := by
        omega
      have hidx_prev : Int.toNat (b - (b - Int.ofNat (m + 2))) = (m + 1) + 1 := by
        rw [show b - (b - Int.ofNat (m + 2)) = Int.ofNat (m + 2) by omega]
        simp [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc]
      have hidx_curr : Int.toNat (b - (b - Int.ofNat (m + 1))) = m + 1 := by
        rw [show b - (b - Int.ofNat (m + 1)) = Int.ofNat (m + 1) by omega]
        simp [Nat.succ_eq_add_one]
      have hX₁ :
          K.X (b - Int.ofNat (m + 2)) = (S (m + 2)).P := by
        simpa [K, S] using
          cocycle_lift_complex_X_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb
            (b - Int.ofNat (m + 2)) hi_prev (m + 2)
            (by
              rw [show b - (b - Int.ofNat (m + 2)) = Int.ofNat (m + 2) by omega]
              simp)
      have hX₂ :
          K.X (b - Int.ofNat (m + 1)) = (S (m + 1)).P := by
        simpa [K, S] using
          cocycle_lift_complex_X_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb
            (b - Int.ofNat (m + 1)) hi_curr (m + 1)
            (by
              rw [show b - (b - Int.ofNat (m + 1)) = Int.ofNat (m + 1) by omega]
              simp)
      have hX₃ :
          K.X (b - Int.ofNat m) = (S m).P := by
        simpa [K, S] using
          cocycle_lift_complex_X_eq_stage
            (I := I) PClass hprojective hsurj E hacyclic b hb
            (b - Int.ofNat m) hi_next m
            (by
              rw [show b - (b - Int.ofNat m) = Int.ofNat m by omega]
              simp)
      refine ShortComplex.exact_of_iso ?_ ?_
      · refine ShortComplex.isoMk (eqToIso hX₁.symm) (eqToIso hX₂.symm) (eqToIso hX₃.symm) ?_ ?_
        · -- Proof comment: the incoming supported differential is the stage map into the
          -- previous kernel inclusion.
          rw [cocycle_lift_complex_d_supported
            (I := I) PClass hprojective hsurj E hacyclic b hb
            (i := b - Int.ofNat (m + 2)) (m := m + 1) hi_prev hidx_prev]
          simp [K, Category.assoc]
        · -- Proof comment: the outgoing supported differential is the next stage map into the
          -- earlier kernel inclusion.
          rw [cocycle_lift_complex_d_supported
            (I := I) PClass hprojective hsurj E hacyclic b hb
            (i := b - Int.ofNat (m + 1)) (m := m) hi_curr hidx_curr]
          simp [K, Category.assoc]
      · simpa [T, S] using
          cocycle_lift_stage_shortComplex_exact_succ
            (I := I) PClass hprojective hsurj E hacyclic b hb m hzero

/-- Helper for Lemma 15.76.1: the extracted raw complex reduces to the given complex `E`
degreewise via the stored stage isomorphisms. -/
private noncomputable def cocycle_lift_complex_reduction_iso
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) :
    ((ReduceModI).mapHomologicalComplex (up ℤ)).obj
        (cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb) ≅
      (E : CpxRI) := by
  -- TODO: define the degreewise components by `(S m).epq` on supported degrees and the zero
  -- object isomorphism above `b`, then verify the differential squares using
  -- `CocycleLiftStage.kernel_ezq_hom_comp` and the explicit degree formulas of
  -- `cocycle_lift_complex_d`.
  sorry

/-- Helper for Lemma 15.76.1: the extracted raw complex is acyclic, because each incoming stage
surjection maps onto the kernel of the outgoing stage differential. -/
private lemma cocycle_lift_complex_acyclic
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic)
    (b : ℤ) (hb : (E : CpxRI).IsStrictlyLE b) :
    (cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb).Acyclic := by
  -- Proof comment: exactness below the cutoff is the supported stage exactness proved above,
  -- and exactness above the cutoff is trivial because the middle term is already zero.
  rw [HomologicalComplex.acyclic_iff]
  intro i
  by_cases hi : i ≤ b
  · let m : ℕ := Int.toNat (b - i)
    have hm : i = b - Int.ofNat m := by
      dsimp [m]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [hm]
    exact
      cocycle_lift_complex_exactAt_supported
        (I := I) PClass hprojective hsurj E hacyclic b hb m
  · have hbi : b < i := lt_of_not_ge hi
    rw [HomologicalComplex.exactAt_iff]
    have hXi :
        IsZero ((cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb).X i) := by
      rw [cocycle_lift_complex_X_above (I := I) PClass hprojective hsurj E hacyclic b hb hbi]
      exact ModuleCat.isZero_of_subsingleton (zero_module (R := R))
    exact ShortComplex.exact_of_isZero_X₂ hXi

/-- Lemma 15.76.1: under the stated projectivity, retract-stability (equivalently, direct-summand
closure in the module category), and surjectivity-modulo-`I` hypotheses on a class `PClass` of
`R`-modules, every bounded-above acyclic complex of
`(R ⧸ I)`-modules whose terms are reductions of objects of `PClass` lifts to a bounded-above
acyclic complex of `R`-modules with terms in `PClass`. -/
theorem exists_boundedAbove_acyclic_lift_of_module_class
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic) :
    ∃ (P : CochainComplex.MinusWithTermsIn PClass)
      (e :
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex (up ℤ)).obj
          (P : CpxR) ≅ (E : CpxRI)),
      (P : CpxR).Acyclic := by
  -- Route correction: the file now exposes the cycle-kernel half of the source proof explicitly,
  -- so the remaining work is the descending surjective lift and the final assembly.
  classical
  obtain ⟨b, hb⟩ := E.exists_isStrictlyLE
  let S : ∀ m : ℕ, CocycleLiftStage (I := I) PClass b (E : CpxRI) m :=
    cocycle_lift_stage (I := I) PClass hprojective hsurj E hacyclic b hb
  have hstage0_kernel :
      PClass (kernel (S 0).q) := (S 0).hkernel
  have hstage0_comp :
      (CocycleLiftStage.kernel_ezq (I := I) (S := S 0)).hom ≫
          kernel.ι ((E : CpxRI).d b (b + 1)) =
        ((ReduceModI).map (kernel.ι (S 0).q)) ≫
          (reduceModI_obj_iso_quotient (I := I) (S 0).P).hom ≫ (S 0).epq.hom := by
    -- Proof comment: the recursive family already packages the first kernel-comparison identity.
    simpa using CocycleLiftStage.kernel_ezq_hom_comp (I := I) (S := S 0)
  let Praw : CpxR :=
    cocycle_lift_complex (I := I) PClass hprojective hsurj E hacyclic b hb
  have hPrawMinus : CochainComplex.minus ModR Praw := by
    -- Proof comment: the extracted complex inherits the same upper cutoff `b`.
    exact (CochainComplex.minus_iff ModR Praw).2
      ⟨b, cocycle_lift_complex_isStrictlyLE (I := I) PClass hprojective hsurj E hacyclic b hb⟩
  let P : CochainComplex.MinusWithTermsIn PClass :=
    ⟨⟨Praw, hPrawMinus⟩,
      cocycle_lift_complex_term_mem (I := I) PClass hprojective hsurj E hacyclic b hb⟩
  let e :
      ((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ (E : CpxRI) :=
    cocycle_lift_complex_reduction_iso (I := I) PClass hprojective hsurj E hacyclic b hb
  have hPrawAcyclic : Praw.Acyclic :=
    cocycle_lift_complex_acyclic (I := I) PClass hprojective hsurj E hacyclic b hb
  exact ⟨P, e, by simpa [Praw] using hPrawAcyclic⟩

end

end
