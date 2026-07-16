import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_3_3
import StacksProject_2024.stacks_project.Chap15.Situation_15_6_1

open CategoryTheory

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/-- Helper for Lemma 15.6.6: the explicit tensor-model object for extension of scalars along
`S.fromAprime`. -/
noncomputable abbrev fromAprime_tensor_obj (M : ModuleCat A') : ModuleCat A := by
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  exact ModuleCat.of A (TensorProduct A' A M)

/-- Helper for Lemma 15.6.6: the quotient-model object `M / ker(S.fromAprime) M`, viewed as an
`A`-module via the quotient-kernel equivalence. -/
noncomputable abbrev fromAprime_quotient_obj (M : ModuleCat A') : ModuleCat A := by
  let I : Ideal A' := RingHom.ker S.fromAprime
  let eA : A' ⧸ I ≃+* A := RingHom.quotientKerEquivOfSurjective S.fromAprime_surjective
  let _ : Module A (M ⧸ (I • (⊤ : Submodule A' M))) :=
    Module.compHom _ eA.symm.toRingHom
  exact ModuleCat.of A (M ⧸ (I • (⊤ : Submodule A' M)))

/-- Helper for Lemma 15.6.6: scalar extension along `S.fromAprime` identifies with the explicit
tensor model. -/
noncomputable def fromAprime_extendScalars_obj_iso_tensor
    (M : ModuleCat A') :
    (ModuleCat.extendScalars S.fromAprime).obj M ≅
      fromAprime_tensor_obj (S := S) M := by
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  letI :
      IsScalarTower A' A
        ↑((ModuleCat.restrictScalars S.fromAprime).obj
          (ModuleCat.of A A)) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ rfl
  let e :
      ↑((ModuleCat.restrictScalars S.fromAprime).obj
        (ModuleCat.of A A)) ≃ₗ[A] A :=
    { __ := AddEquiv.refl A
      map_smul' := fun _ _ ↦ rfl }
  -- Normalize `ModuleCat.extendScalars` to the explicit tensor presentation `A ⊗[A'] M`.
  simpa [fromAprime_tensor_obj, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl A' M)).toModuleIso

/-- Helper for Lemma 15.6.6: scalar extension along `S.fromAprime` identifies with the quotient
model `M / ker(S.fromAprime) M`. -/
noncomputable def fromAprime_extendScalars_obj_iso_quotient
    (M : ModuleCat A') :
    (ModuleCat.extendScalars S.fromAprime).obj M ≅
      fromAprime_quotient_obj (S := S) M := by
  -- Compose the tensor normalization with the source-faithful quotient model.
  -- TODO: identify `A ⊗[A'] M` with `M / ker(S.fromAprime) M` using
  -- `Ideal.quotientKerAlgEquivOfSurjective S.fromAprime_surjective` and
  -- `TensorProduct.quotTensorEquivQuotSMul`.
  sorry

/-- Helper for Lemma 15.6.6: in the quotient model, `mkQ x` corresponds to the tensor generator
`1 ⊗ₜ x`. -/
lemma fromAprime_extendScalars_obj_iso_quotient_inv_mkQ
    (M : ModuleCat A') (x : M) :
    ((fromAprime_extendScalars_obj_iso_quotient (S := S) M).inv).hom
        (((RingHom.ker S.fromAprime) • (⊤ : Submodule A' M)).mkQ x) =
      let _ : Algebra A' A := S.fromAprime.toAlgebra
      ((1 : A) ⊗ₜ[A'] x : (ModuleCat.extendScalars S.fromAprime).obj M) := by
  -- TODO: compare both candidates after applying the forward quotient-model isomorphism.
  sorry

/-- Helper for Lemma 15.6.6: the standard quotient/tensor equivalence is natural in the module
map. -/
lemma fromAprime_quotientMapByIdeal_lTensor_naturality
    {M N : Type*} [AddCommGroup M] [Module A' M] [AddCommGroup N] [Module A' N]
    (ψ : M →ₗ[A'] N) :
    ψ.quotientMapByIdeal (RingHom.ker S.fromAprime) ∘ₗ
        TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker S.fromAprime) =
      TensorProduct.quotTensorEquivQuotSMul N (RingHom.ker S.fromAprime) ∘ₗ
        ψ.lTensor (A' ⧸ RingHom.ker S.fromAprime) := by
  -- Compare both quotient routes on pure tensors, where the quotient formula is explicit.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

end
