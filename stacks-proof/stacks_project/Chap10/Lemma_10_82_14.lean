import Mathlib
import stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

namespace LinearMap

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Helper for Lemma 10.82.14: after identifying `M` with `R ⊗[R] M` and commuting the factors,
the tensor of `R → S` agrees with the canonical map `m ↦ m ⊗ₜ 1`. -/
lemma tensorProduct_mk_one_eq
    (M : Type w) [AddCommGroup M] [Module R M] :
    (TensorProduct.comm R S M).toLinearMap.comp
        (((Algebra.linearMap R S).rTensor M).comp (TensorProduct.lid R M).symm.toLinearMap) =
      (TensorProduct.mk R M S).flip (1 : S) := by
  -- Compare the two linear maps on an arbitrary element of `M`.
  ext m
  simp [TensorProduct.lid_symm_apply]

/-- Helper for Lemma 10.82.14: universal injectivity of `R → S` makes the canonical map
`m ↦ m ⊗ₜ 1` injective for every `R`-module `M`. -/
lemma tensorProduct_mk_one_injective_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) :
    Function.Injective ((TensorProduct.mk R M S).flip (1 : S)) := by
  let eM : ULift.{x} M ≃ₗ[R] M := ULift.moduleEquiv
  let eTensor : ULift.{x} M ⊗[R] S ≃ₗ[R] M ⊗[R] S :=
    TensorProduct.congr eM (LinearEquiv.refl R S)
  have hLiftedInjective :
      Function.Injective ((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) := by
    -- On the lifted module, the universal injectivity hypothesis applies directly.
    rw [← tensorProduct_mk_one_eq (R := R) (S := S) (ULift.{x} M)]
    exact (TensorProduct.comm R S (ULift.{x} M)).injective.comp
      ((hS (ULift.{x} M) inferInstance inferInstance).comp
        (TensorProduct.lid R (ULift.{x} M)).symm.injective)
  have hCompat :
      eTensor.toLinearMap.comp ((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) =
        ((TensorProduct.mk R M S).flip (1 : S)).comp eM.toLinearMap := by
    -- The tensor canonical map commutes with the linear equivalence `ULift M ≃ₗ[R] M`.
    ext m
    simp [eM, eTensor]
  intro m₁ m₂ hm
  have hLiftedEq : ULift.up m₁ = ULift.up m₂ := by
    -- Transport the equality to the lifted module, where injectivity is available.
    apply hLiftedInjective
    apply eTensor.injective
    calc
      eTensor (((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) (ULift.up m₁)) =
          ((TensorProduct.mk R M S).flip (1 : S)) (eM (ULift.up m₁)) := by
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hCompat (ULift.up m₁)
      _ = ((TensorProduct.mk R M S).flip (1 : S)) m₁ := by
            simp [eM]
      _ = ((TensorProduct.mk R M S).flip (1 : S)) m₂ := hm
      _ = ((TensorProduct.mk R M S).flip (1 : S)) (eM (ULift.up m₂)) := by
            simp [eM]
      _ = eTensor (((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) (ULift.up m₂)) := by
            symm
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hCompat (ULift.up m₂)
  simpa using hLiftedEq

/-- Helper for Lemma 10.82.14: tensoring commutes with the canonical map `m ↦ m ⊗ₜ 1`. -/
lemma rTensor_comp_tensorProduct_mk_one {f : M →ₗ[R] N} :
    (f.rTensor S).comp ((TensorProduct.mk R M S).flip (1 : S)) =
      ((TensorProduct.mk R N S).flip (1 : S)).comp f := by
  -- This is the standard `rTensor` naturality formula specialized at the tensor factor `1`.
  simpa using (LinearMap.rTensor_comp_flip_mk (M := S) (f := f) (m := (1 : S)))

/-- Helper for Lemma 10.82.14: if `f ⊗[R] S` is surjective, then the tensor of the quotient map to
the cokernel `N ⧸ range f` is zero. -/
lemma quotientMap_rTensor_eq_zero_of_rTensor_surjective {f : M →ₗ[R] N}
    (hf : Function.Surjective (f.rTensor S)) :
    (((LinearMap.range f).mkQ).rTensor S) = 0 := by
  -- Evaluate on pure tensors and pull each one back along the surjective tensor map.
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := hf z
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.range_mkQ_comp]
  simp

-- Proof sketch: injectivity is detected by applying the universal injectivity hypothesis to the
-- kernel inclusion `ker f → M`.
/-- Lemma 10.82.14 (injective clause): if `R → S` is universally injective as an `R`-module map,
then tensoring an `R`-linear map with `S` reflects injectivity. -/
theorem injective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Injective (f.rTensor S)) : Function.Injective f := by
  intro x y hxy
  -- Apply the naturality square for `m ↦ m ⊗ₜ 1` and cancel with the injectivity of `f ⊗[R] S`.
  have hTensor :
      ((TensorProduct.mk R M S).flip (1 : S)) x =
        ((TensorProduct.mk R M S).flip (1 : S)) y := by
    apply hf
    calc
      (f.rTensor S) (((TensorProduct.mk R M S).flip (1 : S)) x) =
          ((TensorProduct.mk R N S).flip (1 : S)) (f x) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun (rTensor_comp_tensorProduct_mk_one (R := R) (S := S) (f := f)) x
      _ = ((TensorProduct.mk R N S).flip (1 : S)) (f y) := by
            rw [hxy]
      _ = (f.rTensor S) (((TensorProduct.mk R M S).flip (1 : S)) y) := by
            simpa [LinearMap.comp_apply] using
              (LinearMap.congr_fun
                (rTensor_comp_tensorProduct_mk_one (R := R) (S := S) (f := f)) y).symm
  -- The universally injective base-change map detects equality back in `M`.
  exact tensorProduct_mk_one_injective_of_universallyInjective (R := R) (S := S) (M := M) hS hTensor

-- Proof sketch: surjectivity is detected from the cokernel after tensoring and the same universal
-- injectivity hypothesis applied to the canonical map `Q → Q ⊗[R] S`.
/-- Lemma 10.82.14 (surjective clause): if `R → S` is universally injective as an `R`-module map,
then tensoring an `R`-linear map with `S` reflects surjectivity. -/
theorem surjective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Surjective (f.rTensor S)) : Function.Surjective f := by
  intro y
  -- The tensor of the cokernel quotient map vanishes because `f ⊗[R] S` is surjective.
  have hQuotZero :
      (((LinearMap.range f).mkQ).rTensor S) = 0 :=
    quotientMap_rTensor_eq_zero_of_rTensor_surjective (R := R) (S := S) (f := f) hf
  have hCompZero :
      ((TensorProduct.mk R (N ⧸ LinearMap.range f) S).flip (1 : S)).comp (LinearMap.range f).mkQ =
        0 := by
    -- Tensor naturality turns the zero quotient tensor map into a zero canonical map on the
    -- quotient itself.
    calc
      ((TensorProduct.mk R (N ⧸ LinearMap.range f) S).flip (1 : S)).comp (LinearMap.range f).mkQ =
          (((LinearMap.range f).mkQ).rTensor S).comp ((TensorProduct.mk R N S).flip (1 : S)) := by
            symm
            exact rTensor_comp_tensorProduct_mk_one
              (R := R) (S := S) (f := (LinearMap.range f).mkQ)
      _ = 0 := by
            rw [hQuotZero, zero_comp]
  have hTensorZero :
      ((TensorProduct.mk R (N ⧸ LinearMap.range f) S).flip (1 : S)) ((LinearMap.range f).mkQ y) =
        0 := by
    -- Evaluate the zero composite at the class of `y`.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hCompZero y
  have hClassZero : (LinearMap.range f).mkQ y = 0 := by
    -- Universal injectivity applied to the quotient module detects that the cokernel class is
    -- already zero.
    apply tensorProduct_mk_one_injective_of_universallyInjective
      (R := R) (S := S) (M := N ⧸ LinearMap.range f) hS
    simpa using hTensorZero
  have hy_range : y ∈ LinearMap.range f := by
    -- Zero class in the cokernel is exactly membership in the range.
    exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range f) (x := y)).1 <|
      by simpa [Submodule.mkQ_apply] using hClassZero
  -- Unpack range membership to produce a preimage of `y`.
  simpa [LinearMap.mem_range] using hy_range

-- Proof sketch: bijectivity is the conjunction of injectivity and surjectivity.
/-- If tensoring with `S` makes an `R`-linear map bijective, then the original map is bijective,
provided `R → S` is universally injective as an `R`-module map. -/
theorem bijective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Bijective (f.rTensor S)) : Function.Bijective f :=
  ⟨injective_of_rTensor_of_universallyInjective hS hf.1,
    surjective_of_rTensor_of_universallyInjective hS hf.2⟩

end

end LinearMap
