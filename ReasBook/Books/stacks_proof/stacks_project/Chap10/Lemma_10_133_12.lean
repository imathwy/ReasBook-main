import Mathlib
import StacksProject_2024.Chap10.Lemma_10_150_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

variable {A : Type u} {B : Type u} {M : Type u} {N : Type u}
variable [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B)
variable [AddCommGroup M] [AddCommGroup N]
variable [Module B M] [Module B N] [Module A M] [Module A N]
variable [IsScalarTower A B M] [IsScalarTower A B N]

/- Domain-style sampling for Lemma 10.133.12:
- primary domain: relative differential operators under localization of the ambient algebra;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LocalizedModule.equivTensorProduct`,
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`;
- best owner abstraction: the canonical base-change extension theorem for formally étale maps,
  specialized here to the localization map `B → Localization S`;
- primitive data: an `A`-linear map `D : M →ₗ[A] N` together with the owner predicate
  `D.IsDifferentialOperatorOfOrder B k`;
- derived API: the localization-specific extension/uniqueness statement, obtained by transporting
  the formally étale base-change owner along `LocalizedModule.equivTensorProduct`.

Source/core/bridge triage:
- `source-facing`: the localization statement in the wording of Lemma 10.133.12;
- `core/canonical`: the later chapter owner
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`;
- `bridge/view`: the identification of localized modules with tensor-product base change via
  `LocalizedModule.equivTensorProduct`. -/

-- Proof sketch: specialize the canonical formally étale base-change extension theorem to the
-- localization map `B → Localization S`, then transport the resulting tensor-product operator
-- across `LocalizedModule.equivTensorProduct`. The extension identity is checked on generators
-- `m ↦ m/1`, and the order condition is preserved because the transport maps are
-- `Localization S`-linear, hence order `0`.
/-- Helper for Lemma 10.133.12: after the localization/tensor-product identification, the
canonical map `m ↦ m/1` matches the tensor-product generator map `m ↦ 1 ⊗ m`. -/
lemma localizedModule_equivTensorProduct_comp_mkLinearMap
    (P : Type u) [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P] :
    (((LocalizedModule.equivTensorProduct S P).restrictScalars A).toLinearMap).comp
        ((LocalizedModule.mkLinearMap S P).restrictScalars A) =
      (TensorProduct.AlgebraTensorModule.mk B (Localization S) (Localization S) P
          (1 : Localization S)).restrictScalars A := by
  ext p
  -- Both sides send `p` to the tensor `1 ⊗ p`.
  simp [LinearMap.comp_apply, Localization.mk_one_eq_algebraMap]

/-- Helper for Lemma 10.133.12: a `Localization S`-linear map is an order-`0` differential
operator after restricting scalars to `A`. -/
lemma restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
    {P Q : Type u} [AddCommGroup P] [AddCommGroup Q]
    [Module (Localization S) P] [Module (Localization S) Q]
    [Module A P] [Module A Q]
    [IsScalarTower A (Localization S) P] [IsScalarTower A (Localization S) Q]
    (f : P →ₗ[Localization S] Q) :
    (f.restrictScalars A).IsDifferentialOperatorOfOrder (Localization S) 0 := by
  -- Order `0` means commuting with every scalar from `Localization S`.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro g p
  simpa using f.map_smul g p

/-- Lemma 10.133.12: an `A`-linear differential operator `D : M → N` of order `k` extends
uniquely to an `A`-linear differential operator `S⁻¹M → S⁻¹N` of the same order. -/
@[stacks 0G36]
lemma existsUnique_localizedModule_extension_of_isDifferentialOperatorOfOrder
    {D : M →ₗ[A] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder B k) :
    ∃! E : LocalizedModule S M →ₗ[A] LocalizedModule S N,
      E.comp ((LocalizedModule.mkLinearMap S M).restrictScalars A) =
          ((LocalizedModule.mkLinearMap S N).restrictScalars A).comp D ∧
        E.IsDifferentialOperatorOfOrder (Localization S) k := by
  let eM : LocalizedModule S M ≃ₗ[A] Localization S ⊗[B] M :=
    (LocalizedModule.equivTensorProduct S M).restrictScalars A
  let eN : LocalizedModule S N ≃ₗ[A] Localization S ⊗[B] N :=
    (LocalizedModule.equivTensorProduct S N).restrictScalars A
  let tensorMkM : M →ₗ[A] Localization S ⊗[B] M :=
    (TensorProduct.AlgebraTensorModule.mk B (Localization S) (Localization S) M
      (1 : Localization S)).restrictScalars A
  let tensorMkN : N →ₗ[A] Localization S ⊗[B] N :=
    (TensorProduct.AlgebraTensorModule.mk B (Localization S) (Localization S) N
      (1 : Localization S)).restrictScalars A
  let EfromTensor :
      (Localization S ⊗[B] M →ₗ[A] Localization S ⊗[B] N) →
        LocalizedModule S M →ₗ[A] LocalizedModule S N :=
    fun F => eN.symm.toLinearMap.comp (F.comp eM.toLinearMap)
  let tensorOfLocalized :
      (LocalizedModule S M →ₗ[A] LocalizedModule S N) →
        Localization S ⊗[B] M →ₗ[A] Localization S ⊗[B] N :=
    fun F => eN.toLinearMap.comp (F.comp eM.symm.toLinearMap)
  haveI : Algebra.FormallyEtale B (Localization S) :=
    Algebra.FormallyEtale.of_isLocalization S
  rcases
      existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale
        (R := A) (S := B) (S' := Localization S) (M := M) (N := N) hD with
    ⟨Dtensor, hDtensor, hDtensor_unique⟩
  let E : LocalizedModule S M →ₗ[A] LocalizedModule S N := EfromTensor Dtensor
  refine ⟨E, ?_, ?_⟩
  constructor
  · -- Push the extension identity to the tensor side, where it is exactly the owner theorem.
    ext m
    apply eN.injective
    have hMkM :
        eM (LocalizedModule.mk m 1) = tensorMkM m := by
      simpa [LocalizedModule.mkLinearMap_apply, eM, tensorMkM, LinearMap.comp_apply] using
        DFunLike.congr_fun
          (localizedModule_equivTensorProduct_comp_mkLinearMap
            (A := A) (B := B) (S := S) M) m
    have hMkN :
        eN ((LocalizedModule.mkLinearMap S N) (D m)) = tensorMkN (D m) := by
      simpa [eN, tensorMkN, LinearMap.comp_apply] using
        DFunLike.congr_fun
          (localizedModule_equivTensorProduct_comp_mkLinearMap
            (A := A) (B := B) (S := S) N) (D m)
    calc
      eN ((E.comp ((LocalizedModule.mkLinearMap S M).restrictScalars A)) m)
          = Dtensor (tensorMkM m) := by
              suffices hEval : Dtensor (eM (LocalizedModule.mk m 1)) = Dtensor (tensorMkM m) by
                simpa [E, EfromTensor, eN, LocalizedModule.mkLinearMap_apply,
                  LinearMap.comp_apply] using hEval
              rw [hMkM]
      _ = tensorMkN (D m) := by
            simpa [tensorMkM, tensorMkN, LinearMap.comp_apply] using
              DFunLike.congr_fun hDtensor.1 m
      _ = eN (((LocalizedModule.mkLinearMap S N).restrictScalars A).comp D m) := by
            rw [LinearMap.comp_apply]
            exact hMkN.symm
  · -- The transport maps are `Localization S`-linear, hence order `0`, so the order bound
    -- survives conjugation.
    have heM_zero :
        eM.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eM] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S M).toLinearMap)
    have heNsymm_zero :
        eN.symm.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eN] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S N).symm.toLinearMap)
    have hmid :
        (Dtensor.comp eM.toLinearMap).IsDifferentialOperatorOfOrder (Localization S) k := by
      simpa [eM, Nat.zero_add] using
        LinearMap.isDifferentialOperatorOfOrder_comp heM_zero hDtensor.2
    simpa [E, EfromTensor, Nat.add_zero] using
      LinearMap.isDifferentialOperatorOfOrder_comp hmid heNsymm_zero
  · intro F hF
    rcases hF with ⟨hF_extends, hF_order⟩
    let Ftensor : Localization S ⊗[B] M →ₗ[A] Localization S ⊗[B] N :=
      tensorOfLocalized F
    have heMsymm_zero :
        eM.symm.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eM] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S M).symm.toLinearMap)
    have heN_zero :
        eN.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eN] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S N).toLinearMap)
    have hFtensor_extends :
        Ftensor.comp tensorMkM = tensorMkN.comp D := by
      ext m
      have hMkM :
          eM ((LocalizedModule.mkLinearMap S M) m) = tensorMkM m := by
        simpa [eM, tensorMkM, LinearMap.comp_apply] using
          DFunLike.congr_fun
            (localizedModule_equivTensorProduct_comp_mkLinearMap
              (A := A) (B := B) (S := S) M) m
      have hMkN :
          eN ((LocalizedModule.mkLinearMap S N) (D m)) = tensorMkN (D m) := by
        simpa [eN, tensorMkN, LinearMap.comp_apply] using
          DFunLike.congr_fun
            (localizedModule_equivTensorProduct_comp_mkLinearMap
              (A := A) (B := B) (S := S) N) (D m)
      calc
        Ftensor (tensorMkM m)
            = eN (F ((LocalizedModule.mkLinearMap S M) m)) := by
                rw [← hMkM]
                simp [Ftensor, tensorOfLocalized, eM, eN, LinearMap.comp_apply]
        _ = eN (((LocalizedModule.mkLinearMap S N).restrictScalars A).comp D m) := by
              simpa [LinearMap.comp_apply] using DFunLike.congr_fun hF_extends m
        _ = tensorMkN (D m) := hMkN
    have hFtensor_order :
        Ftensor.IsDifferentialOperatorOfOrder (Localization S) k := by
      have hmid :
          (F.comp eM.symm.toLinearMap).IsDifferentialOperatorOfOrder (Localization S) k := by
        simpa [eM, Nat.zero_add] using
          LinearMap.isDifferentialOperatorOfOrder_comp heMsymm_zero hF_order
      simpa [Ftensor, tensorOfLocalized, eN, Nat.add_zero] using
        LinearMap.isDifferentialOperatorOfOrder_comp hmid heN_zero
    have hFtensor_eq : Ftensor = Dtensor := hDtensor_unique Ftensor ⟨hFtensor_extends, hFtensor_order⟩
    ext x
    apply eN.injective
    have hEval := DFunLike.congr_fun hFtensor_eq (eM x)
    simpa [Ftensor, E, EfromTensor, tensorOfLocalized, eM, eN, LinearMap.comp_apply] using hEval

end
