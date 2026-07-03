import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeResidueEvaluation
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_1

open scoped Representation

noncomputable section

universe u v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-- Helper for Exercise 12-12.7-8: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeExercise121278KernelTransportGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278KernelTransportGroup

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: if an owner element of `A ⊗ R_K(G)` already lies in LinearRepresentations_Serre_1977's
realized scalar extension `A ⊗ V[K,p](ΓK)`, then its tensor-character representative dies in the
quotient `A ⊗ (R_K(G) / V[K,p](ΓK))`. This is the owner-side quotient-killing bridge used before
transporting to a fixed fiber. -/
theorem owner_tensor_quotient_image_eq_zero_of_mem_gammaP_scalarExtension
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (hf_gammaP : ((f : G → K) ∈ gammaPElementaryInducedCharacterScalarExtension A K ΓK p)) :
    LinearMap.lTensor A (Submodule.mkQ (V[K,p](ΓK)))
      ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f) = 0 := by
  rcases hf_gammaP with ⟨ξ, hξ⟩
  have howner_eq :
      (ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f =
        LinearMap.lTensor A (V[K,p](ΓK)).subtype ξ := by
    -- Compare the owner tensors through their common realization as the same `K`-valued function.
    apply tensorCharacterRingToFunction_injective_gammaP (A := A) (K := K) (G := G)
    calc
      tensorCharacterRingToFunction (A := A) (K := K) (G := G)
          ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f) =
        (f : G → K) := by
          simpa using
            tensorCharacterRingRealization_ownerLinearEquiv_apply
              (A := A) (K := K) (G := G) f
      _ = tensorGammaPElementaryInducedCharacterToFunction A K ΓK p ξ := by
          simpa using hξ.symm
      _ = tensorCharacterRingToFunction (A := A) (K := K) (G := G)
            (LinearMap.lTensor A (V[K,p](ΓK)).subtype ξ) := by
          simpa using
            tensorGammaPElementaryInducedCharacterToFunction_eq_tensorCharacterRingToFunction_lTensor
              (A := A) (K := K) (ΓK := ΓK) (p := p) ξ
  have hmem_ker :
      (ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f ∈
        LinearMap.ker (LinearMap.lTensor A (Submodule.mkQ (V[K,p](ΓK)))) := by
    -- Once the owner tensor is identified with a tensor coming from `V[K,p](ΓK)`, quotienting
    -- by `V[K,p](ΓK)` kills it by tensor right exactness.
    rw [ker_lTensor_mkQ_eq_range_lTensor_gammaP_subtype_gammaP
      (A := A) (K := K) (ΓK := ΓK) (p := p)]
    exact ⟨ξ, howner_eq.symm⟩
  exact hmem_ker

/-- Helper for Exercise 12-12.7-8: the owner-side quotient-killing bridge remains zero after
transporting the generator `includeRight f` into the fixed fiber over `M`. This is the
transport-stable quotient bridge needed in the source-faithful fixed-fiber argument. -/
theorem regular_fiber_includeRight_quotient_image_eq_zero_of_mem_gammaP_scalarExtension
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (hf_gammaP : ((f : G → K) ∈ gammaPElementaryInducedCharacterScalarExtension A K ΓK p)) :
    LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
      (regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)) = 0 := by
  rcases hf_gammaP with ⟨ξ, hξ⟩
  have howner_eq :
      (ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f =
        LinearMap.lTensor A (V[K,p](ΓK)).subtype ξ := by
    -- Use the same owner-side realization comparison as in the base ring quotient-kill lemma.
    apply tensorCharacterRingToFunction_injective_gammaP (A := A) (K := K) (G := G)
    calc
      tensorCharacterRingToFunction (A := A) (K := K) (G := G)
          ((ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f) =
        (f : G → K) := by
          simpa using
            tensorCharacterRingRealization_ownerLinearEquiv_apply
              (A := A) (K := K) (G := G) f
      _ = tensorGammaPElementaryInducedCharacterToFunction A K ΓK p ξ := by
          simpa using hξ.symm
      _ = tensorCharacterRingToFunction (A := A) (K := K) (G := G)
            (LinearMap.lTensor A (V[K,p](ΓK)).subtype ξ) := by
          simpa using
            tensorGammaPElementaryInducedCharacterToFunction_eq_tensorCharacterRingToFunction_lTensor
              (A := A) (K := K) (ΓK := ΓK) (p := p) ξ
  -- Route correction: rather than trying to transport the owner-side zero statement abstractly,
  -- rewrite the transported generator to `1 ⊗ ξ` and kill it directly by tensor induction on the
  -- witness in `A ⊗ V[K,p](ΓK)`.
  rw [regular_fiber_to_tensorCharacterRingLinearEquiv_includeRight_formula, howner_eq]
  induction ξ using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a χ =>
      -- On a pure tensor, quotienting kills the `V[K,p](ΓK)` factor after the base-change rewrite.
      rw [LinearMap.lTensor_tmul]
      rw [fiber_linearEquiv_tensorCharacterRingOverField_baseChange_tmul_tmul
        (A := A) (K := K) (G := G) (F := M.1.asIdeal.ResidueField)
        (a := (1 : M.1.asIdeal.ResidueField)) (b := a)
        (χ := (show R[K](G) from (V[K,p](ΓK)).subtype χ))]
      rw [LinearMap.lTensor_tmul]
      simp
  | add ξ η hξ hη =>
      -- Both transport and quotient maps are linear, so the sum vanishes componentwise.
      simp [map_add, hξ, hη]

end RegularPrime

end

end Representation
