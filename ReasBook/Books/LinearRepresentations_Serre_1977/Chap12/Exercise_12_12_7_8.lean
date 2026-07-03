import LinearRepresentations_Serre_1977.Chap12.GaloisPowerClasses
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.ScalarExtensionTransport
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.KernelTransport
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.ZeroFiberPrimeClassification
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeClassification
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeResidueEvaluation
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeTensorOwner

open scoped Representation

noncomputable section

universe v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
local notation "RegularPrimeIndex" =>
  Σ p : Nat.Primes, NonzeroResidualCharacteristicMaximalIdeal A p ×
    PRegularGaloisPowerClass ΓK p

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: once LinearRepresentations_Serre_1977's fixed-fiber evaluator is known to have trivial
kernel, the separator-based surjectivity theorem upgrades it to the expected algebra equivalence
with the function ring on `p`-regular `Γ_K`-classes. -/
private noncomputable def
    fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions_of_injective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hinj :
      Function.Injective (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M)) :
    (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) :=
  -- Once the kernel is known to be zero, LinearRepresentations_Serre_1977's separator characters already supply the
  -- surjective half of the fixed-fiber identification.
  AlgEquiv.ofBijective
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M)
    ⟨hinj, regular_fiber_eval_family_surjective_from_separators (A := A) (K := K) (G := G) M⟩

/-- Helper for Exercise 12-12.7-8: the only missing step in the fixed-fiber route is injectivity
of LinearRepresentations_Serre_1977's evaluator on the fiber over `M`. -/
private theorem regular_fiber_eval_zero_on_pregular_representatives
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (hξ :
      ∀ c : PRegularGaloisPowerClass ΓK p,
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c = 0) :
    ∀ x : {x : G // IsPRegular p x},
      (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
        (PRegularConjClass.ofSubtype p x) = 0 := by
  intro x
  -- Normalize the quotient-level vanishing hypothesis back to LinearRepresentations_Serre_1977's honest `p`-regular
  -- representatives before invoking the still-missing quotient-killing step.
  exact
    (regular_fiber_eval_family_algHom_mk_eq_zero_iff
      (A := A) (K := K) (G := G) M ξ x).mp
      (hξ (pRegularGaloisPowerClassMk ΓK p x))

/-- Helper for Exercise 12-12.7-8: LinearRepresentations_Serre_1977's Lemma `12-12.7-7` can be repackaged as an owner
element `f : A ⊗ R_K(G)` together with an `A`-valued lift `φ` whose residue classes are constant
and nonzero on `p`-regular `Γ_K`-classes. This fixes the source-faithful multiplier before the
remaining quotient-killing transport step. -/
private theorem exists_gammaP_owner_witness_nonzero_on_pregular_classes
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    ∃ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
      ∃ φ : G → A,
        ((f : G → K) ∈ gammaPElementaryInducedCharacterScalarExtension A K ΓK p) ∧
        (((algebraMap A K) ∘ φ) = (f : G → K)) ∧
        (∀ {x y : {x : G // IsPRegular p x}},
            pRegularGaloisPowerClassMk ΓK p x = pRegularGaloisPowerClassMk ΓK p y →
              algebraMap A M.1.asIdeal.ResidueField (φ x.1) =
                algebraMap A M.1.asIdeal.ResidueField (φ y.1)) ∧
        ∀ x : {x : G // IsPRegular p x},
          algebraMap A M.1.asIdeal.ResidueField (φ x.1) ≠ 0 := by
  obtain ⟨χ, φ, hφ, hnonzero⟩ :=
    exists_auxiliary_function_mem_gammaPImageScalarExtension_nonzero_mod_primeIdealsOverPrime
      (A := A) (G := G) (L := L) (K := K) p
  let ψ : G → K :=
    tensorGammaPElementaryInducedCharacterToFunction_local
      (K := K) (G := G) (A := A) p χ
  have hψ_gammaP :
      ψ ∈ gammaPElementaryInducedCharacterScalarExtension A K ΓK p := by
    -- The chosen tensor witness already lies in LinearRepresentations_Serre_1977's realized scalar extension `A ⊗ V[K,p]`.
    simpa [ψ, gammaPElementaryInducedCharacterSpan_local,
      tensorGammaPElementaryInducedCharacterToFunction_local] using
      tensorGammaPElementaryInducedCharacter_mem_gammaPElementaryInducedCharacterScalarExtension
        (A := A) (K := K) (G := G) ΓK p χ
  have hψ_owner :
      ψ ∈ characterRingOverFieldAlgebraScalarExtension A K G := by
    -- The ambient owner `A ⊗ R_K(G)` contains the entire realized `γ_p` scalar extension.
    exact
      gammaPElementaryInducedCharacterScalarExtension_le_characterRingOverFieldAlgebraScalarExtension_gammaP
        (A := A) (K := K) (G := G) ΓK p hψ_gammaP
  refine ⟨⟨ψ, hψ_owner⟩, φ, hψ_gammaP, ?_, ?_, ?_⟩
  · -- Repackage the source witness equality with the chosen owner element.
    simpa [ψ] using hφ
  · intro x y hxy
    -- The residue of the chosen lift depends only on the `Γ_K`-class because the owner values do.
    exact
      lifted_owner_residue_eq_of_galoisPowerClass_eq
        (A := A) (K := K) (G := G) (p := p) M ⟨ψ, hψ_owner⟩ φ
        (by simpa [ψ] using hφ) hxy
  · intro x hx_zero
    -- Reducing to zero modulo `M` would place the chosen lift inside `M`, contradicting the
    -- source nonvanishing witness from Lemma `12-12.7-7`.
    let Q : PrimeSpectrum A := ⟨M.1.asIdeal, inferInstance⟩
    have hp_mem : (p : A) ∈ M.1.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using (CharP.cast_eq_zero (R := M.1.asIdeal.ResidueField) p)
    have hp_zeroLocus :
        Q ∈ PrimeSpectrum.zeroLocus (Ideal.span ({(p : A)} : Set A) : Set A) := by
      rw [PrimeSpectrum.mem_zeroLocus, Ideal.span_singleton_le_iff_mem]
      exact hp_mem
    have hnot_mem : φ x.1 ∉ M.1.asIdeal := by
      simpa [Q] using hnonzero x.1 Q hp_zeroLocus
    exact hnot_mem ((Ideal.algebraMap_residueField_eq_zero (I := M.1.asIdeal)).mp hx_zero)

/-- Helper for Exercise 12-12.7-8: if every coordinate of `ξ` vanishes under LinearRepresentations_Serre_1977's fixed-fiber
evaluator, then the same is true after multiplying `ξ` on the left by any fixed-fiber element.
This isolates the purely algebra-homomorphic part of the kernel argument before the missing
quotient transport is invoked. -/
private theorem regular_fiber_eval_family_mul_left_zero_of_eval_family_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (η ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (hξ :
      ∀ c : PRegularGaloisPowerClass ΓK p,
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c = 0) :
    ∀ c : PRegularGaloisPowerClass ΓK p,
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M (η * ξ)) c = 0 := by
  intro c
  -- Because the evaluator is an algebra hom, multiplying by any fixed fiber element only
  -- multiplies the vanishing coordinate by another residue scalar.
  rw [regular_fiber_eval_family_algHom, map_mul, hξ c, mul_zero]

/-- Helper for Exercise 12-12.7-8: if an auxiliary owner witness `f` is presented by an
`A`-valued lift `φ`, then evaluating its `includeRight` image at the class of a chosen
`p`-regular representative returns the residue class of `φ(x)`. This isolates the scalar factor
that later appears in LinearRepresentations_Serre_1977's multiplier argument. -/
private theorem regular_fiber_eval_family_includeRight_value_of_owner_witness
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (φ : G → A)
    (hφ : ((algebraMap A K) ∘ φ) = (f : G → K))
    (x : {x : G // IsPRegular p x}) :
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f))
        (pRegularGaloisPowerClassMk ΓK p x) =
      algebraMap A M.1.asIdeal.ResidueField (φ x.1) := by
  -- Evaluate on the chosen representative, then rewrite the owner residue value using the
  -- explicit `A`-lift `φ`.
  rw [regular_fiber_eval_family_algHom_mk]
  rw [regular_fiber_prequotient_eval_family_algHom_includeRight_apply]
  rw [owner_pregular_residue_eval_of_isIntegralClosure_ofSubtype]
  simpa [Function.comp] using
    (residueFieldOfLiftedValue_eq_algebraMap
      (A := A) (K := K) (p := p) M
      (owner_pregular_value_mem_range_on_pRegular_representatives_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) f x)
      (φ x.1)
      (by simpa [Function.comp] using congrFun hφ x.1))

/-- Helper for Exercise 12-12.7-8: the `γ_p` owner witness from Lemma `12-12.7-7` evaluates to a
nonzero residue scalar on every `p`-regular `Γ_K`-class. This packages the source-faithful
nonvanishing input used in the cancellation step. -/
private theorem regular_fiber_eval_family_includeRight_nonzero_of_owner_witness
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (φ : G → A)
    (hφ : ((algebraMap A K) ∘ φ) = (f : G → K))
    (hnonzero :
      ∀ x : {x : G // IsPRegular p x},
        algebraMap A M.1.asIdeal.ResidueField (φ x.1) ≠ 0) :
    ∀ x : {x : G // IsPRegular p x},
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
          ((Algebra.TensorProduct.includeRight
            (R := A) (A := M.1.asIdeal.ResidueField)
            (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f))
          (pRegularGaloisPowerClassMk ΓK p x) ≠ 0 := by
  intro x
  -- Rewrite the class evaluation as the residue of the chosen `A`-lift, then apply the
  -- witness's nonvanishing hypothesis.
  rw [regular_fiber_eval_family_includeRight_value_of_owner_witness
    (A := A) (K := K) (G := G) (p := p) M f φ hφ x]
  exact hnonzero x

/-- Helper for Exercise 12-12.7-8: after multiplying `ξ` by the `includeRight` image of the
auxiliary witness `f`, the coordinate at a chosen `p`-regular class is the residue of `φ(x)`
times the original coordinate of `ξ`. This is the representative-level multiplier formula from
LinearRepresentations_Serre_1977's source route. -/
private theorem regular_fiber_auxiliary_product_eval_value
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (φ : G → A)
    (hφ : ((algebraMap A K) ∘ φ) = (f : G → K))
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (x : {x : G // IsPRegular p x}) :
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
        (((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f) * ξ))
        (pRegularGaloisPowerClassMk ΓK p x) =
      algebraMap A M.1.asIdeal.ResidueField (φ x.1) *
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
          (pRegularGaloisPowerClassMk ΓK p x) := by
  -- Because the evaluator is an algebra hom, multiplication by `includeRight f` multiplies the
  -- chosen coordinate by the residue scalar coming from `φ(x)`.
  have hmul :=
    congrArg
      (fun g : PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField ↦
        g (pRegularGaloisPowerClassMk ΓK p x))
      ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).map_mul
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)
        ξ)
  simpa [regular_fiber_eval_family_includeRight_value_of_owner_witness
      (A := A) (K := K) (G := G) (p := p) M f φ hφ x] using hmul

/-- Helper for Exercise 12-12.7-8: if every coordinate of `ξ` vanishes, then the auxiliary
multiplier formula already forces the scaled representative values to vanish. This closes the
purely evaluator-side part of LinearRepresentations_Serre_1977's multiplier argument before the missing quotient bridge is
inserted. -/
private theorem regular_fiber_auxiliary_product_eval_eq_zero_of_eval_family_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (φ : G → A)
    (hφ : ((algebraMap A K) ∘ φ) = (f : G → K))
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (hξ :
      ∀ c : PRegularGaloisPowerClass ΓK p,
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c = 0) :
    ∀ x : {x : G // IsPRegular p x},
      algebraMap A M.1.asIdeal.ResidueField (φ x.1) *
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
          (pRegularGaloisPowerClassMk ΓK p x) = 0 := by
  intro x
  -- Rewrite the target scalar multiple as the class evaluation of the auxiliary product, then
  -- reuse the algebra-homomorphic zero statement above.
  rw [← regular_fiber_auxiliary_product_eval_value
    (A := A) (K := K) (G := G) (p := p) M f φ hφ ξ x]
  exact
    regular_fiber_eval_family_mul_left_zero_of_eval_family_zero
      (A := A) (K := K) (G := G) M
      ((Algebra.TensorProduct.includeRight
        (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)
      ξ hξ
      (pRegularGaloisPowerClassMk ΓK p x)

/-- Helper for Exercise 12-12.7-8: after tensoring LinearRepresentations_Serre_1977's quotient
`R[K](G) / V[K,p](ΓK)` with the residue field of `M`, every transported `includeRight`
generator already dies. The fixed-`p` annihilator from Theorem `12-12.6-3` becomes invertible
modulo `M`, so the entire quotient tensor vanishes on these generators. -/
private theorem regular_fiber_includeRight_tensor_quotient_image_eq_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
      (regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)) = 0 := by
  obtain ⟨N, hcop, hNmem⟩ :=
    exists_coprime_scalar_smul_mem_gammaPElementaryInducedCharacterSpan
      (G := G) (L := L) (K := K) p
  let χ : R[K](G) :=
    (ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)) f
  have hNχ_mem : N • χ ∈ V[K,p](ΓK) := by
    -- The public fixed-`p` annihilator already places `N • χ` in LinearRepresentations_Serre_1977's `γ_p` owner.
    simpa [χ, Representation.gammaPElementaryInducedCharacterSpan] using hNmem χ
  have hN_cast_ne :
      ((N : ℕ) : M.1.asIdeal.ResidueField) ≠ 0 := by
    -- Because `N` is coprime to the residue characteristic `p`, its image in the residue field
    -- is nonzero and therefore invertible.
    intro hN_zero
    have hN_dvd : (p : ℕ) ∣ N :=
      (CharP.cast_eq_zero_iff M.1.asIdeal.ResidueField p N).mp hN_zero
    exact ((p.2.coprime_iff_not_dvd).mp hcop) hN_dvd
  have htmul_zero :
      ((N : M.1.asIdeal.ResidueField) •
          LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
            ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ)) = 0 := by
    -- Move the scalar `N` across the tensor factor, then quotient-kill `N • χ`.
    calc
      ((N : M.1.asIdeal.ResidueField) •
          LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
            ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ))
          =
        LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
          (((N : M.1.asIdeal.ResidueField) : M.1.asIdeal.ResidueField) •
            ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ)) := by
              simp
      _ =
        LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
          ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] (N • χ)) := by
            rw [TensorProduct.tmul_smul]
      _ = 0 := by
        rw [LinearMap.lTensor_tmul]
        exact (Submodule.Quotient.mk_eq_zero (V[K,p](ΓK))).2 hNχ_mem
  have hq_zero :
      LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
        ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) = 0 := by
    -- Cancel the nonzero scalar `N` in the residue field.
    exact (smul_eq_zero.mp htmul_zero).resolve_left hN_cast_ne
  have htransport :
      regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f) =
        ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) := by
    -- Normalize the transported generator to the pure tensor `1 ⊗ owner(f)`.
    rw [regular_fiber_to_tensorCharacterRingLinearEquiv_includeRight_formula]
    simpa [χ] using
      fiber_linearEquiv_tensorCharacterRingOverField_baseChange_tmul_tmul
        (A := A) (K := K) (G := G) (F := M.1.asIdeal.ResidueField)
        (a := (1 : M.1.asIdeal.ResidueField)) (b := (1 : A)) χ
  simpa [htransport] using hq_zero

/-- Helper for Exercise 12-12.7-8: the transported quotient map
`k(M) ⊗ R[K](G) → k(M) ⊗ (R[K](G) / V[K,p](ΓK))` is already zero on the entire fixed fiber.
This records the true Chapter `12.6.3` effect on the regular-fiber transport: the quotient tensor
vanishes after reducing modulo a maximal ideal of characteristic `p`. -/
private theorem regular_fiber_tensor_quotient_image_eq_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :
    LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))
      (regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M ξ) = 0 := by
  -- Route correction: Theorem `12-12.6-3` annihilates the tensor quotient outright after
  -- reducing modulo `M`, so tensor induction on the fiber is enough here.
  refine TensorProduct.induction_on ξ ?_ ?_ ?_
  · simp
  · intro a f
    have htmul :
        (a ⊗ₜ[A] f :
          M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) =
          a • ((Algebra.TensorProduct.includeRight
            (R := A) (A := M.1.asIdeal.ResidueField)
            (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f) := by
      simpa using
        (TensorProduct.smul_tmul' a (1 : M.1.asIdeal.ResidueField) f).symm
    rw [htmul, map_smul, LinearEquiv.map_smul]
    simp [regular_fiber_includeRight_tensor_quotient_image_eq_zero
      (A := A) (K := K) (G := G) (p := p) M f]
  · intro ξ η hξ hη
    simp [map_add, hξ, hη]

/-- Helper for Exercise 12-12.7-8: once every coordinate of LinearRepresentations_Serre_1977's fixed-fiber evaluator
vanishes, the fixed-fiber element itself should be zero. This isolates the remaining
source-faithful quotient-killing step from the later injectivity wrapper. -/
private theorem regular_fiber_transport_mem_gammaP_tensor_image
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :
    ∃ ζ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK)),
      LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype ζ =
        regular_fiber_to_tensorCharacterRingLinearEquiv
          (A := A) (K := K) (G := G) (p := p) M ξ := by
  -- The transported quotient class already vanishes on the whole fixed fiber, so right
  -- exactness identifies the transported tensor with one coming from `V[K,p](ΓK)`.
  have hker :
      regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M ξ ∈
        LinearMap.ker
          (LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))) := by
    -- Reinterpret the already proved quotient vanishing as kernel membership.
    exact regular_fiber_tensor_quotient_image_eq_zero
      (A := A) (K := K) (G := G) (p := p) M ξ
  rw [show
        LinearMap.ker
            (LinearMap.lTensor M.1.asIdeal.ResidueField (Submodule.mkQ (V[K,p](ΓK)))) =
          LinearMap.range
            (LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype) by
        simpa using
          (lTensor_mkQ M.1.asIdeal.ResidueField (V[K,p](ΓK)))] at hker
  rcases hker with ⟨ζ, hζ⟩
  exact ⟨ζ, hζ⟩

/-- Helper for Exercise 12-12.7-8: once the transported fixed-fiber tensor has been written as a
tensor coming from `V[K,p](ΓK)`, vanishing of that `γ_p` tensor pulls back to vanishing of the
original fixed-fiber element. -/
private theorem regular_fiber_eq_zero_of_transport_witness_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    {ζ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK))}
    (hζ :
      LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype ζ =
        regular_fiber_to_tensorCharacterRingLinearEquiv
          (A := A) (K := K) (G := G) (p := p) M ξ)
    (hzero : ζ = 0) :
    ξ = 0 := by
  -- The transport equivalence is faithful, so it suffices to collapse the chosen `γ_p` witness.
  apply
    (regular_fiber_to_tensorCharacterRingLinearEquiv
      (A := A) (K := K) (G := G) (p := p) M).injective
  calc
    regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M ξ =
      LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype ζ := by
        exact hζ.symm
    _ = 0 := by
        simpa [hzero]

/-- Helper for Exercise 12-12.7-8: choose the prime-to-`p` scalar that annihilates the quotient
`R[K](G) / V[K,p](ΓK)` from Theorem `12-12.6-3`. This is the scalar used to build the explicit
base-change retraction on `k(M) ⊗ R[K](G)`. -/
private noncomputable def gammaP_tensor_annihilator_scalar
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) : ℕ :=
  Classical.choose
    (exists_coprime_scalar_smul_mem_gammaPElementaryInducedCharacterSpan
      (G := G) (L := L) (K := K) p)

/-- Helper for Exercise 12-12.7-8: the chosen annihilator scalar is coprime to the residue
characteristic `p`. This is exactly what later makes its image invertible in `k(M)`. -/
private theorem gammaP_tensor_annihilator_scalar_coprime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Nat.Coprime p (gammaP_tensor_annihilator_scalar
      (A := A) (K := K) (G := G) (L := L) M) :=
  (Classical.choose_spec
    (exists_coprime_scalar_smul_mem_gammaPElementaryInducedCharacterSpan
      (G := G) (L := L) (K := K) p)).1

/-- Helper for Exercise 12-12.7-8: the chosen annihilator scalar sends every character of
`R[K](G)` into LinearRepresentations_Serre_1977's subgroup `V[K,p](ΓK)`. This is the source-side linear retraction data
before tensoring with the residue field. -/
private theorem gammaP_tensor_annihilator_scalar_smul_mem
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (χ : R[K](G)) :
    gammaP_tensor_annihilator_scalar (A := A) (K := K) (G := G) (L := L) M • χ ∈
      V[K,p](ΓK) :=
  (Classical.choose_spec
    (exists_coprime_scalar_smul_mem_gammaPElementaryInducedCharacterSpan
      (G := G) (L := L) (K := K) p)).2 χ

/-- Helper for Exercise 12-12.7-8: the prime-to-`p` quotient annihilator gives a concrete
`ℤ`-linear map `R[K](G) → V[K,p](ΓK)` by multiplying with the chosen scalar. Tensoring this map
later produces the residue-field retraction promised by the source proof. -/
private noncomputable def gammaP_tensor_annihilator_to_gammaP
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    R[K](G) →ₗ[ℤ] V[K,p](ΓK) where
  toFun χ :=
    ⟨gammaP_tensor_annihilator_scalar (A := A) (K := K) (G := G) (L := L) M • χ,
      gammaP_tensor_annihilator_scalar_smul_mem
        (A := A) (K := K) (G := G) (L := L) M χ⟩
  map_add' χ ψ := by
    -- Multiplication by the fixed annihilator scalar is additive before and after restricting to
    -- the `γ_p` subgroup.
    apply Subtype.ext
    simp [smul_add]
  map_smul' n χ := by
    -- Over `ℤ`, the chosen annihilator commutes with every scalar, so the restriction remains
    -- linear.
    apply Subtype.ext
    simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 12-12.7-8: after tensoring with `k(M)`, the quotient annihilator becomes
an explicit linear retraction from `k(M) ⊗ R[K](G)` back to `k(M) ⊗ V[K,p](ΓK)`. -/
private noncomputable def gammaP_tensor_annihilator_lift
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    TensorProduct ℤ M.1.asIdeal.ResidueField (R[K](G)) →ₗ[M.1.asIdeal.ResidueField]
      TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK)) :=
  LinearMap.lTensor M.1.asIdeal.ResidueField
    (gammaP_tensor_annihilator_to_gammaP
      (A := A) (K := K) (G := G) (L := L) M)

/-- Helper for Exercise 12-12.7-8: composing the tensor inclusion
`k(M) ⊗ V[K,p](ΓK) → k(M) ⊗ R[K](G)` with the annihilator retraction multiplies by the chosen
prime-to-`p` scalar. This is the exact cokernel-control statement from the source route, now
packaged as an explicit composition identity. -/
private theorem gammaP_tensor_annihilator_lift_comp_subtype
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    (gammaP_tensor_annihilator_lift
        (A := A) (K := K) (G := G) (L := L) (p := p) M).comp
      (LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype) =
        ((gammaP_tensor_annihilator_scalar
            (A := A) (K := K) (G := G) (L := L) M :
              M.1.asIdeal.ResidueField) •
          LinearMap.id) := by
  ext ζ
  induction ζ using TensorProduct.induction_on with
  | zero =>
      simp [gammaP_tensor_annihilator_lift]
  | tmul a χ =>
      -- On a pure tensor, the two-step map is exactly multiplication by the annihilator scalar on
      -- the `V[K,p](ΓK)` factor.
      simp [gammaP_tensor_annihilator_lift, gammaP_tensor_annihilator_to_gammaP,
        TensorProduct.tmul_smul, LinearMap.id_apply]
  | add ζ η hζ hη =>
      -- Both tensor maps are linear, so the composition identity extends from pure tensors to
      -- arbitrary sums.
      simp [hζ, hη]

/-- Helper for Exercise 12-12.7-8: composing the annihilator retraction with the tensor inclusion
`k(M) ⊗ V[K,p](ΓK) → k(M) ⊗ R[K](G)` multiplies the ambient tensor by the same prime-to-`p`
scalar. This is the companion composition identity needed before inverting that scalar in the
residue field. -/
private theorem gammaP_subtype_comp_tensor_annihilator_lift
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    (LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype).comp
      (gammaP_tensor_annihilator_lift
        (A := A) (K := K) (G := G) (L := L) (p := p) M) =
        ((gammaP_tensor_annihilator_scalar
            (A := A) (K := K) (G := G) (L := L) M :
              M.1.asIdeal.ResidueField) •
          LinearMap.id) := by
  ext ζ
  induction ζ using TensorProduct.induction_on with
  | zero =>
      simp [gammaP_tensor_annihilator_lift]
  | tmul a χ =>
      -- On a pure tensor in the ambient owner, the retraction sends `χ` to the chosen multiple
      -- `N • χ`, so the composite is again scalar multiplication by `N`.
      simp [gammaP_tensor_annihilator_lift, gammaP_tensor_annihilator_to_gammaP,
        TensorProduct.tmul_smul, LinearMap.id_apply]
  | add ζ η hζ hη =>
      -- Linearity propagates the pure-tensor computation to arbitrary tensors.
      simp [hζ, hη]

/-- Helper for Exercise 12-12.7-8: the chosen annihilator scalar stays nonzero in the residue
field because it is coprime to the residue characteristic `p`. This is the invertibility input
for the base-change retraction. -/
private theorem gammaP_tensor_annihilator_scalar_ne_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    ((gammaP_tensor_annihilator_scalar
        (A := A) (K := K) (G := G) (L := L) M : ℕ) :
      M.1.asIdeal.ResidueField) ≠ 0 := by
  intro hN_zero
  have hN_dvd :
      (p : ℕ) ∣ gammaP_tensor_annihilator_scalar
        (A := A) (K := K) (G := G) (L := L) M :=
    (CharP.cast_eq_zero_iff M.1.asIdeal.ResidueField p
      (gammaP_tensor_annihilator_scalar
        (A := A) (K := K) (G := G) (L := L) M)).mp hN_zero
  exact
    ((p.2.coprime_iff_not_dvd).mp
      (gammaP_tensor_annihilator_scalar_coprime
        (A := A) (K := K) (G := G) (L := L) M)) hN_dvd

/-- Helper for Exercise 12-12.7-8: a transported `γ_p` tensor can be viewed again as a fixed-fiber
element by first including it into `k(M) ⊗ R[K](G)` and then applying the inverse transport
equivalence. This is the thin adapter needed before reusing LinearRepresentations_Serre_1977's existing fixed-fiber
evaluator. -/
private noncomputable def gammaP_tensor_to_regular_fiber
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK)) →ₗ[M.1.asIdeal.ResidueField]
      M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :=
  (regular_fiber_to_tensorCharacterRingLinearEquiv
    (A := A) (K := K) (G := G) (p := p) M).symm.toLinearMap.comp
    (LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype)

/-- Helper for Exercise 12-12.7-8: the transported `γ_p` tensor inherits a residue evaluator on
`p`-regular `Γ_K`-classes by passing through the fixed fiber and then applying LinearRepresentations_Serre_1977's canonical
evaluator. This packages the transport bridge without reopening the quotient argument. -/
private noncomputable def gammaP_tensor_residue_eval_family
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK)) →ₗ[M.1.asIdeal.ResidueField]
      (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) :=
  (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toLinearMap.comp
    (gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M)

/-- Helper for Exercise 12-12.7-8: if `ζ` transports to the fixed-fiber element `ξ`, then the
residue evaluator of `ζ` at an honest `p`-regular representative agrees with the already-defined
fixed-fiber evaluator of `ξ`. This is the exact transport rewrite needed to move the vanishing
hypothesis from `ξ` to the extracted `γ_p` witness. -/
private theorem regular_fiber_transport_pregular_eval_eq
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    {ζ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK))}
    (hζ :
      LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype ζ =
        regular_fiber_to_tensorCharacterRingLinearEquiv
          (A := A) (K := K) (G := G) (p := p) M ξ)
    (x : {x : G // IsPRegular p x}) :
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M ζ
        (pRegularGaloisPowerClassMk ΓK p x) =
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
        (pRegularGaloisPowerClassMk ΓK p x) := by
  have hfiber :
      gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M ζ = ξ := by
    -- Apply the faithful transport equivalence to turn the transported tensor equality back into
    -- an equality inside the fixed fiber.
    apply
      (regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M).injective
    simpa [gammaP_tensor_to_regular_fiber] using hζ
  -- Once the transport has been normalized, the residue-family evaluation is literally the
  -- fixed-fiber evaluation of `ξ`.
  simpa [gammaP_tensor_residue_eval_family, hfiber]

/-- Helper for Exercise 12-12.7-8: the transported `γ_p` evaluator is zero exactly when it
vanishes on every honest `p`-regular representative. This isolates the representative-to-quotient
descent bookkeeping from the remaining injectivity step. -/
private theorem gammaP_tensor_residue_eval_zero_iff_forall_representatives_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ζ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK))) :
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M ζ = 0 ↔
      ∀ x : {x : G // IsPRegular p x},
        gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M ζ
          (pRegularGaloisPowerClassMk ΓK p x) = 0 := by
  constructor
  · intro hzero x
    simpa [hzero]
  · intro hzero
    let ξ :=
      gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M ζ
    let gpre : PRegularConjClass G p → M.1.asIdeal.ResidueField :=
      (regular_fiber_prequotient_eval_family_algHom (A := A) (K := K) (G := G) M) ξ
    let hgpre :
        ∀ t : ΓK, ∀ c : PRegularConjClass G p, gpre (t • c) = gpre c :=
      regular_fiber_prequotient_eval_family_invariant
        (A := A) (K := K) (G := G) M ξ
    -- Rebuild the quotient function pointwise from its representative values.
    ext c
    have hc :
        pRegularGaloisPowerClassLift (K := K) (G := G) (p := p) gpre hgpre c = 0 := by
      refine
        (pRegularGaloisPowerClassLift_eq_zero_iff_forall_representatives_eq_zero
          (K := K) (G := G) (p := p) gpre hgpre c).mpr ?_
      intro x hx
      -- The representative-level hypothesis already gives the needed zero after unfolding the
      -- transported evaluator back to the prequotient family.
      simpa [gammaP_tensor_residue_eval_family, gammaP_tensor_to_regular_fiber, ξ, gpre, hgpre]
        using hzero x
    simpa [gammaP_tensor_residue_eval_family, gammaP_tensor_to_regular_fiber, ξ, gpre, hgpre]
      using hc

/-- Helper for Exercise 12-12.7-8: if the fixed-fiber evaluator of `ξ` vanishes everywhere, then
the transported `γ_p` witness also has zero residue evaluator. This is the exact vanishing bridge
needed before the final injectivity step on `k(M) ⊗ V[K,p](ΓK)`. -/
private theorem gammaP_tensor_residue_eval_eq_zero_of_eval_family_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    {ζ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK))}
    (hζ :
      LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype ζ =
        regular_fiber_to_tensorCharacterRingLinearEquiv
          (A := A) (K := K) (G := G) (p := p) M ξ)
    (hξ :
      ∀ c : PRegularGaloisPowerClass ΓK p,
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c = 0) :
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M ζ = 0 := by
  -- Descend the fixed-fiber vanishing hypothesis to representatives, then transport it to the
  -- extracted `γ_p` witness one representative at a time.
  refine
    (gammaP_tensor_residue_eval_zero_iff_forall_representatives_zero
      (A := A) (K := K) (G := G) (p := p) M ζ).mpr ?_
  intro x
  rw [regular_fiber_transport_pregular_eval_eq
    (A := A) (K := K) (G := G) (p := p) M ξ hζ x]
  exact hξ (pRegularGaloisPowerClassMk ΓK p x)

/-- Helper for Exercise 12-12.7-8: on a pure tensor, the transported `γ_p` residue evaluator is
linear in the residue-field coefficient, so the arbitrary pure-tensor case reduces to the
generator `1 ⊗ χ`. -/
private theorem gammaP_tensor_residue_eval_family_tmul
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (a : M.1.asIdeal.ResidueField)
    (χ : V[K,p](ΓK))
    (c : PRegularGaloisPowerClass ΓK p) :
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
        (a ⊗ₜ[ℤ] χ) c =
      a *
        gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
          ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) c := by
  -- Rewrite `a ⊗ χ` as `a • (1 ⊗ χ)` and then push the scalar through the linear evaluator.
  have htmul :
      (a ⊗ₜ[ℤ] χ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK))) =
        a • ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) := by
    simpa using (TensorProduct.smul_tmul' a (1 : M.1.asIdeal.ResidueField) χ).symm
  calc
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
        (a ⊗ₜ[ℤ] χ) c =
      gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
        (a • ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ)) c := by
          rw [htmul]
    _ =
      (a •
        gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
          ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ)) c := by
            rw [map_smul]
    _ =
      a *
        gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
          ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) c := by
            rfl

/-- Helper for Exercise 12-12.7-8: an honest element `χ ∈ V[K,p](ΓK)` also defines an owner
element of `A ⊗ R_K(G)` by viewing the same `K`-valued class function inside LinearRepresentations_Serre_1977's scalar
extension. This is the source object whose residue evaluation LinearRepresentations_Serre_1977 studies before base change. -/
private noncomputable def gammaP_owner_of_subtype
    (χ : V[K,p](ΓK)) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G :=
  -- The same virtual `K`-character belongs to the scalar extension `A ⊗ R_K(G)` because pure
  -- tensors `1 ⊗ χ` generate that owner.
  ⟨((V[K,p](ΓK)).subtype χ : G → K),
    mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
      (A := A) (K := K) (G := G) χ.2⟩

/-- Helper for Exercise 12-12.7-8: on the source generator `χ ∈ V[K,p](ΓK)`, LinearRepresentations_Serre_1977's residue
evaluator is obtained by evaluating the corresponding owner element on `p`-regular conjugacy
classes and then descending to `Γ_K`-classes. This is the pre-base-change map that the tensor
evaluator should agree with on `1 ⊗ χ`. -/
private noncomputable def gammaP_pregular_residue_eval
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (χ : V[K,p](ΓK)) :
    PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField :=
  -- Route correction: package the source evaluator directly on `χ`, rather than continuing to
  -- hide it behind the transported tensor map.
  pRegularGaloisPowerClassLift (K := K) (G := G) (p := p)
    (owner_pregular_residue_eval_of_isIntegralClosure
      (A := A) (K := K) (G := G) (p := p) M
      (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ))
    (owner_pregular_residue_eval_of_isIntegralClosure_invariant
      (A := A) (K := K) (G := G) (p := p) M
      (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ))

/-- Helper for Exercise 12-12.7-8: the owner-side tensor corresponding to `χ ∈ V[K,p](ΓK)` is
exactly the pure tensor `1 ⊗ χ` in `A ⊗ R_K(G)`. This identifies the source owner with the
generator used by the base-change map. -/
private theorem ownerLinearEquiv_tensorCharacterRing_gammaP_owner_of_subtype
    (χ : V[K,p](ΓK)) :
    ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)
      (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ) =
        (1 : A) ⊗ₜ[ℤ] ((V[K,p](ΓK)).subtype χ : R[K](G)) := by
  -- Compare the two ambient tensors through their common realization as the same `K`-valued
  -- function on `G`.
  apply tensorCharacterRingRealization_injective (A := A) (K := K) (G := G)
  calc
    tensorCharacterRingRealization (A := A) (K := K) (G := G)
        (ownerLinearEquiv_tensorCharacterRing (A := A) (K := K) (G := G)
          (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ)) =
      ((gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ :
          characterRingOverFieldAlgebraScalarExtension A K G) : G → K) := by
            simpa using
              tensorCharacterRingRealization_ownerLinearEquiv_apply
                (A := A) (K := K) (G := G)
                (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ)
    _ = ((V[K,p](ΓK)).subtype χ : G → K) := rfl
    _ =
      tensorCharacterRingRealization (A := A) (K := K) (G := G)
        ((1 : A) ⊗ₜ[ℤ] ((V[K,p](ΓK)).subtype χ : R[K](G))) := by
          ext g
          simp [tensorCharacterRingRealization_apply_tmul]

/-- Helper for Exercise 12-12.7-8: transporting the generator `1 ⊗ χ` from
`k(M) ⊗ V[K,p](ΓK)` into the fixed fiber is the same as transporting the `includeRight` image of
the corresponding source owner. This is the transport identity needed to compare the tensor and
source residue evaluators on generators. -/
private theorem gammaP_tensor_one_tmul_transport_eq_includeRight
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (χ : V[K,p](ΓK)) :
    LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype
        ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) =
      regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
          (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ)) := by
  -- First rewrite the transported owner via `ownerLinearEquiv_tensorCharacterRing`, then
  -- normalize the associativity transport to the pure tensor `1 ⊗ χ`.
  calc
    LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype
        ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) =
      (1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] ((V[K,p](ΓK)).subtype χ : R[K](G)) := by
        simp [LinearMap.lTensor_tmul]
    _ =
      regular_fiber_to_tensorCharacterRingLinearEquiv
        (A := A) (K := K) (G := G) (p := p) M
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
          (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ)) := by
            rw [regular_fiber_to_tensorCharacterRingLinearEquiv_includeRight_formula]
            rw [ownerLinearEquiv_tensorCharacterRing_gammaP_owner_of_subtype
              (A := A) (K := K) (G := G) (p := p) χ]
            symm
            simpa using
              fiber_linearEquiv_tensorCharacterRingOverField_baseChange_tmul_tmul
                (A := A) (K := K) (G := G) (F := M.1.asIdeal.ResidueField)
                (a := (1 : M.1.asIdeal.ResidueField)) (b := (1 : A))
                (((V[K,p](ΓK)).subtype χ : R[K](G)))

/-- Helper for Exercise 12-12.7-8: on the generator `1 ⊗ χ`, the transported tensor evaluator is
exactly LinearRepresentations_Serre_1977's source residue evaluator on the corresponding `γ_p` character `χ`. This closes
the transport mismatch and leaves only the source kernel theorem as the remaining frontier. -/
private theorem gammaP_tensor_residue_eval_family_one_tmul_eq_source
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (χ : V[K,p](ΓK)) :
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
        ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) =
      gammaP_pregular_residue_eval (A := A) (K := K) (G := G) (p := p) M χ := by
  -- Evaluate both sides on honest `p`-regular representatives, then use the transport identity
  -- above to reduce the tensor side to the source owner evaluator.
  apply pRegularGaloisPowerClass_funext (K := K) (G := G) (p := p)
  intro x
  rw [regular_fiber_transport_pregular_eval_eq
    (A := A) (K := K) (G := G) (p := p) M
    ((Algebra.TensorProduct.includeRight
      (R := A) (A := M.1.asIdeal.ResidueField)
      (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
      (gammaP_owner_of_subtype (A := A) (K := K) (G := G) (p := p) χ))
    (gammaP_tensor_one_tmul_transport_eq_includeRight
      (A := A) (K := K) (G := G) (p := p) M χ) x]
  -- Once the tensor transport is normalized, both sides are literally the same quotient descent
  -- of the owner-side residue evaluator.
  simp [gammaP_pregular_residue_eval, regular_fiber_eval_family_algHom_mk]

/-- Helper for Exercise 12-12.7-8: once the residue-field coefficient is nonzero, vanishing of
the transported evaluator on `a ⊗ χ` is equivalent to vanishing on the generator `1 ⊗ χ`. This
isolates the only source-sized kernel step still missing from the tensor-side argument. -/
private theorem gammaP_tensor_residue_eval_family_tmul_eq_zero_iff_of_ne_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a : M.1.asIdeal.ResidueField}
    (ha : a ≠ 0)
    (χ : V[K,p](ΓK)) :
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
        (a ⊗ₜ[ℤ] χ) = 0 ↔
      gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
        ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ) = 0 := by
  constructor
  · intro hzero
    -- Normalize the zero function to representatives and cancel the nonzero scalar coefficient.
    refine
      (gammaP_tensor_residue_eval_zero_iff_forall_representatives_zero
        (A := A) (K := K) (G := G) (p := p) M
        ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ)).mpr ?_
    intro x
    have hx :
        gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
            (a ⊗ₜ[ℤ] χ) (pRegularGaloisPowerClassMk ΓK p x) = 0 := by
      simpa [hzero]
    rw [gammaP_tensor_residue_eval_family_tmul
      (A := A) (K := K) (G := G) (p := p) M a χ
      (pRegularGaloisPowerClassMk ΓK p x)] at hx
    exact (mul_eq_zero.mp hx).resolve_left ha
  · intro hzero
    -- Conversely, the scalar-linear pure-tensor formula immediately rebuilds the vanishing of
    -- `a ⊗ χ`.
    refine
      (gammaP_tensor_residue_eval_zero_iff_forall_representatives_zero
        (A := A) (K := K) (G := G) (p := p) M
        (a ⊗ₜ[ℤ] χ)).mpr ?_
    intro x
    rw [gammaP_tensor_residue_eval_family_tmul
      (A := A) (K := K) (G := G) (p := p) M a χ
      (pRegularGaloisPowerClassMk ΓK p x)]
    have hx :
        gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
            ((1 : M.1.asIdeal.ResidueField) ⊗ₜ[ℤ] χ)
            (pRegularGaloisPowerClassMk ΓK p x) = 0 := by
      simpa [hzero]
    simp [hx]

/-- Helper for Exercise 12-12.7-8: the transport map
`k(M) ⊗ V[K,p](ΓK) → M.Fiber (A ⊗ R_K(G))` is injective because the explicit annihilator
retraction multiplies tensor-domain elements by a nonzero scalar. This records the faithful half
of LinearRepresentations_Serre_1977's transport route before the modular-character kernel step is applied. -/
private theorem gammaP_tensor_to_regular_fiber_injective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Injective (gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M) := by
  intro ζ η hζη
  have htransport :
      LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype ζ =
        LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype η := by
    -- Apply the fiber-to-owner equivalence so equality in the fixed fiber becomes equality in
    -- the ambient tensor `k(M) ⊗ R_K(G)`.
    have h :=
      congrArg
        (regular_fiber_to_tensorCharacterRingLinearEquiv
          (A := A) (K := K) (G := G) (p := p) M)
        hζη
    simpa [gammaP_tensor_to_regular_fiber] using h
  have hsub_zero :
      LinearMap.lTensor M.1.asIdeal.ResidueField (V[K,p](ΓK)).subtype (ζ - η) = 0 := by
    simpa [LinearMap.map_sub, htransport]
  have hscaled_zero :
      ((gammaP_tensor_annihilator_scalar
          (A := A) (K := K) (G := G) (L := L) M :
            M.1.asIdeal.ResidueField) • (ζ - η)) = 0 := by
    -- The annihilator retraction turns the inclusion into multiplication by the fixed
    -- prime-to-`p` scalar, so vanishing after inclusion forces a scalar multiple of `ζ - η`
    -- to vanish.
    have h :=
      congrArg
        (gammaP_tensor_annihilator_lift
          (A := A) (K := K) (G := G) (L := L) (p := p) M)
        hsub_zero
    simpa [LinearMap.comp_apply, gammaP_tensor_annihilator_lift_comp_subtype,
      LinearMap.smul_apply, LinearMap.id_apply] using h
  have hsub :
      ζ - η = 0 :=
    (smul_eq_zero.mp hscaled_zero).resolve_left
      (gammaP_tensor_annihilator_scalar_ne_zero
        (A := A) (K := K) (G := G) (L := L) (p := p) M)
  exact sub_eq_zero.mp hsub

/-- Helper for Exercise 12-12.7-8: every fixed-fiber element comes from a transported
`γ_p`-tensor. This packages the quotient-killing transport already proved earlier as surjectivity
of `gammaP_tensor_to_regular_fiber`. -/
private theorem gammaP_tensor_to_regular_fiber_surjective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Surjective (gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M) := by
  intro ξ
  obtain ⟨ζ, hζ⟩ :=
    regular_fiber_transport_mem_gammaP_tensor_image
      (A := A) (K := K) (G := G) (p := p) M ξ
  refine ⟨ζ, ?_⟩
  -- Undo the faithful transport equivalence to identify the chosen tensor preimage with `ξ`.
  apply
    (regular_fiber_to_tensorCharacterRingLinearEquiv
      (A := A) (K := K) (G := G) (p := p) M).injective
  simpa [gammaP_tensor_to_regular_fiber] using hζ

/-- Helper for Exercise 12-12.7-8: choose for each `p`-regular `Γ_K`-class the tensor-side
preimage of LinearRepresentations_Serre_1977's normalized fixed-fiber separator. This is the explicit separator section on
`k(M) ⊗ V[K,p](ΓK)` prescribed by the source route. -/
private noncomputable def gammaP_tensor_separator_preimage
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK)) :=
  Classical.choose
    (gammaP_tensor_to_regular_fiber_surjective
      (A := A) (K := K) (G := G) (p := p) M
      (normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c))

/-- Helper for Exercise 12-12.7-8: the chosen tensor-side separator preimage transports back to
the normalized fixed-fiber separator it was chosen from. This is the bridge used to read off the
delta-function evaluation formula on the tensor side. -/
private theorem gammaP_tensor_separator_preimage_to_regular_fiber
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M
        (gammaP_tensor_separator_preimage (A := A) (K := K) (G := G) (p := p) M c) =
      normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c :=
  Classical.choose_spec
    (gammaP_tensor_to_regular_fiber_surjective
      (A := A) (K := K) (G := G) (p := p) M
      (normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c))

/-- Helper for Exercise 12-12.7-8: the tensor-side separator preimage evaluates as the delta
function at the chosen class `c`. This is the explicit tensor-domain separator identity needed
before the remaining kernel argument. -/
private theorem gammaP_tensor_separator_preimage_apply
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c d : PRegularGaloisPowerClass ΓK p) :
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M
        (gammaP_tensor_separator_preimage (A := A) (K := K) (G := G) (p := p) M c) d =
      if c = d then 1 else 0 := by
  -- Transport the chosen tensor separator back to the fixed fiber, where the normalized
  -- separator already has the required delta-function values.
  rw [gammaP_tensor_residue_eval_family]
  simp [gammaP_tensor_separator_preimage_to_regular_fiber,
    normalized_regular_fiber_separator_apply]

/-- Helper for Exercise 12-12.7-8: summing the tensor-side separator preimages with prescribed
coefficients reconstructs any residue-field-valued function on `p`-regular `Γ_K`-classes. This
closes the separator half of the modular-character theorem directly on the tensor domain. -/
private theorem gammaP_tensor_residue_eval_family_surjective_from_separators
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Surjective
      (gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M) := by
  classical
  intro ψ
  let ζ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK)) :=
    ∑ c : PRegularGaloisPowerClass ΓK p,
      ψ c • gammaP_tensor_separator_preimage (A := A) (K := K) (G := G) (p := p) M c
  refine ⟨ζ, ?_⟩
  -- The separator preimages are delta functions under evaluation, so their coefficient sum
  -- reproduces `ψ` pointwise.
  ext d
  calc
    gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M ζ d =
      ∑ c : PRegularGaloisPowerClass ΓK p,
        ψ c *
          (gammaP_tensor_residue_eval_family
            (A := A) (K := K) (G := G) (p := p) M
            (gammaP_tensor_separator_preimage
              (A := A) (K := K) (G := G) (p := p) M c)) d := by
        simp [ζ, map_sum]
    _ =
      ∑ c : PRegularGaloisPowerClass ΓK p, if c = d then ψ c else 0 := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        by_cases hcd : c = d
        · simp [gammaP_tensor_separator_preimage_apply, hcd]
        · simp [gammaP_tensor_separator_preimage_apply, hcd]
    _ = ψ d := by
        simpa using
          (Finset.sum_ite_eq (s := Finset.univ) d
            (fun c : PRegularGaloisPowerClass ΓK p ↦ ψ c))

/-- Helper for Exercise 12-12.7-8: injectivity of the transported `γ_p` residue evaluator is the
remaining structural step needed to close LinearRepresentations_Serre_1977's fixed-fiber kernel argument. Mathematically,
this is the modular-character injectivity statement on `k(M) ⊗ V[K,p](ΓK)`. -/
private theorem gammaP_tensor_residue_eval_injective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ζ : TensorProduct ℤ M.1.asIdeal.ResidueField (V[K,p](ΓK)))
    (hzero :
      gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M ζ = 0) :
    ζ = 0 := by
  let ξ :=
    gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M ζ
  have hξ_zero :
      ∀ c : PRegularGaloisPowerClass ΓK p,
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c = 0 := by
    intro c
    -- Unfold the transport definition once: the fixed-fiber evaluation of `ξ` is exactly the
    -- tensor-side residue evaluation of `ζ`.
    exact congrArg (fun f ↦ f c) (by simpa [gammaP_tensor_residue_eval_family, ξ] using hzero)
  -- Route correction: the false `ℤ`-injective source evaluator has been removed. The remaining
  -- frontier is now the genuine tensor-side modular-character theorem: show that the transported
  -- fixed-fiber element `ξ` with zero class evaluations must itself vanish.
  have hξ_eq_zero : ξ = 0 := by
    -- TODO: use the tensor-side separator preimages and LinearRepresentations_Serre_1977's auxiliary witness with
    -- nowhere-zero residues to prove the kernel statement on `k(M) ⊗ V[K,p](ΓK)`.
    sorry
  have hmap_zero :
      gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M ζ =
        gammaP_tensor_to_regular_fiber (A := A) (K := K) (G := G) (p := p) M 0 := by
    simpa [gammaP_tensor_to_regular_fiber, ξ] using hξ_eq_zero
  exact
    (gammaP_tensor_to_regular_fiber_injective
      (A := A) (K := K) (G := G) (p := p) M) hmap_zero

/-- Helper for Exercise 12-12.7-8: once every coordinate of LinearRepresentations_Serre_1977's fixed-fiber evaluator
vanishes, the fixed-fiber element itself should be zero. This isolates the remaining
source-faithful quotient-killing step from the later injectivity wrapper. -/
private theorem regular_fiber_eq_zero_of_eval_family_zero
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
    (hξ :
      ∀ c : PRegularGaloisPowerClass ΓK p,
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c = 0) :
    ξ = 0 := by
  -- Route correction: the source proof now passes through the extracted `γ_p` witness itself.
  -- After transport, the fixed-fiber vanishing hypothesis is converted directly into vanishing of
  -- the transported `γ_p` residue evaluator, isolating the remaining modular-character
  -- injectivity step on `k(M) ⊗ V[K,p](ΓK)`.
  obtain ⟨ζ, hζ⟩ :=
    regular_fiber_transport_mem_gammaP_tensor_image
      (A := A) (K := K) (G := G) (p := p) M ξ
  have hζ_zero : ζ = 0 := by
    have hgamma_zero :
        gammaP_tensor_residue_eval_family (A := A) (K := K) (G := G) (p := p) M ζ = 0 :=
      gammaP_tensor_residue_eval_eq_zero_of_eval_family_zero
        (A := A) (K := K) (G := G) (p := p) M ξ hζ hξ
    -- The remaining source-faithful gap is now isolated as injectivity of the transported
    -- `γ_p` residue evaluator on `k(M) ⊗ V[K,p](ΓK)`.
    exact
      gammaP_tensor_residue_eval_injective
        (A := A) (K := K) (G := G) (p := p) M ζ hgamma_zero
  -- Once the transported `γ_p` witness vanishes, the fixed-fiber element itself vanishes by the
  -- transport equivalence.
  exact
    regular_fiber_eq_zero_of_transport_witness_zero
      (A := A) (K := K) (G := G) (p := p) M ξ hζ hζ_zero

/-- Helper for Exercise 12-12.7-8: the only missing step in the fixed-fiber route is injectivity
of LinearRepresentations_Serre_1977's evaluator on the fiber over `M`. -/
private theorem regular_fiber_eval_family_injective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Injective (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M) := by
  intro ξ η hξη
  -- Route correction: reduce injectivity to the kernel statement for `ξ - η`, so the remaining
  -- source work is concentrated entirely in the quotient-killing lemma above.
  have hdiff :
      ∀ c : PRegularGaloisPowerClass ΓK p,
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M (ξ - η)) c = 0 := by
    intro c
    have hsub :
        regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M (ξ - η) =
          regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ -
            regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M η := by
      simpa using
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).map_sub ξ η
    have hzero :
        regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ -
          regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M η = 0 := by
      rw [hξη, sub_self]
    exact by simpa [hsub] using congrArg (fun f ↦ f c) hzero
  have hkernel :
      ξ - η = 0 :=
    regular_fiber_eq_zero_of_eval_family_zero
      (A := A) (K := K) (G := G) M (ξ - η) hdiff
  exact sub_eq_zero.mp hkernel

/-- Helper for Exercise 12-12.7-8: the fixed fiber over a nonzero residual-characteristic maximal
ideal `M` should be identified with the function ring on the `p`-regular `Γ_K`-classes. This is
the remaining fiber-equivalence owner from LinearRepresentations_Serre_1977's source route. -/
private noncomputable def fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) :=
  -- The fixed-fiber equivalence is exactly the evaluator, once its kernel has been shown to be
  -- trivial by LinearRepresentations_Serre_1977's quotient-killing argument.
  fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions_of_injective
    (A := A) (K := K) (G := G) M
    (regular_fiber_eval_family_injective (A := A) (K := K) (G := G) M)

/-- Helper for Exercise 12-12.7-8: for each fixed residual-characteristic maximal ideal `M` and
`p`-regular `Γ_K`-class `c`, LinearRepresentations_Serre_1977's source route should produce a prime of `A ⊗ R_K(G)`
satisfying the intrinsic regular-prime predicate. -/
private theorem exists_regular_prime_for_fixed_class
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    ∃ P : SpecAKG, IsGaloisPowerClassScalarExtensionRegularPrime K M c P := by
  let φ :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G →+*
        M.1.asIdeal.ResidueField :=
    (Pi.evalRingHom
      (fun _ : PRegularGaloisPowerClass ΓK p ↦ M.1.asIdeal.ResidueField) c).comp
      ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom.comp
        ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)).toRingHom))
  let P : SpecAKG := ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · -- The coordinate-kernel prime contracts to `M` because scalars from `A` evaluate to their
    -- residue classes in `M.1.asIdeal.ResidueField`.
    ext a
    change φ (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a) =
        0 ↔ a ∈ M.1.asIdeal
    simpa [φ] using (Ideal.algebraMap_residueField_eq_zero (I := M.1.asIdeal) (x := a))
  · -- On owner generators, membership in the coordinate kernel is exactly LinearRepresentations_Serre_1977's residue test
    -- for the chosen `p`-regular `Γ_K`-class `c`.
    intro f
    change φ f = 0 ↔
      ∀ x : {x : G // IsPRegular p x},
        pRegularGaloisPowerClassMk ΓK p x = c →
          ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    simpa [φ] using
      (regular_fiber_eval_family_includeRight_zero_iff
        (A := A) (K := K) (G := G) (p := p) M c f)

/-- Helper for Exercise 12-12.7-8: the regular prime `P_{M,c}` attached to a nonzero maximal
ideal `M` of residual characteristic `p` and a `p`-regular `Γ_K`-class `c`. -/
noncomputable def galoisPowerClassScalarExtensionRegularPrime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) : SpecAKG :=
  Classical.choose (exists_regular_prime_for_fixed_class (A := A) (K := K) (G := G) M c)

/-- Helper for Exercise 12-12.7-8: the regular prime `P_{M,c}` satisfies LinearRepresentations_Serre_1977's intrinsic
regular-prime criterion. -/
theorem galoisPowerClassScalarExtensionRegularPrime_spec
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    IsGaloisPowerClassScalarExtensionRegularPrime K M c
      (galoisPowerClassScalarExtensionRegularPrime K M c) := by
  -- The owner prime was chosen precisely from the existence statement for the fixed class `c`.
  exact Classical.choose_spec
    (exists_regular_prime_for_fixed_class (A := A) (K := K) (G := G) M c)

/-- Helper for Exercise 12-12.7-8: LinearRepresentations_Serre_1977's intrinsic regular-prime predicate determines
`P_{M,c}` uniquely. -/
theorem
    eq_galoisPowerClassScalarExtensionRegularPrime_of_isGaloisPowerClassScalarExtensionRegularPrime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) {P : SpecAKG}
    (hP : IsGaloisPowerClassScalarExtensionRegularPrime K M c P) :
    P = galoisPowerClassScalarExtensionRegularPrime K M c := by
  -- LinearRepresentations_Serre_1977's intrinsic criterion determines the prime by its membership test on every owner
  -- element `f`.
  apply PrimeSpectrum.ext
  ext f
  exact (hP.2 f).trans
    ((galoisPowerClassScalarExtensionRegularPrime_spec (A := A) (K := K) (G := G) M c).2 f).symm

/-- Helper for Exercise 12-12.7-8: once a prime over a fixed maximal ideal `M` is known to
satisfy LinearRepresentations_Serre_1977's intrinsic regular-prime predicate for some class `c`, it must already be the
chosen indexed prime `P_{M,c}`. -/
private theorem exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_exists_intrinsic_witness
    {p : Nat.Primes} (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : SpecAKG}
    (h𝔭 :
      ∃ c : PRegularGaloisPowerClass ΓK p,
        IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  rcases h𝔭 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  -- The chosen prime `P_{M,c}` is characterized uniquely by the intrinsic regular-prime
  -- predicate, so any other witness with the same data must coincide with it.
  symm
  exact
    eq_galoisPowerClassScalarExtensionRegularPrime_of_isGaloisPowerClassScalarExtensionRegularPrime
      (A := A) (K := K) (G := G) M c hc

end RegularPrime

/-- Helper for Exercise 12-12.7-8: any nonzero prime of the coefficient ring `A` is some
residual-characteristic maximal ideal. This is the coefficient-ring split for the nonzero branch
of the spectrum classification. -/
private theorem nonzero_primeSpectrum_eq_residual_maximal_local
    (q : PrimeSpectrum A) (hq : q.asIdeal ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
      M.1.asIdeal = q.asIdeal := by
  -- A nonzero prime is maximal because every nonzero quotient of `A` is finite.
  letI : q.asIdeal.IsMaximal :=
    Ring.HasFiniteQuotients.maximalOfPrime hq
  have hfiniteQuot : Finite (A ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient hq
  letI : Finite (A ⧸ q.asIdeal) := hfiniteQuot
  -- Its residue field is finite, hence has prime characteristic.
  have hfiniteResidue : Finite q.asIdeal.ResidueField := by
    exact Finite.of_surjective
      (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).surjective
  letI : Finite q.asIdeal.ResidueField := hfiniteResidue
  let p : Nat.Primes :=
    ⟨ringChar q.asIdeal.ResidueField, CharP.prime_ringChar q.asIdeal.ResidueField⟩
  let M : NonzeroResidualCharacteristicMaximalIdeal A p :=
    ⟨⟨q.asIdeal, inferInstance⟩, hq, by
      simpa [p] using
        (inferInstance : CharP q.asIdeal.ResidueField (ringChar q.asIdeal.ResidueField))⟩
  -- The packaged maximal ideal is definitionally the original prime.
  exact ⟨p, M, rfl⟩

/-- Helper for Exercise 12-12.7-8: under the canonical fixed-fiber equivalence, the transported
coordinate prime is exactly LinearRepresentations_Serre_1977's intrinsic regular prime for the chosen class `c`. -/
private theorem regular_fiber_coordinate_prime_is_regularPrime
    {p : Nat.Primes} (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    IsGaloisPowerClassScalarExtensionRegularPrime K M c
      (regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M
        (fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions
          (A := A) (K := K) (G := G) M) c) := by
  let e :=
    fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions
      (A := A) (K := K) (G := G) M
  change IsGaloisPowerClassScalarExtensionRegularPrime K M c
    (regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M e c)
  have hmem :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        f ∈ (regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M e c).asIdeal ↔
          ∀ x : {x : G // IsPRegular p x},
            pRegularGaloisPowerClassMk ΓK p x = c →
              ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
    intro f
    -- Unfold the coordinate prime until membership is the vanishing of the corresponding
    -- fixed-fiber coordinate, then compare that coordinate with LinearRepresentations_Serre_1977's residue criterion.
    change
      (Algebra.TensorProduct.includeRight
        (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) f) ∈
          (((PrimeSpectrum.comapEquiv e.toRingEquiv).symm
            (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c)).asIdeal) ↔
        ∀ x : {x : G // IsPRegular p x},
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    change
      (Algebra.TensorProduct.includeRight
        (R := A) (A := M.1.asIdeal.ResidueField)
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) f) ∈
          Ideal.comap e.toRingHom
            ((regular_fiber_eval_prime (A := A) (K := K) (G := G) M c).asIdeal) ↔
        ∀ x : {x : G // IsPRegular p x},
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    change
      e ((Algebra.TensorProduct.includeRight
          (R := A) (A := M.1.asIdeal.ResidueField)
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f) ∈
          (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c).asIdeal ↔
        ∀ x : {x : G // IsPRegular p x},
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    change
      (e ((Algebra.TensorProduct.includeRight
            (R := A) (A := M.1.asIdeal.ResidueField)
            (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f)) c = 0 ↔
        ∀ x : {x : G // IsPRegular p x},
          pRegularGaloisPowerClassMk ΓK p x = c →
            ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1
    simpa [e, fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions,
      fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions_of_injective,
      regular_fiber_eval_prime, RingHom.mem_ker, RingHom.comp_apply] using
      (regular_fiber_eval_family_includeRight_zero_iff
        (A := A) (K := K) (G := G) (p := p) M c f)
  refine ⟨?_, ?_⟩
  · -- Scalar membership in the transported coordinate prime recovers exactly the fixed maximal
    -- ideal `M`.
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx⟩ := pRegularGaloisPowerClassMk_surjective (G := G) ΓK p c
      rcases (hmem (algebraMap A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a)).1 ha x hx with
        ⟨b, hb⟩
      have hba : b.1 = a := by
        apply (IsFractionRing.injective A K)
        change algebraMap A K b.1 = algebraMap A K a
        simpa using hb
      simpa [hba] using b.2
    · intro ha
      refine (hmem (algebraMap A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a)).2 ?_
      intro x hx
      refine ⟨⟨a, ha⟩, ?_⟩
      change algebraMap A K a = algebraMap A K a
      rfl
  · -- The same unfolded membership test is LinearRepresentations_Serre_1977's intrinsic residue criterion for the class `c`.
    intro f
    exact hmem f

/-- Helper for Exercise 12-12.7-8: a prime of `A ⊗ R_K(G)` lying over a fixed nonzero maximal
ideal `M` should be one of the indexed regular primes `P_{M,c}`. This is the remaining
classification step in the nonzero branch. -/
private theorem exists_intrinsic_regularPrime_of_comap_eq_fixed_maximal
    {p : Nat.Primes} (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭 := by
  let e :=
    fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions
      (A := A) (K := K) (G := G) M
  have hclass :
      ∀ q :
        PrimeSpectrum
          (M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)),
        ∃ c : PRegularGaloisPowerClass ΓK p,
          IsGaloisPowerClassScalarExtensionRegularPrime K M c
            (regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M q) := by
    intro q
    -- Every prime of the transported function ring is a coordinate prime, so transport the
    -- canonical coordinate witness back from the fiber to the ambient spectrum.
    obtain ⟨c, hc⟩ :=
      regular_fiber_lift_surjective (A := A) (K := K) (G := G) M e q
    refine ⟨c, ?_⟩
    simpa [e, regular_fiber_coordinate_prime, hc] using
      (regular_fiber_coordinate_prime_is_regularPrime
        (A := A) (K := K) (G := G) M c)
  -- With the canonical coordinate witnesses available on the fiber, the existing transport API
  -- packages the fixed-maximal classification back in `Spec (A ⊗ R_K(G))`.
  exact
    exists_isGaloisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal_of_regularFiberClassification
      (A := A) (K := K) (G := G) M hclass h𝔭

/-- Helper for Exercise 12-12.7-8: a prime of `A ⊗ R_K(G)` lying over a fixed nonzero maximal
ideal `M` is equal to the chosen indexed regular prime once the intrinsic witness has been
transported back from the regular fiber. -/
private theorem exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal
    {p : Nat.Primes} (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  -- Once the fixed-fiber classification has produced the intrinsic witness, uniqueness of
  -- LinearRepresentations_Serre_1977's regular-prime predicate identifies `𝔭` with the chosen indexed prime.
  exact
    exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_exists_intrinsic_witness
      (A := A) (K := K) (G := G) M
      (exists_intrinsic_regularPrime_of_comap_eq_fixed_maximal
        (A := A) (K := K) (G := G) M h𝔭)

/-- Helper for Exercise 12-12.7-8: a prime whose contraction to `A` is zero should be one of the
zero-residual primes `P₀,c`. This is the remaining bottom-fiber classification step. -/
private theorem exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot_local
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    ∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭 := by
  -- Route correction: the zero branch is now delegated to the canonical bottom-fiber
  -- classification module, so this local theorem is only the source-facing adapter.
  exact
    exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot
      (A := A) (K := K) (G := G) h𝔭

/-- The canonical indexing map sending a `Γ_K`-class `c` to `P₀,c` and a regular-prime index
`⟨p, M, c⟩` to `P_{M,c}`. -/
noncomputable abbrev galoisPowerClassScalarExtensionPrimeIdealAssociation :
    GaloisPowerClass ΓK ⊕ RegularPrimeIndex → SpecAKG :=
  Sum.elim (galoisPowerClassScalarExtensionZeroPrimeIdeal K)
    (fun i ↦
      match i with
      | ⟨_, M, c⟩ => galoisPowerClassScalarExtensionRegularPrime K M c)

local notation "primeIdealAssociation" =>
  (galoisPowerClassScalarExtensionPrimeIdealAssociation K :
    GaloisPowerClass ΓK ⊕ RegularPrimeIndex → SpecAKG)

/-- Exercise 12-12.7-8: in the arithmetic setting where `K` is the fraction field of the domain
`A`, every prime of `A ⊗ R_K(G)` is either one of the zero-residual primes `P₀,c` indexed by
`Γ_K`-classes or one of the regular primes `P_{M,c}` indexed by residual-characteristic maximal
ideals and `p`-regular `Γ_K`-classes. -/
theorem galoisPowerClassScalarExtensionPrimeIdealClassification
    (𝔭 : SpecAKG) :
    (∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭) ∨
      ∃ (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
        (c : PRegularGaloisPowerClass ΓK p),
        galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  by_cases h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥
  · -- The zero-contraction branch is already handled by the transported bottom-fiber
    -- classification.
    exact Or.inl <|
      exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot_local
        (A := A) (K := K) (G := G) h𝔭
  · -- Otherwise the contracted prime of `A` is nonzero, hence a residual-characteristic maximal
    -- ideal; then the remaining fixed-fiber step should classify `𝔭`.
    let q : PrimeSpectrum A :=
      PrimeSpectrum.comap
        (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) 𝔭
    have hq : q.asIdeal ≠ ⊥ := by
      simpa [q] using h𝔭
    obtain ⟨p, M, hM⟩ :=
      nonzero_primeSpectrum_eq_residual_maximal_local (A := A) q hq
    have hcontract :
        Ideal.comap
            (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
            𝔭.asIdeal = M.1.asIdeal := by
      simpa [q] using hM.symm
    obtain ⟨c, hc⟩ :=
      exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal
        (A := A) (K := K) (G := G) M hcontract
    exact Or.inr ⟨p, M, c, hc⟩

/-- Companion bridge for Exercise 12-12.7-8: surjectivity of the canonical indexing map is
equivalent to the explicit source-facing spectrum classification theorem. -/
theorem galoisPowerClassScalarExtensionPrimeIdealAssociation_surjective_iff :
    Function.Surjective primeIdealAssociation ↔
      ∀ 𝔭 : SpecAKG,
        (∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭) ∨
          ∃ (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
            (c : PRegularGaloisPowerClass ΓK p),
            galoisPowerClassScalarExtensionRegularPrime K M c = 𝔭 := by
  constructor
  · intro hsurj 𝔭
    obtain ⟨i, hi⟩ := hsurj 𝔭
    cases i with
    | inl c =>
        exact Or.inl ⟨c, hi⟩
    | inr i =>
        cases i with
        | mk p i =>
            cases i with
            | mk M c =>
                exact Or.inr ⟨p, M, c, hi⟩
  · intro hclass 𝔭
    rcases hclass 𝔭 with ⟨c, hc⟩ | ⟨p, M, c, hc⟩
    · exact ⟨Sum.inl c, hc⟩
    · exact ⟨Sum.inr ⟨p, M, c⟩, hc⟩

/-- Exercise 12-12.7-8, surjective indexing-map form: the canonical indexing map from the
disjoint union of the zero family and the regular family onto `Spec (A ⊗ R_K(G))` is surjective.
-/
theorem galoisPowerClassScalarExtensionPrimeIdealAssociation_surjective :
    Function.Surjective primeIdealAssociation := by
  rw [galoisPowerClassScalarExtensionPrimeIdealAssociation_surjective_iff]
  exact galoisPowerClassScalarExtensionPrimeIdealClassification (A := A) (K := K) (G := G)

end

end Representation
