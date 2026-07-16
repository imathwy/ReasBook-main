import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_2_2
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_7_5.GeneratorFieldModel
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_7_5.GeneratorFieldOrbitTrace
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_7_5.GeneratorFieldSubrepresentation
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_4_1
import LinearRepresentations_Serre_1977.Serre.Chap12.GaloisPowerClasses
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_6_2.SeparatorSupport

noncomputable section

open Representation
open PrimeSpectrum
open scoped Representation

universe u v w

namespace Representation

open IsCyclotomicExtension.Rat

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K] [IsFractionRing A K]
variable {p : ℕ} [Fact p.Prime]

local notation "ΓK" => Γ[K](G)

/- Route correction: this is source Lemma 16 in §12.7. If the `p`-regular components
of two elements are `Γ_K`-conjugate, then every function in `A ⊗ R_K(G)` has congruent values
modulo each prime of `A` above `(p)`. Downstream Lemma 18 only needs the ideal-membership
form below; quotient formulations should be derived from this theorem locally. -/

/-- Helper for Lemma 12-12.7-4: every owner element of `A ⊗ R_K(G)` is constant on the ambient
arithmetic `Γ_K`-power classes. -/
lemma isConstantOnGaloisPowerClasses_of_mem_characterRingOverFieldAlgebraScalarExtension_local
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) :
    IsConstantOnGaloisPowerClasses ΓK f := by
  -- First promote `f` to a genuine class function, then descend the `Γ_K`-invariance criterion
  -- through Corollary `12.12.4.2`.
  have hfClass : _root_.IsClassFunction f := by
    induction hf using Submodule.span_induction with
    | mem ψ hψ =>
        exact isClassFunction_of_mem_characterRingOverField ψ (by simpa using hψ)
    | zero =>
        simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K)))
    | add f g _ _ hf hg =>
        letI : _root_.IsClassFunction f := hf
        letI : _root_.IsClassFunction g := hg
        simpa using (inferInstance : _root_.IsClassFunction (f + g))
    | smul a f _ hf =>
        letI : _root_.IsClassFunction f := hf
        simpa using (inferInstance : _root_.IsClassFunction (a • f))
  refine (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hfClass).2 ?_
  let φ : classFunctionSubmodule K G :=
    ⟨f, (mem_classFunctionSubmodule_iff K f).2 hfClass⟩
  have hscalar :
      f ∈ characterRingOverFieldAlgebraScalarExtension K K G := by
    have hle :
        characterRingOverFieldAlgebraScalarExtension A K G ≤
          (characterRingOverFieldAlgebraScalarExtension K K G).restrictScalars A := by
      refine Submodule.span_le.2 ?_
      intro ψ hψ
      exact mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
        (A := K) (K := K) (G := G) (by simpa using hψ)
    exact hle hf
  simpa using
    (classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
      (G := G) (L := L) K φ).1 hscalar

/-- Helper for Lemma 12-12.7-4: equality of `p`-regular `Γ_K`-power classes implies equality of
the ambient `Γ_K`-power classes. -/
lemma galoisPowerClassMk_eq_of_pRegularGaloisPowerClassMk_eq
    {s t : G} (hs : IsPRegular p s) (ht : IsPRegular p t)
    (hclass :
      pRegularGaloisPowerClassMk ΓK p ⟨s, hs⟩ =
        pRegularGaloisPowerClassMk ΓK p ⟨t, ht⟩) :
    galoisPowerClassMk ΓK s = galoisPowerClassMk ΓK t := by
  -- Unpack the orbit-quotient equality and forget the `p`-regular proof data.
  change Quotient.mk'' (ConjClasses.mk s) = Quotient.mk'' (ConjClasses.mk t)
  apply Quotient.sound
  rcases Quotient.exact hclass with ⟨u, hu⟩
  exact ⟨u, by simpa using congrArg Subtype.val hu⟩

/-- Helper for Lemma 12-12.7-4: owner values agree on `p`-regular representatives with the same
`Γ_K`-power class. -/
lemma pRegularComponentValueEqOfGaloisPowerClassEq
    {f : G → K} (hf : f ∈ A ⊗R[K](G))
    {x y : {x : G // IsPRegular p x}}
    (hxy : pRegularGaloisPowerClassMk ΓK p x = pRegularGaloisPowerClassMk ΓK p y) :
    f x.1 = f y.1 := by
  -- Convert the `p`-regular quotient equality to the ambient quotient and apply constancy there.
  have hconst :
      IsConstantOnGaloisPowerClasses ΓK f :=
    isConstantOnGaloisPowerClasses_of_mem_characterRingOverFieldAlgebraScalarExtension_local
      (K := K) (A := A) hf
  have hmk :
      galoisPowerClassMk ΓK x.1 = galoisPowerClassMk ΓK y.1 :=
    galoisPowerClassMk_eq_of_pRegularGaloisPowerClassMk_eq
      (K := K) (p := p) x.2 y.2 hxy
  exact hconst.eq_of_mk_eq hmk

/-- Helper for Lemma 12-12.7-4: the remaining arithmetic step compares an owner value with its
`p'`-component modulo a prime ideal above `(p)`. -/
lemma ordCompl_card_not_mem_primeIdealOverPrime_local
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    (((ordCompl[p] (Nat.card G) : ℕ) : A)) ∉ Q.asIdeal := by
  -- The prime-to-`p` part of `|G|` stays invertible modulo every prime ideal lying above `(p)`.
  have hcard_ne_zero : Nat.card G ≠ 0 := by
    have hcard_pos : 0 < Nat.card G :=
      Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩
    exact hcard_pos.ne'
  have hcop : Nat.Coprime p (ordCompl[p] (Nat.card G)) :=
    Nat.coprime_ordCompl Fact.out hcard_ne_zero
  simpa using
    nat_cast_not_mem_primeIdealOverPrime_of_coprime
      (A := A) p (ordCompl[p] (Nat.card G)) hcop Q hQ

/-- Helper for Lemma 12-12.7-4: the defect against the `p'`-component vanishes on the
`p`-regular frontier. -/
lemma pRegularComponentDefect_eq_zero_of_isPRegular_local
    {f : G → K} {s : G} (hs : IsPRegular p s) :
    f s - f (pRegularComponent p s) = 0 := by
  -- On a `p`-regular element, the chosen `p'`-component is the element itself.
  rw [pRegularComponent_eq_self_of_isPRegular (p := p) (x := s) hs]
  ring

/-- Helper for Lemma 12-12.7-4: a sufficiently large `p`-power kills the `p`-part of an element,
so the element and its `p'`-component have the same `p^k`-th power. -/
lemma exists_p_power_eq_pRegularComponent_pow_local (g : G) :
    ∃ k : ℕ, g ^ (p ^ k) = (pRegularComponent p g) ^ (p ^ k) := by
  let hdecomp :=
    p_component_decomposition_exists (p := p) g (isOfFinOrder_of_finite g)
  rcases hdecomp.isPElement with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hpowu : (pUnipotentComponent p g) ^ (p ^ k) = 1 := by
    simpa [hk] using pow_orderOf_eq_one (pUnipotentComponent p g)
  -- Raising the canonical commuting decomposition to `p^k` kills the `p`-part.
  calc
    g ^ (p ^ k) =
        ((pUnipotentComponent p g) * (pRegularComponent p g)) ^ (p ^ k) := by
          exact congrArg (fun x : G ↦ x ^ (p ^ k)) hdecomp.eq_mul
    _ =
        (pUnipotentComponent p g) ^ (p ^ k) * (pRegularComponent p g) ^ (p ^ k) := by
          rw [hdecomp.commute.mul_pow]
    _ = (pRegularComponent p g) ^ (p ^ k) := by
          rw [hpowu, one_mul]

/-- Helper for Lemma 12-12.7-4: inside the cyclic subgroup `⟨g⟩`, the ambient element `g` and its
`p'`-component admit marked lifts with the Chapter `10.10.3.2` `p^k`-power coincidence. -/
lemma cyclicRestrictionEndpointData_local
    (g : G) :
    ∃ (k : ℕ) (xH xrH : Subgroup.zpowers g),
      xH ^ (p ^ k) = xrH ^ (p ^ k) ∧ xH.1 = g ∧ xrH.1 = pRegularComponent p g := by
  obtain ⟨k, hkpow⟩ := exists_p_power_eq_pRegularComponent_pow_local (p := p) g
  let xH : Subgroup.zpowers g := ⟨g, Subgroup.mem_zpowers g⟩
  let xrH : Subgroup.zpowers g :=
    ⟨pRegularComponent p g,
      (p_component_decomposition_exists (p := p) g
        (isOfFinOrder_of_finite g)).right_mem_zpowers⟩
  refine ⟨k, xH, xrH, ?_, rfl, rfl⟩
  -- The Chapter `10.10.3.2` power comparison is already stated on the ambient group.
  apply Subtype.ext
  simpa [xH, xrH] using hkpow

/-- Helper for Lemma 12-12.7-4: a `p^k`-power equality in the principal quotient `A / (p)`
descends to equality in the quotient by any prime ideal above `(p)`. -/
lemma primeIdealOverPrime_quotient_eq_of_qpow_span_quotient_eq_local
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal)
    {a b : A} {k : ℕ}
    (hq :
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) a) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) b) ^ (p ^ k)) :
    Ideal.Quotient.mk Q.asIdeal a = Ideal.Quotient.mk Q.asIdeal b := by
  -- First give the prime quotient characteristic `p`, then cancel the common `p^k`-th power by
  -- injectivity of Frobenius in the domain `A ⧸ Q`.
  letI : CharP (A ⧸ Q.asIdeal) p := by
    have hp0 : ((p : A ⧸ Q.asIdeal)) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hQ (Ideal.subset_span (by simp)))
    exact (CharP.charP_iff_prime_eq_zero (R := A ⧸ Q.asIdeal) Fact.out).2 hp0
  letI : IsDomain (A ⧸ Q.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime Q.asIdeal).2 Q.isPrime
  have hqpowQ :
      (Ideal.Quotient.mk Q.asIdeal a) ^ (p ^ k) =
        (Ideal.Quotient.mk Q.asIdeal b) ^ (p ^ k) := by
    simpa using congrArg (Ideal.Quotient.factor hQ) hq
  exact ((frobenius_inj (A ⧸ Q.asIdeal) p).iterate k) <| by
    simpa [iterate_frobenius] using hqpowQ

/-- Helper for Lemma 12-12.7-4: restricting an ambient owner element to a subgroup keeps it in the
same scalar-extended character ring over that subgroup. -/
lemma restrict_mem_characterRingOverFieldAlgebraScalarExtension_local
    (H : Subgroup G) {f : G → K} (hf : f ∈ A ⊗R[K](G)) :
    (fun h : H ↦ f h) ∈ A ⊗R[K](H) := by
  -- Restrict the defining `A`-span generator-by-generator, reducing the field-level part to
  -- restriction of honest representations.
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      have hχ_mem : χ ∈ R[K](G) := by
        simpa using hχ
      have hχ_restrict : (fun h : H ↦ χ h) ∈ R[K](H) := by
        refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ_mem
        · intro ψ hψ
          rcases hψ with ⟨ρ, hρfd, -, rfl⟩
          change (Rep.res H.subtype ρ).ρ.character ∈ R[K](H)
          letI : FiniteDimensional K ρ := hρfd
          letI : FiniteDimensional K (Rep.res H.subtype ρ) := by infer_instance
          exact rep_character_mem_characterRingOverField (Rep.res H.subtype ρ)
        · intro n
          exact (R[K](H)).algebraMap_mem n
        · intro φ ψ _ _ hφ hψ
          simpa using (R[K](H)).add_mem hφ hψ
        · intro φ ψ _ _ hφ hψ
          simpa using (R[K](H)).mul_mem hφ hψ
      exact
        mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
          (A := A) hχ_restrict
  | zero =>
      exact zero_mem (A ⊗R[K](H))
  | add f g _ _ hf hg =>
      simpa using (A ⊗R[K](H)).add_mem hf hg
  | smul a f _ hf =>
      simpa using (A ⊗R[K](H)).smul_mem a hf

/-- Helper for Lemma 12-12.7-4: Serre's generator field for a cyclic linear character is
finite-dimensional over `K`, so its generator-field model has a well-defined character. -/
@[reducible] private def instFiniteDimensionalGeneratorFieldCarrier_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    FiniteDimensional K (generatorFieldCarrier (K := K) (x := g) β) :=
  IntermediateField.adjoin.finiteDimensional
    ((generatorField_generator_isAlgebraic (K := K) (x := g) β).isIntegral)

attribute [local instance] instFiniteDimensionalGeneratorFieldCarrier_local

/-- Helper for Lemma 12-12.7-4: the one-dimensional algebraic-closure model attached to `β`
realizes the chosen linear constituent on the cyclic subgroup `⟨g⟩`. -/
private def chosenLinearConstituentRep_1274_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    Representation (AlgebraicClosure K) (Subgroup.zpowers g) (AlgebraicClosure K) :=
  { toFun := fun c ↦ (β c : (AlgebraicClosure K)ˣ) • LinearMap.id
    map_one' := by
      ext z
      simp
    map_mul' := by
      intro c d
      ext z
      simp [smul_smul] }

/-- Helper for Lemma 12-12.7-4: the character of the one-dimensional constituent model is exactly
the chosen linear character `β`. -/
private theorem chosenLinearConstituentRep_character_1274_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    (chosenLinearConstituentRep_1274_local (K := K) g β).character = fun c ↦ ↑(β c) := by
  -- In dimension one, the trace of scalar multiplication is that scalar itself.
  ext c
  rw [Representation.character]
  change
    LinearMap.trace (AlgebraicClosure K) (AlgebraicClosure K)
        (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) • LinearMap.id) =
      ((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
  rw [LinearMap.map_smul]
  simp [LinearMap.trace_id]

/-- Helper for Lemma 12-12.7-4: the one-dimensional constituent model is irreducible. -/
private theorem chosenLinearConstituentRep_isIrreducible_1274_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    (chosenLinearConstituentRep_1274_local (K := K) g β).IsIrreducible := by
  have hnontrivial :
      Nontrivial (Subrepresentation (chosenLinearConstituentRep_1274_local (K := K) g β)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot_top
    have hbot_top_submodule :
        (⊥ : Submodule (AlgebraicClosure K) (AlgebraicClosure K)) = ⊤ := by
      exact congrArg Subrepresentation.toSubmodule hbot_top
    exact bot_ne_top hbot_top_submodule
  letI := hnontrivial
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro σ hσ
  apply Subrepresentation.toSubmodule_injective
  have hσ' : σ.toSubmodule ≠ ⊥ := by
    intro hbot
    apply hσ
    exact Subrepresentation.toSubmodule_injective hbot
  rcases (Submodule.ne_bot_iff σ.toSubmodule).mp hσ' with ⟨y, hy, hy0⟩
  have hyinv : y⁻¹ * y ∈ σ.toSubmodule := by
    simpa [smul_eq_mul] using Submodule.smul_mem σ.toSubmodule y⁻¹ hy
  have h1 : (1 : AlgebraicClosure K) ∈ σ.toSubmodule := by
    -- A nonzero vector generates the whole one-dimensional carrier.
    have hmul : y⁻¹ * y = (1 : AlgebraicClosure K) := by
      field_simp [hy0]
    simpa [hmul] using hyinv
  refine Submodule.eq_top_iff'.2 ?_
  intro z
  simpa using Submodule.smul_mem σ.toSubmodule z h1

/-- Helper for Lemma 12-12.7-4: base-changing a `K`-linear map and then evaluating it against a
conjugating scalar multiplication agrees with multiplying after evaluation. -/
private theorem liftBaseChange_conj_mul_1274_local
    {B : Type*} [CommRing B] [Algebra K B]
    {M : Type*} [AddCommGroup M] [Module K M]
    (incl : M →ₗ[K] B) (T : M →ₗ[K] M) (b : B)
    (hT : ∀ z : M, incl (T z) = b * incl z) (t : TensorProduct K B M) :
    LinearMap.liftBaseChange B incl (LinearMap.baseChange B T t) =
      b * LinearMap.liftBaseChange B incl t := by
  -- Reduce the tensor statement to pure tensors, where it is just the conjugation identity.
  induction t using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a z =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
        LinearMap.liftBaseChange_tmul, hT, smul_eq_mul, smul_eq_mul]
      ring
  | add t₁ t₂ ih₁ ih₂ =>
      rw [map_add, map_add, map_add, ih₁, ih₂, mul_add]

/-- Helper for Lemma 12-12.7-4: evaluation on the generator field produces the nonzero intertwiner
from the scalar extension of the generator-field model to the one-dimensional constituent model. -/
private def generatorField_evaluationIntertwiner_1274_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    (Representation.scalarExtension (k := AlgebraicClosure K)
        (generatorField_linearCharacter_representation (K := K) (x := g) β)).IntertwiningMap
      (chosenLinearConstituentRep_1274_local (K := K) g β) := by
  refine
    ⟨LinearMap.liftBaseChange (AlgebraicClosure K)
        ((generatorFieldOfLinearCharacter (K := K) (x := g) β).val).toLinearMap, ?_⟩
  intro c
  rw [LinearMap.ext_iff]
  intro t
  change
    LinearMap.liftBaseChange (AlgebraicClosure K)
        ((generatorFieldOfLinearCharacter (K := K) (x := g) β).val).toLinearMap
        ((LinearMap.baseChange (AlgebraicClosure K)
          ((generatorField_linearCharacter_representation (K := K) (x := g) β) c)) t) =
      (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) *
        (LinearMap.liftBaseChange (AlgebraicClosure K)
          ((generatorFieldOfLinearCharacter (K := K) (x := g) β).val).toLinearMap t)
  -- On each pure tensor, the generator-field action is multiplication by the same scalar `β c`.
  exact
    liftBaseChange_conj_mul_1274_local (K := K)
      ((generatorFieldOfLinearCharacter (K := K) (x := g) β).val).toLinearMap
      ((generatorField_linearCharacter_representation (K := K) (x := g) β) c)
      (((β c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) (fun z ↦ rfl) t

/-- Helper for Lemma 12-12.7-4: the evaluation intertwiner is nonzero. -/
private theorem generatorField_evaluationIntertwiner_ne_zero_1274_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    generatorField_evaluationIntertwiner_1274_local (K := K) g β ≠ 0 := by
  intro hzero
  have hval := congrArg
    (fun f :
      (Representation.scalarExtension (k := AlgebraicClosure K)
          (generatorField_linearCharacter_representation (K := K) (x := g) β)).IntertwiningMap
        (chosenLinearConstituentRep_1274_local (K := K) g β) ↦
        f (1 ⊗ₜ[K] (1 : generatorFieldCarrier (K := K) (x := g) β)))
    hzero
  have htmul :
      generatorField_evaluationIntertwiner_1274_local (K := K) g β
          (1 ⊗ₜ[K] (1 : generatorFieldCarrier (K := K) (x := g) β)) =
        (1 : AlgebraicClosure K) := by
    -- Evaluating the pure tensor `1 ⊗ 1` just returns `1`.
    show LinearMap.liftBaseChange (AlgebraicClosure K)
        ((generatorFieldOfLinearCharacter (K := K) (x := g) β).val).toLinearMap
        (1 ⊗ₜ[K] (1 : generatorFieldCarrier (K := K) (x := g) β)) = 1
    rw [LinearMap.liftBaseChange_tmul, smul_eq_mul, one_mul]
    rfl
  exact one_ne_zero ((htmul.symm.trans hval).trans rfl)

/-- Helper for Lemma 12-12.7-4: the chosen algebraically closed constituent yields a nonzero
intertwiner from the scalar extension of the generator-field model into the scalar extension of
the original irreducible representation. -/
private theorem generatorField_scalarExtension_to_scalarExtension_ne_zero_1274_local
    (g : G)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Subgroup.zpowers g) V) [ρ.IsIrreducible]
    (σΩ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure K) ρ))
    (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ)
    (hβchar : σΩ.toRepresentation.character = fun c ↦ ↑(β c)) :
    ∃ F :
        (Representation.scalarExtension (k := AlgebraicClosure K)
            (generatorField_linearCharacter_representation (K := K) (x := g) β)).IntertwiningMap
          (Representation.scalarExtension (k := AlgebraicClosure K) ρ),
      F ≠ 0 := by
  let τ := generatorField_linearCharacter_representation (K := K) (x := g) β
  let χΩ := chosenLinearConstituentRep_1274_local (K := K) g β
  letI : χΩ.IsIrreducible :=
    chosenLinearConstituentRep_isIrreducible_1274_local (K := K) g β
  have hcardC_ne_alg : (Nat.card (Subgroup.zpowers g) : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  letI : Invertible (Nat.card (Subgroup.zpowers g) : AlgebraicClosure K) :=
    invertibleOfNonzero hcardC_ne_alg
  obtain ⟨eχσ⟩ : Nonempty (χΩ.Equiv σΩ.toRepresentation) := by
    -- The chosen constituent has exactly the linear character `β`, so the two irreducibles are
    -- equivalent over the algebraic closure.
    exact
      (Representation.character_eq_iff_nonempty_equiv χΩ σΩ.toRepresentation).mp
        ((chosenLinearConstituentRep_character_1274_local (K := K) g β).trans hβchar.symm)
  let inclΩ :
      σΩ.toRepresentation.IntertwiningMap
        (Representation.scalarExtension (k := AlgebraicClosure K) ρ) :=
    ⟨σΩ.toSubmodule.subtype, by
      intro c
      ext z
      rfl⟩
  let fτΩ := generatorField_evaluationIntertwiner_1274_local (K := K) g β
  have hfτΩ : fτΩ ≠ 0 :=
    generatorField_evaluationIntertwiner_ne_zero_1274_local (K := K) g β
  refine ⟨inclΩ.comp (eχσ.toIntertwiningMap.comp fτΩ), ?_⟩
  intro hzero
  apply hfτΩ
  apply Representation.IntertwiningMap.ext
  rw [LinearMap.ext_iff]
  intro z
  have hcomp := congrArg
    (fun f :
      (Representation.scalarExtension (k := AlgebraicClosure K) τ).IntertwiningMap
        (Representation.scalarExtension (k := AlgebraicClosure K) ρ) ↦ f z)
    hzero
  have hsub0 : eχσ.toLinearEquiv (fτΩ z) = 0 := by
    apply Submodule.subtype_injective σΩ.toSubmodule
    exact hcomp
  exact eχσ.toLinearEquiv.map_eq_zero_iff.mp hsub0

/-- Helper for Lemma 12-12.7-4: the chosen constituent makes the scalar-extension pairing between
the generator-field model and the original irreducible representation nonzero. -/
private theorem generatorField_scalarExtension_pairing_ne_zero_1274_local
    (g : G)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Subgroup.zpowers g) V) [ρ.IsIrreducible]
    (σΩ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure K) ρ))
    (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ)
    (hβchar : σΩ.toRepresentation.character = fun c ↦ ↑(β c)) :
    ⟪(Representation.scalarExtension (k := AlgebraicClosure K)
          (generatorField_linearCharacter_representation (K := K) (x := g) β)).character,
        (Representation.scalarExtension (k := AlgebraicClosure K) ρ).character⟫ ≠
      (0 : AlgebraicClosure K) := by
  let τ := generatorField_linearCharacter_representation (K := K) (x := g) β
  obtain ⟨FΩ, hFΩ_ne⟩ :=
    generatorField_scalarExtension_to_scalarExtension_ne_zero_1274_local
      (K := K) g ρ σΩ β hβchar
  have hcardC_ne_alg : (Nat.card (Subgroup.zpowers g) : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  letI : Invertible (Nat.card (Subgroup.zpowers g) : AlgebraicClosure K) :=
    invertibleOfNonzero hcardC_ne_alg
  have hpos :
      0 <
        Module.finrank (AlgebraicClosure K)
          ((Representation.scalarExtension (k := AlgebraicClosure K) τ).IntertwiningMap
            (Representation.scalarExtension (k := AlgebraicClosure K) ρ)) := by
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨FΩ, hFΩ_ne⟩
  -- Orthogonality turns the nonzero intertwiner into a nonzero scalar pairing.
  have hpair := (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
    (AlgebraicClosure K)
    (Representation.scalarExtension (k := AlgebraicClosure K)
      (generatorField_linearCharacter_representation (K := K) (x := g) β))
    (Representation.scalarExtension (k := AlgebraicClosure K) ρ)).trans_ne
    (Nat.cast_ne_zero.mpr hpos.ne')
  convert hpair using 2 <;> exact Subsingleton.elim _ _

/-- Helper for Lemma 12-12.7-4: the pairing over `K` is already nonzero, after descending the
scalar-extension pairing through the coefficient map `K → AlgebraicClosure K`. -/
private theorem generatorField_pairing_ne_zero_1274_local
    (g : G)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Subgroup.zpowers g) V) [ρ.IsIrreducible]
    (σΩ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure K) ρ))
    (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ)
    (hβchar : σΩ.toRepresentation.character = fun c ↦ ↑(β c)) :
    ⟪(generatorField_linearCharacter_representation (K := K) (x := g) β).character,
        ρ.character⟫ ≠ (0 : K) := by
  have hpair_alg_ne :=
    generatorField_scalarExtension_pairing_ne_zero_1274_local
      (K := K) g ρ σΩ β hβchar
  have hpair_map_ne :
      algebraMap K (AlgebraicClosure K)
          ⟪(generatorField_linearCharacter_representation (K := K) (x := g) β).character,
            ρ.character⟫ ≠
        (0 : AlgebraicClosure K) := by
    have hpair_map :
        ⟪(fun c : Subgroup.zpowers g ↦ algebraMap K (AlgebraicClosure K)
              ((generatorField_linearCharacter_representation (K := K) (x := g) β).character c)),
            fun c : Subgroup.zpowers g ↦ algebraMap K (AlgebraicClosure K) (ρ.character c)⟫ =
          algebraMap K (AlgebraicClosure K)
            ⟪(generatorField_linearCharacter_representation (K := K) (x := g) β).character,
              ρ.character⟫ := by
      simp [Representation.groupFunctionPairingOverField, map_mul]
    rw [← hpair_map]
    simpa [scalarExtension_character_eq_map_to_algClosure (K := K)
        (τ := generatorField_linearCharacter_representation (K := K) (x := g) β),
      scalarExtension_character_eq_map_to_algClosure (K := K) (τ := ρ)] using hpair_alg_ne
  intro hzero
  exact hpair_map_ne (by rw [hzero, map_zero])

/-- Helper for Lemma 12-12.7-4: the chosen constituent forces a nonzero intertwiner from the
generator-field model to the original irreducible cyclic representation over `K`. -/
private theorem generatorField_intertwiningMap_finrank_pos_1274_local
    (g : G)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Subgroup.zpowers g) V) [ρ.IsIrreducible]
    (σΩ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure K) ρ))
    (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ)
    (hβchar : σΩ.toRepresentation.character = fun c ↦ ↑(β c)) :
    0 <
      Module.finrank K
        ((generatorField_linearCharacter_representation (K := K) (x := g) β).IntertwiningMap
          ρ) := by
  have hpair_ne :=
    generatorField_pairing_ne_zero_1274_local (K := K) g ρ σΩ β hβchar
  have hcardC_ne : (Nat.card (Subgroup.zpowers g) : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  letI : Invertible (Nat.card (Subgroup.zpowers g) : K) := invertibleOfNonzero hcardC_ne
  have hfinK_ne : (Module.finrank K
      ((generatorField_linearCharacter_representation (K := K) (x := g) β).IntertwiningMap ρ) : K) ≠ 0 := by
    rw [← Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
      K (generatorField_linearCharacter_representation (K := K) (x := g) β) ρ]
    convert hpair_ne using 2 <;> exact Subsingleton.elim _ _
  refine Nat.pos_of_ne_zero (fun h => hfinK_ne ?_)
  rw [h]; simp

/-- Helper for Lemma 12-12.7-4: a chosen algebraically closed linear constituent identifies the
generator-field model with the original irreducible cyclic representation over `K`. -/
private theorem generatorField_model_equiv_of_chosen_constituent_1274_local
    (g : G)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Subgroup.zpowers g) V) [ρ.IsIrreducible]
    (σΩ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure K) ρ))
    (_hσΩ_irr : σΩ.toRepresentation.IsIrreducible)
    (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ)
    (hβchar : σΩ.toRepresentation.character = fun c ↦ ↑(β c)) :
    Nonempty ((generatorField_linearCharacter_representation (K := K) (x := g) β).Equiv ρ) := by
  obtain ⟨f, hf⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp
      (generatorField_intertwiningMap_finrank_pos_1274_local
        (K := K) g ρ σΩ β hβchar)
  -- A nonzero intertwiner between irreducibles is already an equivalence.
  exact generatorField_model_equiv_of_nonzero_intertwiner (K := K) (x := g) β ρ f hf

/-- Helper for Lemma 12-12.7-4: move an honest finite-dimensional character into the universe
expected by `Rep`, without changing its character values. -/
private theorem rep_character_mem_characterRingOverField_universe_bridge_1274_local
    {K' : Type v} [Field K']
    {H : Type u} [Group H] [Finite H]
    {V : Type w} [AddCommGroup V] [Module K' V] [FiniteDimensional K' V]
    (ρ : Representation K' H V) :
    ρ.character ∈ R[K'](H) := by
  let e := (Module.finBasis K' V).equivFun
  let ρfin : Representation K' H (Fin (Module.finrank K' V) → K') :=
    { toFun := fun h ↦ e.conj (ρ h)
      map_one' := by
        -- Conjugation carries the identity action to the identity action on the coordinate model.
        calc
          e.conj (ρ 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id e
      map_mul' := by
        intro g h
        -- The coordinate model still satisfies the representation law after conjugation.
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let τρ : Representation K' H (ULift.{max u v} (Fin (Module.finrank K' V) → K')) :=
    { toFun := fun h ↦
        { toFun := fun x ↦ ⟨ρfin h x.down⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  let τ : Rep K' H := Rep.of τρ
  have hfin : ρ.character = ρfin.character := by
    -- Passing to coordinates preserves the character because trace is conjugation-invariant.
    ext h
    symm
    simpa [τ, ρfin, Representation.character] using
      (LinearMap.trace_conj' (ρ h) e)
  have hulift : τ.ρ.character = ρfin.character := by
    -- The final `ULift` is only a universe adjustment, so the trace stays unchanged.
    ext h
    change
      LinearMap.trace K' (ULift.{max u v} (Fin (Module.finrank K' V) → K'))
          ((ULift.moduleEquiv.symm : (Fin (Module.finrank K' V) → K') ≃ₗ[K']
            ULift.{max u v} (Fin (Module.finrank K' V) → K')).conj (ρfin h)) =
        LinearMap.trace K' (Fin (Module.finrank K' V) → K') (ρfin h)
    simpa [τ, τρ] using
      (LinearMap.trace_conj' (ρfin h)
        (ULift.moduleEquiv.symm : (Fin (Module.finrank K' V) → K') ≃ₗ[K']
          ULift.{max u v} (Fin (Module.finrank K' V) → K')))
  have hchar : ρ.character = τ.ρ.character := by
    exact hfin.trans hulift.symm
  exact hchar ▸ Representation.rep_character_mem_characterRingOverField (K := K') (G := H) τ

/-- Helper for Lemma 12-12.7-4: the generator-field model contributes an ordinary owner element of
`A ⊗ R_K(⟨g⟩)`. -/
lemma generatorFieldCharacter_mem_characterRingOverFieldAlgebraScalarExtension_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    (generatorField_linearCharacter_representation (K := K) (x := g) β).character ∈
      A ⊗R[K](Subgroup.zpowers g) := by
  -- First view the generator-field model as an honest `K`-representation of the cyclic subgroup,
  -- then promote its character into the scalar-extended owner over `A`.
  let τβ : Rep K (Subgroup.zpowers g) :=
    Rep.of (generatorField_linearCharacter_representation (K := K) (x := g) β)
  have hτβ : τβ.ρ.character ∈ R[K](Subgroup.zpowers g) :=
    rep_character_mem_characterRingOverField_universe_bridge_1274_local
      (ρ := generatorField_linearCharacter_representation (K := K) (x := g) β)
  exact
    mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
      (A := A) hτβ

/-- Helper for Lemma 12-12.7-4: package the generator-field character as a bundled element of the
scalar-extended character-ring subalgebra on the cyclic subgroup `⟨g⟩`. -/
noncomputable def generatorFieldCharacter_subalgebra_mk_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra A K (Subgroup.zpowers g) :=
  ⟨(generatorField_linearCharacter_representation (K := K) (x := g) β).character,
    generatorFieldCharacter_mem_characterRingOverFieldAlgebraScalarExtension_local
      (K := K) (A := A) g β⟩

/-- Helper for Lemma 12-12.7-4: realize the abstract tensor owner `A ⊗ R_K(H)` as an `H → K`
function. This is the source-side normalization used before any cyclic quotient comparison. -/
private abbrev tensorCharacterRingRealization_1274_local
    (H : Subgroup G) :
    TensorProduct ℤ A (R[K](H)) →ₗ[A] H → K :=
  (A ⊗R[K](H)).subtype.comp
    (((R[K](H)).toSubmodule).tensorToSpan A)

/-- Helper for Lemma 12-12.7-4: realizing an abstract tensor character on `H` always lands in the
owner `A ⊗ R_K(H)`. -/
private theorem tensorCharacterRingToFunction_mem_owner_1274_local
    (H : Subgroup G) (ξ : TensorProduct ℤ A (R[K](H))) :
    tensorCharacterRingRealization_1274_local (A := A) (K := K) H ξ ∈
      A ⊗R[K](H) := by
  -- Push the tensor realization through the defining span of the owner.
  induction ξ using TensorProduct.induction_on with
  | zero =>
      simpa using (A ⊗R[K](H)).zero_mem
  | tmul a χ =>
      -- On pure tensors the realization is the expected scalar multiple of the underlying
      -- virtual character.
      simpa [tensorCharacterRingRealization_1274_local] using
        (A ⊗R[K](H)).smul_mem a
          (mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
            (A := A) (K := K) (G := H) χ.property)
  | add ξ η hξ hη =>
      simpa [tensorCharacterRingRealization_1274_local, map_add] using
        (A ⊗R[K](H)).add_mem hξ hη

/-- Helper for Lemma 12-12.7-4: every owner element on `H` is realized by an abstract tensor
character. This gives a concrete tensor representative before passing to residue calculations. -/
private theorem exists_tensorCharacterRing_preimage_of_mem_owner_1274_local
    (H : Subgroup G) {f : H → K} (hf : f ∈ A ⊗R[K](H)) :
    ∃ ξ : TensorProduct ℤ A (R[K](H)),
      tensorCharacterRingRealization_1274_local (A := A) (K := K) H ξ = f := by
  -- Induct over the defining `A`-span of the owner to build a tensor representative.
  induction hf using Submodule.span_induction with
  | mem g hg =>
      let χ : R[K](H) := ⟨g, by simpa using hg⟩
      refine ⟨1 ⊗ₜ[ℤ] χ, ?_⟩
      have htmul :
          ((((R[K](H)).toSubmodule.tensorToSpan A) (1 ⊗ₜ[ℤ] χ) : A ⊗R[K](H)) : H → K) =
            (1 : A) • (χ : H → K) := by
        simpa using
          (Submodule.tensorToSpan_apply_tmul
            (R := ℤ) (A := A) (p := (R[K](H)).toSubmodule)
            (a := (1 : A)) (x := χ))
      ext c
      simpa [tensorCharacterRingRealization_1274_local, χ] using congrFun htmul c
  | zero =>
      refine ⟨0, ?_⟩
      simp [tensorCharacterRingRealization_1274_local]
  | add g h _ _ hg hh =>
      rcases hg with ⟨ξg, rfl⟩
      rcases hh with ⟨ξh, rfl⟩
      refine ⟨ξg + ξh, ?_⟩
      simp [tensorCharacterRingRealization_1274_local, map_add]
  | smul a g _ hg =>
      rcases hg with ⟨ξg, rfl⟩
      refine ⟨a • ξg, ?_⟩
      simp [tensorCharacterRingRealization_1274_local]

/-- Helper for Lemma 12-12.7-4: the cyclic subgroup `⟨g⟩` is generated by its distinguished
element `zpowers_generator`. -/
lemma zpowers_zpowersGenerator_eq_top_local (g : G) :
    Subgroup.zpowers ((zpowers_generator (x := g) : Subgroup.zpowers g)) = ⊤ := by
  -- Every element of `⟨g⟩` is already a power of the subgroup generator corresponding to `g`.
  ext y
  constructor
  · intro _hy
    simp
  · intro _hy
    rcases Subgroup.mem_zpowers_iff.mp y.2 with ⟨n, hn⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
      apply Subtype.ext
      simpa using hn⟩

/-- Helper for Lemma 12-12.7-4: every element of `⟨g⟩` is an integral power of the distinguished
generator `zpowers_generator`. -/
lemma exists_eq_zpowersGenerator_zpow_local (g : G) (y : Subgroup.zpowers g) :
    ∃ n : ℤ, y = (zpowers_generator (x := g)) ^ n := by
  -- Rewrite the subgroup membership witness against the canonical generator of `⟨g⟩`.
  rcases Subgroup.mem_zpowers_iff.mp y.2 with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simpa using hn.symm

/-- Helper for Lemma 12-12.7-4: if a `K`-value is known to come from `A`, choose one lift and
reduce it modulo the fixed prime ideal `Q`. -/
noncomputable def residueFieldOfLiftedValue_local
    (Q : PrimeSpectrum A)
    (z : K) (hz : z ∈ Set.range (algebraMap A K)) :
    Q.asIdeal.ResidueField :=
  algebraMap A Q.asIdeal.ResidueField (Classical.choose hz)

/-- Helper for Lemma 12-12.7-4: the chosen residue class is zero exactly when the underlying
`K`-value is represented by an element of the fixed prime ideal `Q`. -/
@[simp] theorem residueFieldOfLiftedValue_eq_zero_iff_local
    (Q : PrimeSpectrum A)
    (z : K) (hz : z ∈ Set.range (algebraMap A K)) :
    residueFieldOfLiftedValue_local (A := A) (K := K) Q z hz = 0 ↔
      ∃ a : Q.asIdeal, algebraMap A K a.1 = z := by
  constructor
  · intro hz0
    -- Zero in the residue field means the chosen `A`-lift already lies in `Q`.
    refine ⟨⟨Classical.choose hz, ?_⟩, ?_⟩
    · exact (Ideal.algebraMap_residueField_eq_zero (I := Q.asIdeal)).mp hz0
    · exact Classical.choose_spec hz
  · rintro ⟨a, ha⟩
    -- Any two lifts of the same `K`-value agree because `A → K` is injective.
    have hEq : (Classical.choose hz : A) = a.1 := by
      apply (IsFractionRing.injective A K)
      calc
        algebraMap A K (Classical.choose hz) = z := Classical.choose_spec hz
        _ = algebraMap A K a.1 := ha.symm
    simpa [residueFieldOfLiftedValue_local, hEq] using a.2

/-- Helper for Lemma 12-12.7-4: two proofs that the same `K`-value comes from `A` define the same
residue class modulo `Q`. -/
theorem residueFieldOfLiftedValue_eq_of_eq_local
    (Q : PrimeSpectrum A)
    {z : K} (hz hw : z ∈ Set.range (algebraMap A K)) :
    residueFieldOfLiftedValue_local (A := A) (K := K) Q z hz =
      residueFieldOfLiftedValue_local (A := A) (K := K) Q z hw := by
  -- Both chosen lifts map to the same fraction-field value, so they agree in the residue field.
  apply congrArg (algebraMap A Q.asIdeal.ResidueField)
  apply (IsFractionRing.injective A K)
  calc
    algebraMap A K (Classical.choose hz) = z := Classical.choose_spec hz
    _ = algebraMap A K (Classical.choose hw) := (Classical.choose_spec hw).symm

/-- Helper for Lemma 12-12.7-4: equal `K`-values with `A`-lifts give equal residue classes
modulo `Q`. -/
theorem residueFieldOfLiftedValue_congr_local
    (Q : PrimeSpectrum A)
    {z w : K} (hz : z ∈ Set.range (algebraMap A K))
    (hw : w ∈ Set.range (algebraMap A K)) (hzw : z = w) :
    residueFieldOfLiftedValue_local (A := A) (K := K) Q z hz =
      residueFieldOfLiftedValue_local (A := A) (K := K) Q w hw := by
  subst hzw
  exact residueFieldOfLiftedValue_eq_of_eq_local (A := A) (K := K) Q hz hw

/-- Helper for Lemma 12-12.7-4: if the same `K`-value is presented by an explicit lift `a : A`,
the chosen residue class is exactly the residue class of `a`. -/
@[simp] theorem residueFieldOfLiftedValue_eq_algebraMap_local
    (Q : PrimeSpectrum A)
    {z : K} (hz : z ∈ Set.range (algebraMap A K))
    (a : A) (ha : algebraMap A K a = z) :
    residueFieldOfLiftedValue_local (A := A) (K := K) Q z hz =
      algebraMap A Q.asIdeal.ResidueField a := by
  -- Replace the arbitrary witness by the explicit lift `a`, then unfold the residue-class
  -- definition on that canonical representative.
  have hcanon :
      residueFieldOfLiftedValue_local (A := A) (K := K) Q z hz =
        residueFieldOfLiftedValue_local (A := A) (K := K) Q
          (algebraMap A K a) ⟨a, rfl⟩ := by
    exact residueFieldOfLiftedValue_congr_local (A := A) (K := K) Q hz ⟨a, rfl⟩ ha.symm
  rw [hcanon]
  have hchoose :
      (Classical.choose (⟨a, rfl⟩ : algebraMap A K a ∈ Set.range (algebraMap A K))) = a := by
    apply (IsFractionRing.injective A K)
    simpa using
      (Classical.choose_spec (⟨a, rfl⟩ : algebraMap A K a ∈ Set.range (algebraMap A K)))
  simpa [residueFieldOfLiftedValue_local, hchoose]

/-- Helper for Lemma 12-12.7-4: once the endpoint values of a cyclic owner element admit
`A`-lifts, vanishing of their residue difference is exactly the desired witness in `Q.asIdeal`. -/
theorem cyclicDifferenceResidueEval_zero_iff_local
    (g : G)
    (Q : PrimeSpectrum A)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K (Subgroup.zpowers g))
    (y z : Subgroup.zpowers g)
    (hy : ((f : Subgroup.zpowers g → K) y) ∈ Set.range (algebraMap A K))
    (hz : ((f : Subgroup.zpowers g → K) z) ∈ Set.range (algebraMap A K)) :
    residueFieldOfLiftedValue_local (A := A) (K := K) Q ((f : Subgroup.zpowers g → K) y) hy -
        residueFieldOfLiftedValue_local (A := A) (K := K) Q ((f : Subgroup.zpowers g → K) z) hz =
          0 ↔
      ∃ q : Q.asIdeal,
        algebraMap A K q.1 = (f : Subgroup.zpowers g → K) y - (f : Subgroup.zpowers g → K) z := by
  constructor
  · intro hzero
    let ay : A := Classical.choose hy
    let az : A := Classical.choose hz
    have hvalue_y :
        residueFieldOfLiftedValue_local (A := A) (K := K) Q ((f : Subgroup.zpowers g → K) y) hy =
          algebraMap A Q.asIdeal.ResidueField ay := by
      exact residueFieldOfLiftedValue_eq_algebraMap_local
        (A := A) (K := K) Q hy ay (Classical.choose_spec hy)
    have hvalue_z :
        residueFieldOfLiftedValue_local (A := A) (K := K) Q ((f : Subgroup.zpowers g → K) z) hz =
          algebraMap A Q.asIdeal.ResidueField az := by
      exact residueFieldOfLiftedValue_eq_algebraMap_local
        (A := A) (K := K) Q hz az (Classical.choose_spec hz)
    have hzero' : algebraMap A Q.asIdeal.ResidueField (ay - az) = 0 := by
      -- The residue evaluator is additive after replacing both endpoints by explicit lifts.
      calc
        algebraMap A Q.asIdeal.ResidueField (ay - az) =
            algebraMap A Q.asIdeal.ResidueField ay -
              algebraMap A Q.asIdeal.ResidueField az := by rw [map_sub]
        _ = residueFieldOfLiftedValue_local (A := A) (K := K) Q
              ((f : Subgroup.zpowers g → K) y) hy -
            residueFieldOfLiftedValue_local (A := A) (K := K) Q
              ((f : Subgroup.zpowers g → K) z) hz := by
              rw [hvalue_y, hvalue_z]
        _ = 0 := hzero
    have hmem : ay - az ∈ Q.asIdeal := by
      exact (Ideal.algebraMap_residueField_eq_zero (I := Q.asIdeal)).mp hzero'
    refine ⟨⟨ay - az, hmem⟩, ?_⟩
    -- The chosen endpoint lifts now assemble to the required difference witness.
    calc
      algebraMap A K (ay - az) = algebraMap A K ay - algebraMap A K az := by rw [map_sub]
      _ = (f : Subgroup.zpowers g → K) y - (f : Subgroup.zpowers g → K) z := by
            rw [Classical.choose_spec hy, Classical.choose_spec hz]
  · rintro ⟨q, hq⟩
    let ay : A := Classical.choose hy
    let az : A := Classical.choose hz
    have hvalue_y :
        residueFieldOfLiftedValue_local (A := A) (K := K) Q ((f : Subgroup.zpowers g → K) y) hy =
          algebraMap A Q.asIdeal.ResidueField ay := by
      exact residueFieldOfLiftedValue_eq_algebraMap_local
        (A := A) (K := K) Q hy ay (Classical.choose_spec hy)
    have hvalue_z :
        residueFieldOfLiftedValue_local (A := A) (K := K) Q ((f : Subgroup.zpowers g → K) z) hz =
          algebraMap A Q.asIdeal.ResidueField az := by
      exact residueFieldOfLiftedValue_eq_algebraMap_local
        (A := A) (K := K) Q hz az (Classical.choose_spec hz)
    have hEq : ay - az = q.1 := by
      apply (IsFractionRing.injective A K)
      calc
        algebraMap A K (ay - az) = algebraMap A K ay - algebraMap A K az := by rw [map_sub]
        _ = (f : Subgroup.zpowers g → K) y - (f : Subgroup.zpowers g → K) z := by
              rw [Classical.choose_spec hy, Classical.choose_spec hz]
        _ = algebraMap A K q.1 := hq.symm
    have hzero' : algebraMap A Q.asIdeal.ResidueField (ay - az) = 0 := by
      calc
        algebraMap A Q.asIdeal.ResidueField (ay - az) =
            algebraMap A Q.asIdeal.ResidueField q.1 := by rw [hEq]
        _ = 0 := by
              simpa using
                (Ideal.algebraMap_residueField_eq_zero (I := Q.asIdeal) (x := q.1)).2 q.2
    -- Rewrite both residues through the explicit chosen lifts, then collapse to the zero
    -- residue class of `ay - az`.
    calc
      residueFieldOfLiftedValue_local (A := A) (K := K) Q ((f : Subgroup.zpowers g → K) y) hy -
          residueFieldOfLiftedValue_local (A := A) (K := K) Q
            ((f : Subgroup.zpowers g → K) z) hz =
        algebraMap A Q.asIdeal.ResidueField ay -
          algebraMap A Q.asIdeal.ResidueField az := by
            rw [hvalue_y, hvalue_z]
      _ = algebraMap A Q.asIdeal.ResidueField (ay - az) := by rw [map_sub]
      _ = 0 := hzero'

/- Faithfulness to Serre's §12.7: there `A` is the ring of integers `ℤ[μ_m]` generated by the
`m`-th roots of unity (`m = Monoid.exponent G`), which is integrally closed.  The character values
that appear below are sums of roots of unity, hence algebraic integers; the conclusion of Lemma 16
states that their differences are realized by elements of `A`, and this requires `A` to be
integrally closed (it is false for non-maximal orders such as `ℤ[2i] ⊂ ℚ(i)`).  We therefore record
integral closedness of `A` here, matching Serre's hypothesis. -/
variable [IsIntegrallyClosed A]

/-- Helper for Lemma 12-12.7-4: in a commutative ring of characteristic `p`, the `p ^ k`-th power
of a finite sum is the sum of the `p ^ k`-th powers (the iterated "freshman's dream"). -/
private lemma sum_pow_prime_pow_eq_local {R : Type*} [CommRing R] [CharP R p]
    {ι : Type*} (s : Finset ι) (f : ι → R) (k : ℕ) :
    (∑ i ∈ s, f i) ^ (p ^ k) = ∑ i ∈ s, f i ^ (p ^ k) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty,
        zero_pow (pow_ne_zero k (Fact.out : p.Prime).pos.ne')]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, add_pow_char_pow, ih, Finset.sum_insert ha]

/-- Helper for Lemma 12-12.7-4 (the freshman's-dream core, kept self-contained for budget).
For families `u, v` of algebraic integers in a commutative ring `Ω` whose `p ^ k`-th powers agree
termwise, the difference `(∑ u) ^ (p ^ k) - (∑ v) ^ (p ^ k)` is `p` times an algebraic integer.
Worked entirely inside the ring `O = integralClosure ℤ Ω`, reducing modulo `(p)`. -/
private lemma pow_sum_sub_eq_prime_mul_integral_local
    {Ω : Type*} [CommRing Ω] {ι : Type*} [Fintype ι] (k : ℕ) (u v : ι → Ω)
    (hu : ∀ i, IsIntegral ℤ (u i)) (hv : ∀ i, IsIntegral ℤ (v i))
    (huv : ∀ i, u i ^ (p ^ k) = v i ^ (p ^ k)) :
    ∃ c : Ω, IsIntegral ℤ c ∧
      (∑ i, u i) ^ (p ^ k) - (∑ i, v i) ^ (p ^ k) = (p : Ω) * c := by
  classical
  set O := integralClosure ℤ Ω with hOdef
  let uO : ι → O := fun i => ⟨u i, hu i⟩
  let vO : ι → O := fun i => ⟨v i, hv i⟩
  have huvO : ∀ i, uO i ^ (p ^ k) = vO i ^ (p ^ k) := by
    intro i
    apply Subtype.ext
    simpa [uO, vO, SubmonoidClass.coe_pow] using huv i
  -- The two `p ^ k`-th powers agree modulo `(p)` in `O`, by the freshman's dream.
  have hfresh :
      (Ideal.Quotient.mk (Ideal.span {(p : O)}) (∑ i, uO i)) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span {(p : O)}) (∑ i, vO i)) ^ (p ^ k) := by
    rcases subsingleton_or_nontrivial (O ⧸ Ideal.span {(p : O)}) with hsub | hnt
    · exact Subsingleton.elim _ _
    · haveI : CharP (O ⧸ Ideal.span {(p : O)}) p := by
        have hp0 : (p : O ⧸ Ideal.span {(p : O)}) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : O)})) p]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        exact (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
      rw [map_sum, map_sum, sum_pow_prime_pow_eq_local, sum_pow_prime_pow_eq_local]
      exact Finset.sum_congr rfl (fun i _ => by rw [← map_pow, ← map_pow, huvO i])
  have hdvd : (p : O) ∣ (∑ i, uO i) ^ (p ^ k) - (∑ i, vO i) ^ (p ^ k) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, map_pow, map_pow]
    exact hfresh
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨O.val c, c.2, ?_⟩
  have hcv := congrArg O.val hc
  rw [map_sub, map_pow, map_pow, map_sum, map_sum, map_mul, map_natCast] at hcv
  exact hcv

/-- Helper for Lemma 12-12.7-4 (the lift to `A`, kept self-contained for budget).  If `χy, χz` and
the carry `w` are algebraic integers with `χy ^ (p ^ k) - χz ^ (p ^ k) = p · w`, then `χy - χz` is
realized by an element of any prime `Q` of `A` above `(p)`:  lift everything to `A` by integral
closedness, then cancel the common `p ^ k`-th power by Frobenius injectivity in `A ⧸ Q`. -/
private lemma lift_pow_congr_to_prime_local
    (k : ℕ) {χy χz w : K}
    (hyInt : IsIntegral ℤ χy) (hzInt : IsIntegral ℤ χz) (hwInt : IsIntegral ℤ w)
    (hweq : χy ^ (p ^ k) - χz ^ (p ^ k) = (p : K) * w)
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = χy - χz := by
  obtain ⟨ay, hay⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hyInt.tower_top (A := A))
  obtain ⟨az, haz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hzInt.tower_top (A := A))
  obtain ⟨e, he⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hwInt.tower_top (A := A))
  have hAdvd : ay ^ (p ^ k) - az ^ (p ^ k) = (p : A) * e := by
    apply IsFractionRing.injective A K
    rw [map_sub, map_pow, map_pow, hay, haz, map_mul, map_natCast, he, ← hweq]
  have hmkpow :
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ay) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) az) ^ (p ^ k) := by
    rw [← map_pow, ← map_pow, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hAdvd]
    exact Ideal.mem_span_singleton.mpr ⟨e, rfl⟩
  have hmkQ : Ideal.Quotient.mk Q.asIdeal ay = Ideal.Quotient.mk Q.asIdeal az :=
    primeIdealOverPrime_quotient_eq_of_qpow_span_quotient_eq_local Q hQ hmkpow
  refine ⟨⟨ay - az, ?_⟩, ?_⟩
  · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact hmkQ
  · rw [map_sub, hay, haz]

/-- Helper for Lemma 12-12.7-4: integrality over `ℤ` descends along the injective coefficient map
`K → Ω` (isolated for budget, since the instance search over the intermediate field is heavy). -/
private lemma isIntegral_of_algebraMap_isIntegral_local
    {Ω : Type*} [Field Ω] [Algebra K Ω] {x : K}
    (h : IsIntegral ℤ (algebraMap K Ω x)) : IsIntegral ℤ x :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K Ω)
    (FaithfulSMul.algebraMap_injective K Ω)).1 h

/-- Helper for Lemma 12-12.7-4 (the carry pull-back, kept self-contained for budget).  The carry
`c ∈ Ω` produced by the freshman's dream lies in the image of `K` — namely it is the image of
`w = (χy ^ (p ^ k) - χz ^ (p ^ k)) / p` — and that `w` is an algebraic integer. -/
private lemma kbridge_carry_local
    {Ω : Type*} [Field Ω] [Algebra K Ω] [CharZero Ω]
    {ι : Type*} [Fintype ι] (k : ℕ) (u v : ι → Ω)
    (hu : ∀ i, IsIntegral ℤ (u i)) (hv : ∀ i, IsIntegral ℤ (v i))
    (huv : ∀ i, u i ^ (p ^ k) = v i ^ (p ^ k))
    {χy χz : K}
    (hSy : algebraMap K Ω χy = ∑ i, u i) (hSz : algebraMap K Ω χz = ∑ i, v i) :
    ∃ w : K, IsIntegral ℤ w ∧ χy ^ (p ^ k) - χz ^ (p ^ k) = (p : K) * w := by
  obtain ⟨c, hcInt, hceq⟩ :=
    pow_sum_sub_eq_prime_mul_integral_local (Ω := Ω) k u v hu hv huv
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  have hΩeq : algebraMap K Ω (χy ^ (p ^ k) - χz ^ (p ^ k)) = (p : Ω) * c := by
    rw [map_sub, map_pow, map_pow, hSy, hSz]; exact hceq
  refine ⟨(χy ^ (p ^ k) - χz ^ (p ^ k)) / (p : K), ?_, ?_⟩
  · apply isIntegral_of_algebraMap_isIntegral_local (K := K) (Ω := Ω)
    rw [map_div₀, map_natCast, hΩeq, mul_div_cancel_left₀ _ hpΩ]; exact hcInt
  · rw [mul_div_assoc', mul_div_cancel_left₀ _ hpK]

/-- Helper for Lemma 12-12.7-4: the arithmetic heart of Serre's Lemma 16 over a number field.
Given families `u, v` of algebraic integers in an extension `Ω ⊇ K` whose `p ^ k`-th powers agree
termwise, and whose sums are the `Ω`-images of the `K`-values `χy, χz`, the difference `χy - χz`
is the image of an element of every prime `Q` of `A` lying above `(p)`. -/
private lemma sumEmbeddings_pow_congr_lift_local
    {Ω : Type*} [Field Ω] [Algebra K Ω] [CharZero Ω]
    {ι : Type*} [Fintype ι] (k : ℕ) (u v : ι → Ω)
    (hu : ∀ i, IsIntegral ℤ (u i)) (hv : ∀ i, IsIntegral ℤ (v i))
    (huv : ∀ i, u i ^ (p ^ k) = v i ^ (p ^ k))
    {χy χz : K}
    (hSy : algebraMap K Ω χy = ∑ i, u i) (hSz : algebraMap K Ω χz = ∑ i, v i)
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = χy - χz := by
  have hχyInt : IsIntegral ℤ χy :=
    isIntegral_of_algebraMap_isIntegral_local (K := K)
      (by rw [hSy]; exact IsIntegral.sum _ (fun i _ => hu i))
  have hχzInt : IsIntegral ℤ χz :=
    isIntegral_of_algebraMap_isIntegral_local (K := K)
      (by rw [hSz]; exact IsIntegral.sum _ (fun i _ => hv i))
  obtain ⟨w, hwInt, hweq⟩ := kbridge_carry_local (K := K) (Ω := Ω) k u v hu hv huv hSy hSz
  exact lift_pow_congr_to_prime_local (K := K) k hχyInt hχzInt hwInt hweq Q hQ

/-- Helper for Lemma 12-12.7-4: the generator-field model is the atomic cyclic source term whose
character values must be compared modulo primes above `(p)`. -/
lemma generatorFieldCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
    (g : G) (β : Subgroup.zpowers g →* (AlgebraicClosure K)ˣ)
    (y z : Subgroup.zpowers g) (k : ℕ) (hyz : y ^ (p ^ k) = z ^ (p ^ k))
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal,
      algebraMap A K q.1 =
        (generatorField_linearCharacter_representation (K := K) (x := g) β).character y -
          (generatorField_linearCharacter_representation (K := K) (x := g) β).character z := by
  -- Normalize the two endpoints to powers of the distinguished generator of `⟨g⟩`.
  rcases exists_eq_zpowersGenerator_zpow_local (g := g) y with ⟨ny, rfl⟩
  rcases exists_eq_zpowersGenerator_zpow_local (g := g) z with ⟨nz, rfl⟩
  have hyzPow :
      ((zpowers_generator (x := g)) ^ ny) ^ (p ^ k) =
        ((zpowers_generator (x := g)) ^ nz) ^ (p ^ k) := by
    simpa using hyz
  have hcharPowY :
      algebraMap K (AlgebraicClosure K)
          ((generatorField_linearCharacter_representation (K := K) (x := g) β).character
            ((zpowers_generator (x := g)) ^ ny)) =
        ∑ σ : generatorFieldCarrier (K := K) (x := g) β →ₐ[K] AlgebraicClosure K,
          σ (⟨((β ((zpowers_generator (x := g)) ^ ny) : (AlgebraicClosure K)ˣ) :
              AlgebraicClosure K),
            linear_character_value_mem_generatorField (K := K) (x := g) β
              ((zpowers_generator (x := g)) ^ ny)⟩ :
              generatorFieldCarrier (K := K) (x := g) β) :=
    generatorField_model_character_eq_sum_embeddings_on_generator_powers (K := K) (x := g) β ny
  have hcharPowZ :
      algebraMap K (AlgebraicClosure K)
          ((generatorField_linearCharacter_representation (K := K) (x := g) β).character
            ((zpowers_generator (x := g)) ^ nz)) =
        ∑ σ : generatorFieldCarrier (K := K) (x := g) β →ₐ[K] AlgebraicClosure K,
          σ (⟨((β ((zpowers_generator (x := g)) ^ nz) : (AlgebraicClosure K)ˣ) :
              AlgebraicClosure K),
            linear_character_value_mem_generatorField (K := K) (x := g) β
              ((zpowers_generator (x := g)) ^ nz)⟩ :
              generatorFieldCarrier (K := K) (x := g) β) :=
    generatorField_model_character_eq_sum_embeddings_on_generator_powers (K := K) (x := g) β nz
  -- The distinguished generator value `β (x ^ n)` is a root of unity, hence an algebraic integer,
  -- and `hyzPow` forces termwise-equal `p ^ k`-th powers of the embeddings; feed the two embedding
  -- sums into the arithmetic core `sumEmbeddings_pow_congr_lift_local`.
  set aY : generatorFieldCarrier (K := K) (x := g) β :=
    ⟨((β ((zpowers_generator (x := g)) ^ ny) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K),
      linear_character_value_mem_generatorField (K := K) (x := g) β
        ((zpowers_generator (x := g)) ^ ny)⟩ with haYdef
  set aZ : generatorFieldCarrier (K := K) (x := g) β :=
    ⟨((β ((zpowers_generator (x := g)) ^ nz) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K),
      linear_character_value_mem_generatorField (K := K) (x := g) β
        ((zpowers_generator (x := g)) ^ nz)⟩ with haZdef
  have haYcoe : (aY : AlgebraicClosure K) =
      ((β ((zpowers_generator (x := g)) ^ ny) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := rfl
  have haZcoe : (aZ : AlgebraicClosure K) =
      ((β ((zpowers_generator (x := g)) ^ nz) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := rfl
  -- Both generator values are roots of unity of order dividing the order of the cyclic generator.
  have haYord : aY ^ (orderOf ((zpowers_generator (x := g)) ^ ny)) = 1 := by
    refine Subtype.ext ?_
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, haYcoe]
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have haZord : aZ ^ (orderOf ((zpowers_generator (x := g)) ^ nz)) = 1 := by
    refine Subtype.ext ?_
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, haZcoe]
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have hu : ∀ σ : generatorFieldCarrier (K := K) (x := g) β →ₐ[K] AlgebraicClosure K,
      IsIntegral ℤ (σ aY) := by
    intro σ
    refine IsIntegral.of_pow (n := orderOf ((zpowers_generator (x := g)) ^ ny))
      (orderOf_pos _) ?_
    rw [← map_pow, haYord, map_one]; exact isIntegral_one
  have hv : ∀ σ : generatorFieldCarrier (K := K) (x := g) β →ₐ[K] AlgebraicClosure K,
      IsIntegral ℤ (σ aZ) := by
    intro σ
    refine IsIntegral.of_pow (n := orderOf ((zpowers_generator (x := g)) ^ nz))
      (orderOf_pos _) ?_
    rw [← map_pow, haZord, map_one]; exact isIntegral_one
  have haaPow : aY ^ (p ^ k) = aZ ^ (p ^ k) := by
    refine Subtype.ext ?_
    simp only [SubmonoidClass.coe_pow, haYcoe, haZcoe]
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, hyzPow]
  have huv : ∀ σ : generatorFieldCarrier (K := K) (x := g) β →ₐ[K] AlgebraicClosure K,
      (σ aY) ^ (p ^ k) = (σ aZ) ^ (p ^ k) := by
    intro σ
    rw [← map_pow, ← map_pow, haaPow]
  exact sumEmbeddings_pow_congr_lift_local (K := K) (A := A)
    (Ω := AlgebraicClosure K) k
    (fun σ : generatorFieldCarrier (K := K) (x := g) β →ₐ[K] AlgebraicClosure K => σ aY)
    (fun σ : generatorFieldCarrier (K := K) (x := g) β →ₐ[K] AlgebraicClosure K => σ aZ)
    hu hv huv hcharPowY hcharPowZ Q hQ

/-- Helper for Lemma 12-12.7-4: once the atomic generator-field congruence is known, an
irreducible cyclic `K`-representation inherits the same endpoint congruence by transport across
Serre's generator-field model. -/
lemma irreducibleCyclicCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
    (g : G)
    {V : Type (max u w)} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Subgroup.zpowers g) V) [ρ.IsIrreducible]
    (y z : Subgroup.zpowers g) (k : ℕ) (hyz : y ^ (p ^ k) = z ^ (p ^ k))
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = ρ.character y - ρ.character z := by
  -- Route correction: after isolating the generator-field arithmetic, the irreducible cyclic case
  -- is only transport along the chosen constituent equivalence.
  obtain ⟨σΩ, hσΩ_irr, β, hβchar⟩ :=
    choose_algClosed_linear_constituent (K := K) (x := g) ρ
  obtain ⟨e⟩ :=
    generatorField_model_equiv_of_chosen_constituent_1274_local
      (K := K) g ρ σΩ hσΩ_irr β hβchar
  obtain ⟨q, hq⟩ :=
    generatorFieldCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
      (K := K) (A := A) (p := p) g β y z k hyz Q hQ
  refine ⟨q, ?_⟩
  -- The character of `ρ` is identified with the generator-field character through the transport
  -- equivalence `e`.
  calc
    algebraMap A K q.1 =
        (generatorField_linearCharacter_representation (K := K) (x := g) β).character y -
          (generatorField_linearCharacter_representation (K := K) (x := g) β).character z := hq
    _ = ρ.character y - ρ.character z := by
          rw [congrFun (Representation.char_iso e) y, congrFun (Representation.char_iso e) z]

/-- Helper for Lemma 12-12.7-4: endpoint witnesses add across a finite direct sum of cyclic
representations. -/
lemma directSumCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
    (g : G) {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)]
    (π : ∀ i, Representation K (Subgroup.zpowers g) (V i))
    (y z : Subgroup.zpowers g) (k : ℕ) (_hyz : y ^ (p ^ k) = z ^ (p ^ k))
    (Q : PrimeSpectrum A) (_hQ : Ideal.span {(p : A)} ≤ Q.asIdeal)
    (hπ :
      ∀ i, ∃ q : Q.asIdeal, algebraMap A K q.1 = (π i).character y - (π i).character z) :
    ∃ q : Q.asIdeal,
      algebraMap A K q.1 =
        (Representation.directSum π).character y - (Representation.directSum π).character z := by
  classical
  choose q hq using hπ
  refine ⟨⟨∑ i, (q i).1, Ideal.sum_mem _ fun i _ ↦ (q i).2⟩, ?_⟩
  have hchar_y :
      (Representation.directSum π).character y = ∑ i, (π i).character y := by
    letI : DecidableEq ι := Classical.decEq ι
    -- Conjugate the direct-sum action to the plain finite product, where the block-diagonal trace
    -- formula from `trace_piMap_eq_sum_trace` applies literally.
    have hconj :
        (DirectSum.linearEquivFunOnFintype K ι V).conj ((Representation.directSum π) y) =
          LinearMap.piMap (fun i ↦ (π i) y) := by
      ext x i
      rfl
    calc
      (Representation.directSum π).character y =
          LinearMap.trace K _ ((DirectSum.linearEquivFunOnFintype K ι V).conj
            ((Representation.directSum π) y)) := by
              symm
              exact LinearMap.trace_conj' ((Representation.directSum π) y)
                (DirectSum.linearEquivFunOnFintype K ι V)
      _ = LinearMap.trace K _ (LinearMap.piMap (fun i ↦ (π i) y)) := by rw [hconj]
      _ = ∑ i, (π i).character y := by
            simpa [Representation.character] using
      (trace_piMap_eq_sum_trace (K := K) (f := fun i ↦ π i y))
  have hchar_z :
      (Representation.directSum π).character z = ∑ i, (π i).character z := by
    letI : DecidableEq ι := Classical.decEq ι
    -- The same conjugation-to-products computation applies at the second endpoint.
    have hconj :
        (DirectSum.linearEquivFunOnFintype K ι V).conj ((Representation.directSum π) z) =
          LinearMap.piMap (fun i ↦ (π i) z) := by
      ext x i
      rfl
    calc
      (Representation.directSum π).character z =
          LinearMap.trace K _ ((DirectSum.linearEquivFunOnFintype K ι V).conj
            ((Representation.directSum π) z)) := by
              symm
              exact LinearMap.trace_conj' ((Representation.directSum π) z)
                (DirectSum.linearEquivFunOnFintype K ι V)
      _ = LinearMap.trace K _ (LinearMap.piMap (fun i ↦ (π i) z)) := by rw [hconj]
      _ = ∑ i, (π i).character z := by
            simpa [Representation.character] using
      (trace_piMap_eq_sum_trace (K := K) (f := fun i ↦ π i z))
  calc
    algebraMap A K (∑ i, (q i).1) = ∑ i, algebraMap A K (q i).1 := by
      simp
    _ = ∑ i, ((π i).character y - (π i).character z) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hq i
    _ = (∑ i, (π i).character y) - ∑ i, (π i).character z := by
      rw [Finset.sum_sub_distrib]
    _ = (Representation.directSum π).character y - (Representation.directSum π).character z := by
      rw [hchar_y, hchar_z]

/-- Helper for Lemma 12-12.7-4: the remaining atomic cyclic step is the honest-character
comparison on `⟨g⟩`, before extending to the full `A`-span. -/
lemma honestCyclicCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
    (g : G)
    {V : Type (max u w)} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Subgroup.zpowers g) V)
    (y z : Subgroup.zpowers g) (k : ℕ) (hyz : y ^ (p ^ k) = z ^ (p ^ k))
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = ρ.character y - ρ.character z := by
  classical
  let H : Subgroup G := Subgroup.zpowers g
  letI : NeZero (Nat.card H : K) := ⟨Nat.cast_ne_zero.mpr Finite.card_pos.ne'⟩
  obtain ⟨ι, _, σ, e, hσirr⟩ :
      ∃ (ι : Type (max u w)) (_ : Fintype ι) (σ : ι → Subrepresentation ρ)
        (e : (Representation.directSum fun i ↦ (σ i).toRepresentation).Equiv ρ),
          ∀ i, (σ i).toRepresentation.IsIrreducible :=
    exists_equiv_directSum_irreducible_subrepresentations (ρ := ρ)
  obtain ⟨q, hq⟩ :=
    directSumCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
      (K := K) (A := A) (p := p) g
      (π := fun i ↦ (σ i).toRepresentation) y z k hyz Q hQ
      (fun i ↦ by
        letI : ((σ i).toRepresentation).IsIrreducible := hσirr i
        -- Each irreducible summand is reduced to the atomic generator-field comparison.
        exact
          irreducibleCyclicCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
            (K := K) (A := A) (p := p) g ((σ i).toRepresentation) y z k hyz Q hQ)
  refine ⟨q, ?_⟩
  -- The decomposition equivalence identifies the honest cyclic character with the direct-sum
  -- character assembled from its irreducible summands.
  calc
    algebraMap A K q.1 =
        (Representation.directSum fun i ↦ (σ i).toRepresentation).character y -
          (Representation.directSum fun i ↦ (σ i).toRepresentation).character z := hq
    _ = ρ.character y - ρ.character z := by
          rw [congrFun (Representation.char_iso e) y, congrFun (Representation.char_iso e) z]

/-- Helper for Lemma 12-12.7-4: on a finite cyclic subgroup, the remaining source proof is the
direct quotient/Frobenius comparison from equal `p^k`-th powers to congruent owner values modulo
every prime above `(p)`. -/
lemma cyclicCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) (g : G)
    (y z : Subgroup.zpowers g) (k : ℕ) (hyz : y ^ (p ^ k) = z ^ (p ^ k))
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = f y.1 - f z.1 := by
  let fH : Subgroup.zpowers g → K := fun h ↦ f h.1
  have hfH : fH ∈ A ⊗R[K](Subgroup.zpowers g) :=
    restrict_mem_characterRingOverFieldAlgebraScalarExtension_local
      (K := K) (A := A) (H := Subgroup.zpowers g) hf
  let witnessProp : (Subgroup.zpowers g → K) → Prop :=
    fun ψ ↦ ∃ q : Q.asIdeal, algebraMap A K q.1 = ψ y - ψ z
  have hmain : witnessProp fH := by
    -- First run the outer `A`-span induction defining `A ⊗ R_K(H)`.
    refine Submodule.span_induction
        (s := (((R[K](Subgroup.zpowers g)).toSubmodule :
          Submodule ℤ (Subgroup.zpowers g → K)) : Set (Subgroup.zpowers g → K)))
        (p := fun ψ _ ↦ witnessProp ψ) ?_ ?_ ?_ ?_ hfH
    · intro χ hχ
      have hχ_mem : χ ∈ R[K](Subgroup.zpowers g) := by
        simpa using hχ
      let honestCharacters : Set (Subgroup.zpowers g → K) :=
        { ψ : Subgroup.zpowers g → K |
            ∃ (V : Type (max u w)) (_ : AddCommGroup V) (_ : Module K V)
              (_ : FiniteDimensional K V)
                (ρ : Representation K (Subgroup.zpowers g) V), ψ = ρ.character }
      have hχ_span :
          χ ∈ Submodule.span ℤ honestCharacters := by
        simpa [honestCharacters] using
          Representation.characterRing_mem_span_honest_characters
            (K := K) (G := Subgroup.zpowers g) χ hχ_mem
      -- Then reduce the field-level character ring to honest characters on the cyclic subgroup.
      refine Submodule.span_induction (s := honestCharacters) (p := fun ψ _ ↦ witnessProp ψ)
          ?_ ?_ ?_ ?_ hχ_span
      · intro ψ hψ
        rcases hψ with ⟨V, _instAddCommGroupV, _instModuleV, _instFiniteDimensionalV, ρ, rfl⟩
        exact
          honestCyclicCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
            (K := K) (A := A) (p := p) g ρ y z k hyz Q hQ
      · refine ⟨0, ?_⟩
        simp
      · intro ψ ξ _ _ hψ hξ
        rcases hψ with ⟨qψ, hqψ⟩
        rcases hξ with ⟨qξ, hqξ⟩
        refine ⟨⟨qψ.1 + qξ.1, Q.asIdeal.add_mem qψ.2 qξ.2⟩, ?_⟩
        -- Add the two ideal witnesses and rewrite the result as the endpoint difference for
        -- the sum character.
        calc
          algebraMap A K (qψ.1 + qξ.1) =
              algebraMap A K qψ.1 + algebraMap A K qξ.1 := by
                simp
          _ = (ψ y - ψ z) + (ξ y - ξ z) := by
                rw [hqψ, hqξ]
          _ = (ψ + ξ) y - (ψ + ξ) z := by
                simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      · intro n ψ _ hψ
        rcases hψ with ⟨q, hq⟩
        refine ⟨⟨(n : A) * q.1, Q.asIdeal.mul_mem_left (n : A) q.2⟩, ?_⟩
        -- Integer scaling keeps the witness inside the prime ideal and scales the endpoint
        -- difference exactly as the `ℤ`-span induction expects.
        calc
          algebraMap A K ((n : A) * q.1) = (n : K) * algebraMap A K q.1 := by
                simp [map_mul]
          _ = n • algebraMap A K q.1 := by
                simp
          _ = n • (ψ y - ψ z) := by
                rw [hq]
          _ = n • ψ y - n • ψ z := by
                rw [zsmul_sub]
          _ = (n • ψ) y - (n • ψ) z := by
                simp [Pi.smul_apply]
    · refine ⟨0, ?_⟩
      simp
    · intro ψ ξ _ _ hψ hξ
      rcases hψ with ⟨qψ, hqψ⟩
      rcases hξ with ⟨qξ, hqξ⟩
      refine ⟨⟨qψ.1 + qξ.1, Q.asIdeal.add_mem qψ.2 qξ.2⟩, ?_⟩
      -- The outer `A`-span uses the same additive witness arithmetic as the inner honest span.
      calc
        algebraMap A K (qψ.1 + qξ.1) =
            algebraMap A K qψ.1 + algebraMap A K qξ.1 := by
              simp
        _ = (ψ y - ψ z) + (ξ y - ξ z) := by
              rw [hqψ, hqξ]
        _ = (ψ + ξ) y - (ψ + ξ) z := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    · intro a ψ _ hψ
      rcases hψ with ⟨q, hq⟩
      refine ⟨⟨a * q.1, Q.asIdeal.mul_mem_left a q.2⟩, ?_⟩
      -- Scalar multiplication by `a ∈ A` is tracked through `algebraMap A K` and matched against
      -- the pointwise `A`-module structure on functions.
      calc
        algebraMap A K (a * q.1) = algebraMap A K a * algebraMap A K q.1 := by
              simp [map_mul]
        _ = algebraMap A K a * (ψ y - ψ z) := by
              rw [hq]
        _ = algebraMap A K a • (ψ y - ψ z) := by
              simp
        _ = algebraMap A K a • ψ y - algebraMap A K a • ψ z := by
              rw [smul_sub]
        _ = (a • ψ) y - (a • ψ) z := by
              simp [Pi.smul_apply, Algebra.smul_def]
  rcases hmain with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  -- Finally unwrap the restricted function back to the original ambient owner values.
  simpa [witnessProp, fH] using hq

/-- Helper for Lemma 12-12.7-4: the remaining arithmetic step compares an owner value with its
`p'`-component modulo a prime ideal above `(p)`. -/
lemma characterValueSubMemPrimeIdealOverPrimeOfPRegularComponent
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) (g : G)
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = f g - f (pRegularComponent p g) := by
  obtain ⟨k, xH, xrH, hxpowH, hxH, hxrH⟩ := cyclicRestrictionEndpointData_local (p := p) g
  obtain ⟨q, hq⟩ :=
    cyclicCharacterValueSubMemPrimeIdealOverPrime_of_powEq_local
      (K := K) (A := A) (p := p) hf g xH xrH k hxpowH Q hQ
  refine ⟨q, ?_⟩
  -- The cyclic restriction step already identifies the restricted endpoint values with the
  -- ambient values at `g` and at `pRegularComponent p g`.
  calc
    algebraMap A K q.1 = f xH.1 - f xrH.1 := by simpa using hq
    _ = f g - f (pRegularComponent p g) := by rw [hxH, hxrH]

/-- Lemma 12-12.7-4: if the `p`-regular components of `x` and `y` have the same
`Γ_K`-power class, then every owner element of `A ⊗ R_K(G)` takes values congruent modulo every
prime ideal of `A` above `(p)`. -/
theorem character_value_sub_mem_primeIdealOverPrime_of_pRegularComponents_galoisPowerConjugate
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) {x y : G}
    (hxy :
      pRegularGaloisPowerClassMk ΓK p
          ⟨pRegularComponent p x, isPRegular_pRegularComponent (p := p) x⟩ =
        pRegularGaloisPowerClassMk ΓK p
          ⟨pRegularComponent p y, isPRegular_pRegularComponent (p := p) y⟩)
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = f x - f y := by
  -- Reduce to the `p'`-components, where the `Γ_K`-power hypothesis gives literal equality of
  -- values, and isolate the remaining arithmetic comparison in the one-variable helper above.
  have hxyValue :
      f (pRegularComponent p x) = f (pRegularComponent p y) :=
    pRegularComponentValueEqOfGaloisPowerClassEq
      (K := K) (A := A) (p := p) hf hxy
  obtain ⟨qx, hqx⟩ :=
    characterValueSubMemPrimeIdealOverPrimeOfPRegularComponent
      (K := K) (A := A) (p := p) hf x Q hQ
  obtain ⟨qy, hqy⟩ :=
    characterValueSubMemPrimeIdealOverPrimeOfPRegularComponent
      (K := K) (A := A) (p := p) hf y Q hQ
  refine ⟨⟨qx.1 - qy.1, Q.asIdeal.sub_mem qx.2 qy.2⟩, ?_⟩
  -- Subtract the two one-variable congruences and cancel the common `p'`-component value.
  calc
    algebraMap A K (qx.1 - qy.1) =
        algebraMap A K qx.1 - algebraMap A K qy.1 := by
          simp
    _ = (f x - f (pRegularComponent p x)) - (f y - f (pRegularComponent p y)) := by
          rw [hqx, hqy]
    _ = f x - f y := by
          rw [hxyValue]
          ring

end

end Representation
