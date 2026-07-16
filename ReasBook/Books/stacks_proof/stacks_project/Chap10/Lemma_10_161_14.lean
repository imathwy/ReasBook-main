import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_25_1
import stacks_proof.stacks_project.Chap10.Lemma_10_37_12
import stacks_proof.stacks_project.Chap10.Lemma_10_37_13
import stacks_proof.stacks_project.Chap10.Lemma_10_37_17
import stacks_proof.stacks_project.Chap10.Lemma_10_63_15
import stacks_proof.stacks_project.Chap10.Lemma_10_63_16
import stacks_proof.stacks_project.Chap10.Lemma_10_119_2_Koll_r
import stacks_proof.stacks_project.Chap10.Lemma_10_119_3
import stacks_proof.stacks_project.Chap10.Proposition_10_110_1
import stacks_proof.stacks_project.Chap10.Lemma_10_157_2
import stacks_proof.stacks_project.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped Pointwise

/- 
Domain-style sampling:
* primary domain: the normal locus on `Spec R` in commutative algebra;
* sampled owner declarations of the same kind:
  `IsNormalRing`,
  `IsNormalRing.isNormalLocalizationAtPrime`,
  `isIntegrallyClosed_of_isNormalRing`,
  `IsLocalization.isDomain_of_atPrime`;
* best owner abstraction: membership in the normal locus is owned by
  `IsNormalRing (Localization.AtPrime p.asIdeal)`;
* primitive data vs. derived API: the primitive pointwise datum is the local normal-ring owner
  `IsNormalRing (Localization.AtPrime p.asIdeal)`, while the domain and integrally-closed views are
  derived API under the ambient domain hypothesis.

Source/core/bridge triage:
* `source-facing`: the normal locus of `Spec R` and the theorem that it is open under the
  existence of one normal principal localization;
* `core/canonical`: `Localization.AtPrime`, `Localization.Away`, and the owner `IsNormalRing`;
* `bridge/view`: the domain-specialized equivalence with integrally closed prime localizations.
-/

namespace PrimeSpectrum

/-- The normal locus of `Spec R`, consisting of the primes whose local rings are normal. -/
def normalLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  { p | IsNormalRing (Localization.AtPrime p.asIdeal) }

/-- Membership in `PrimeSpectrum.normalLocus R` means that the corresponding local ring is
normal. -/
theorem mem_normalLocus {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    p ∈ normalLocus R ↔
      IsNormalRing (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

/-- Over a domain, membership in `PrimeSpectrum.normalLocus R` is equivalent to the corresponding
prime localization being integrally closed. -/
theorem mem_normalLocus_iff_isIntegrallyClosed {R : Type u} [CommRing R] [IsDomain R]
    (p : PrimeSpectrum R) :
    p ∈ normalLocus R ↔
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  rw [mem_normalLocus]
  constructor
  · intro hp
    letI : IsNormalRing (Localization.AtPrime p.asIdeal) := hp
    infer_instance
  · intro hp
    letI : IsDomain (Localization.AtPrime p.asIdeal) :=
      IsLocalization.isDomain_of_atPrime (Localization.AtPrime p.asIdeal) p.asIdeal
    letI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := hp
    infer_instance

end PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.14: localizing `QuotSMulTop a R` at `p` agrees with quotienting the
localized ring by the image of `a`. -/
noncomputable def localized_quotSMulTop_atPrime_equiv
    (p : PrimeSpectrum R) (a : R) :
    LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R) ≃ₗ[Localization.AtPrime p.asIdeal]
      QuotSMulTop (algebraMap R (Localization.AtPrime p.asIdeal) a)
        (Localization.AtPrime p.asIdeal) :=
  let e₁ := LocalizedModule.equivTensorProduct (R := R) p.asIdeal.primeCompl (QuotSMulTop a R)
  let e₂ := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
    (R := R) (r := a) (M := R) (Localization.AtPrime p.asIdeal)).symm
  let e₃ := QuotSMulTop.congr (algebraMap R (Localization.AtPrime p.asIdeal) a)
    (LocalizedModule.equivTensorProduct (R := R) p.asIdeal.primeCompl R).symm
  e₁.trans (e₂.trans e₃)

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.14: a Noetherian normal local domain satisfies the depth lower bound
coming from `(S₂)`. -/
lemma local_normal_domain_depth_ge_min_two
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] :
    WithBot.some (moduleDepth A A : ℕ∞) ≥
      min (2 : WithBot ℕ∞) (ringKrullDim A) := by
  -- Proof comment: reuse the same dimension trichotomy as in Serre's criterion for normality.
  by_cases hdim0 : ringKrullDim A = 0
  · -- Proof comment: in dimension `0`, the lower bound is immediate.
    simpa [hdim0]
  · by_cases hdim1 : ringKrullDim A = 1
    · -- Proof comment: in dimension `1`, a normal local domain is a DVR and hence
      -- Cohen-Macaulay.
      have hNormalDimOne :
          ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
            (_ : IsIntegrallyClosed A), ringKrullDim A = 1 := by
        exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim1⟩
      have hRegDim : IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
        exact ((discreteValuationRing_tfae (A := A)).out 4 2).mp hNormalDimOne
      letI : IsRegularLocalRing A := hRegDim.1
      have hCM : Module.CohenMacaulay A A := inferInstance
      have hdepth_eq :
          WithBot.some (moduleDepth A A : ℕ∞) = 1 := by
        simpa [Module.supportDim_self_eq_ringKrullDim, hRegDim.2] using
          hCM.supportDim_eq_moduleDepth.symm
      simpa [hdim1, hdepth_eq]
    · -- Proof comment: outside dimensions `0` and `1`, the Kollár trichotomy forces depth at
      -- least `2`.
      have hArtFalse : ¬ IsArtinianRing A := by
        intro hArt
        exact hdim0 <|
          ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
            ((isArtinianRing_iff_krullDimLE_zero).mp hArt)
      have hRegFalse : ¬ (IsRegularLocalRing A ∧ ringKrullDim A = 1) := by
        rintro ⟨_, hdimA⟩
        exact hdim1 hdimA
      have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension A :=
        not_hasKollarExceptionalFiniteExtension_of_normal_local_domain_of_krullDim_ne_zero
          (A := A) hdim0
      have hxor :=
        kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension
          (R := A)
      have hdepth : (2 : WithTop ℕ) ≤ moduleDepth A A := by
        simpa [Xor', hArtFalse, hRegFalse, hExceptionalFalse] using hxor
      have hdepth_enat : (2 : ℕ∞) ≤ moduleDepth A A := by
        simpa using hdepth
      have hdepth_bot : (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A A : ℕ∞) := by
        simpa [WithBot.some_eq_coe] using (WithBot.coe_le_coe.2 hdepth_enat)
      exact le_trans (min_le_left _ _) hdepth_bot

/-- Helper for Lemma 10.161.14: `(R₁)` is exactly the primewise regularity condition in codimension
at most `1`. -/
lemma serreConditionR_one_iff_forall_isRegularLocalRing
    {A : Type*} [CommRing A] [IsNoetherianRing A] :
    SerreConditionR A 1 ↔
      ∀ q : PrimeSpectrum A,
        q.asIdeal.primeHeight ≤ 1 →
          IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  constructor
  · intro h q hq
    -- Proof comment: this is the defining field of the `(R₁)` owner.
    exact h.isRegularLocalRing_localizationAtPrime q hq
  · intro h
    -- Proof comment: rebuild the owner from the primewise codimension-one clause.
    exact
      { toIsNoetherian := inferInstance
        isRegularLocalRing_localizationAtPrime := h }

/-- Helper for Lemma 10.161.14: `(S₂)` is exactly the primewise depth lower bound. -/
lemma serreConditionS_two_iff_forall_moduleDepth_ge_min
    {A : Type*} [CommRing A] [IsNoetherianRing A] :
    SerreConditionS A 2 ↔
      ∀ q : PrimeSpectrum A,
        WithBot.some
            (moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :
              ℕ∞) ≥
          min (2 : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q.asIdeal)) := by
  constructor
  · intro h q
    -- Proof comment: this is the self-module specialization already exposed by the chapter API.
    exact SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := A) h q
  · intro h
    -- Proof comment: package the primewise depth estimates back into the `(S₂)` owner.
    exact
      { toIsNoetherian := inferInstance
        toSerreConditionS := by
          refine
            { toFinite := inferInstance
              moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
          intro q
          simpa [Module.supportDim_self_eq_ringKrullDim] using h q }

/-- Helper for Lemma 10.161.14: inside the self-module `A`, the submodule generated by one scalar
is the principal ideal that scalar generates. -/
lemma quotSMulTop_submodule_eq_principal_ideal
    {A : Type*} [CommRing A] (a : A) :
    a • (⊤ : Submodule A A) = Ideal.span ({a} : Set A) := by
  -- Proof comment: rewrite the scalar multiple of the whole ring as the span of the singleton
  -- generator.
  simp [← Submodule.ideal_span_singleton_smul]

/-- Helper for Lemma 10.161.14: the self-module quotient `A / aA` is the usual principal ring
quotient. -/
noncomputable def quotSMulTop_to_principal_quotient_linearEquiv
    {A : Type*} [CommRing A] (a : A) :
    QuotSMulTop a A ≃ₗ[A] A ⧸ Ideal.span ({a} : Set A) :=
  Submodule.quotEquivOfEq (a • (⊤ : Submodule A A)) (Ideal.span ({a} : Set A))
    (quotSMulTop_submodule_eq_principal_ideal (A := A) a)

/-- Helper for Lemma 10.161.14: in a local ring, every element outside the maximal ideal is a
unit. -/
lemma primeCompl_le_isUnit_submonoid_of_local
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).primeCompl ≤ IsUnit.submonoid A := by
  -- Proof comment: the complement of the maximal ideal is exactly the unit group in a local ring.
  intro x hx
  simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Classical.not_not] using hx

/-- Helper for Lemma 10.161.14: a local ring is canonically the localization at the complement of
its maximal ideal. -/
noncomputable def localization_at_maximal_ringEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
  letI : IsLocalization (maximalIdeal A).primeCompl A :=
    IsLocalization.self (primeCompl_le_isUnit_submonoid_of_local A)
  IsLocalization.algEquiv (maximalIdeal A).primeCompl
    (Localization.AtPrime (maximalIdeal A)) A

/-- Helper for Lemma 10.161.14: the basic open `D(f)` lies in the normal locus when `R_f`
is normal. This early copy is used by the Serre-descent helper before the later public helper
declaration appears in the file. -/
lemma mem_normalLocus_of_mem_basicOpen_of_normalAway
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {f : R} (hAway : IsNormalRing (Localization.Away f)) {p : PrimeSpectrum R}
    (hp : p ∈ PrimeSpectrum.basicOpen f) :
    p ∈ PrimeSpectrum.normalLocus R := by
  -- Proof comment: choose a prime of `Spec(R_f)` over `p`, localize the normal ring `R_f` there,
  -- and compare the resulting local ring with `R_p`.
  obtain ⟨qAway, hqAway⟩ :
      ∃ qAway : PrimeSpectrum (Localization.Away f),
        PrimeSpectrum.comap (algebraMap R (Localization.Away f)) qAway = p := by
    have hrange :
        p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      simpa [PrimeSpectrum.mem_basicOpen] using hp
    exact Set.mem_range.mp hrange
  letI : IsNormalRing (Localization.Away f) := hAway
  have hqAway_normal : IsNormalRing (Localization.AtPrime qAway.asIdeal) :=
    isNormalRing_of_isLocalization qAway.asIdeal.primeCompl
  have hqAway_asIdeal :
      Ideal.comap (algebraMap R (Localization.Away f)) qAway.asIdeal = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqAway
  letI : IsLocalization.AtPrime (Localization.AtPrime qAway.asIdeal) p.asIdeal := by
    simpa [hqAway_asIdeal] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers f)
        (Localization.AtPrime qAway.asIdeal)
        qAway.asIdeal)
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime qAway.asIdeal :=
    IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime qAway.asIdeal)
  exact (PrimeSpectrum.mem_normalLocus p).2 <|
    isNormalRing_of_equiv e.symm.toRingEquiv

/-- Helper for Lemma 10.161.14: associated primes of the principal quotient can be computed on the
transport-stable `QuotSMulTop` model and converted back only once globally. -/
lemma associatedPrimes_principal_quotient_eq_associatedPrimes_quotSMulTop
    {A : Type*} [CommRing A] [IsNoetherianRing A] (a : A) :
    associatedPrimes A (A ⧸ Ideal.span ({a} : Set A)) =
      associatedPrimes A (QuotSMulTop a A) := by
  -- Proof comment: rewrite both sides to the textbook associated-prime owner and transport along
  -- the canonical equivalence between `QuotSMulTop a A` and `A / (a)`.
  rw [← associatedPrimesOfModule_eq_associatedPrimes (R := A)
      (M := A ⧸ Ideal.span ({a} : Set A)),
    ← associatedPrimesOfModule_eq_associatedPrimes (R := A)
      (M := QuotSMulTop a A)]
  simpa using
    (LinearEquiv.associatedPrimesOfModule_eq (R := A)
      (M := QuotSMulTop a A) (M' := A ⧸ Ideal.span ({a} : Set A))
      (quotSMulTop_to_principal_quotient_linearEquiv (A := A) a)).symm

/-- Helper for Lemma 10.161.14: in a Noetherian local domain, a nonzero maximal-ideal element
forces the closed point to be associated to the quotient module `A / aA` in the stable
`QuotSMulTop` model as soon as the local ring has Krull dimension `1`. -/
lemma maximalIdeal_mem_associatedPrimes_quotSMulTop_of_ringKrullDim_eq_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    {a : A} (ha0 : a ≠ 0) (haM : a ∈ maximalIdeal A) (hdim : ringKrullDim A = 1) :
    maximalIdeal A ∈ associatedPrimes A (QuotSMulTop a A) := by
  -- Proof comment: the source `(R₁)` branch only needs the closed point to be associated to the
  -- one-dimensional local quotient; the standard depth-`≥ 2` contradiction gives this directly on
  -- `QuotSMulTop`, avoiding any extra transport.
  by_contra hnot
  have hdepth_ge_two : (2 : ℕ∞) ≤ moduleDepth A A := by
    simpa using
      (depth_ge_two_of_regular_element_and_maximalIdeal_not_mem_associatedPrimes_quotSMulTop
        (R := A) haM (IsSMulRegular.of_ne_zero ha0) hnot)
  have hdepth_le : moduleDepth A A ≤ 1 :=
    moduleDepth_self_le_one_of_ringKrullDim_eq_one (R := A) hdim
  have : (2 : ℕ∞) ≤ 1 := le_trans hdepth_ge_two hdepth_le
  norm_num at this

/-- Helper for Lemma 10.161.14: in a Noetherian local domain, a nonzero maximal-ideal element
whose principal quotient does not have the closed point associated would force depth at least
`2`; hence depth `< 2` makes the closed point associated to the principal quotient. -/
lemma maximalIdeal_mem_associatedPrimes_principal_quotient_of_moduleDepth_lt_two
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    {a : A} (ha0 : a ≠ 0) (haM : a ∈ maximalIdeal A) (hdepth : moduleDepth A A < 2) :
    maximalIdeal A ∈ associatedPrimes A (A ⧸ Ideal.span ({a} : Set A)) := by
  -- Proof comment: prove the source Case I conclusion first on `QuotSMulTop a A`, where the depth
  -- lemma already lives, and only then rewrite back to the textbook quotient `A / (a)`.
  have hquot :
      maximalIdeal A ∈ associatedPrimes A (QuotSMulTop a A) := by
    -- Proof comment: depth `< 2` rules out the negation because the same standard theorem would
    -- force depth `≥ 2`.
    by_contra hnot
    have hdepth_ge_two : (2 : ℕ∞) ≤ moduleDepth A A := by
      simpa using
        (depth_ge_two_of_regular_element_and_maximalIdeal_not_mem_associatedPrimes_quotSMulTop
          (R := A) haM (IsSMulRegular.of_ne_zero ha0) hnot)
    exact (not_lt_of_ge hdepth_ge_two) hdepth
  simpa [associatedPrimes_principal_quotient_eq_associatedPrimes_quotSMulTop (A := A) a] using
    hquot

/-- Helper for Lemma 10.161.14: a codimension-`≤ 1` Serre-bad localization of a Noetherian domain
has depth `< 2`. -/
lemma moduleDepth_lt_two_of_height_le_one_and_not_regular
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : PrimeSpectrum A)
    (hqle : q.asIdeal.primeHeight ≤ 1)
    (hnotreg : ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal)) :
    moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) < 2 := by
  let B := Localization.AtPrime q.asIdeal
  by_cases hq0 : q.asIdeal.primeHeight = 0
  · -- Proof comment: a height-zero localization of a domain is a field, hence regular local,
    -- contradicting the Serre-bad hypothesis.
    have hdim0 : ringKrullDim B = 0 := by
      calc
        ringKrullDim B = q.asIdeal.height := by
          simpa [B] using (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal B)
        _ = q.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 0 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hq0
    letI : Ring.KrullDimLE 0 B := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
    letI : Field B := (Ring.KrullDimLE.isField_of_isDomain (R := B)).toField
    have hreg : IsRegularLocalRing B := by
      infer_instance
    exact False.elim <| hnotreg <| by simpa [B] using hreg
  · -- Proof comment: once height zero is excluded, codimension `≤ 1` forces height exactly `1`,
    -- so the existing one-dimensional depth bound gives `depth ≤ 1 < 2`.
    have hq1 : q.asIdeal.primeHeight = 1 := by
      exact le_antisymm hqle (ENat.one_le_iff_ne_zero.2 hq0)
    have hdim1 : ringKrullDim B = 1 := by
      calc
        ringKrullDim B = q.asIdeal.height := by
          simpa [B] using (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal B)
        _ = q.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 1 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hq1
    have hdepth_le : moduleDepth B B ≤ 1 :=
      moduleDepth_self_le_one_of_ringKrullDim_eq_one (R := B) hdim1
    exact lt_of_le_of_lt hdepth_le (by norm_num)

/-- Helper for Lemma 10.161.14: a codimension-`≤ 1` nonregular localization of a Noetherian
domain has Krull dimension exactly `1`. -/
lemma ringKrullDim_eq_one_of_height_le_one_and_not_regular
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : PrimeSpectrum A)
    (hqle : q.asIdeal.primeHeight ≤ 1)
    (hnotreg : ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal)) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 1 := by
  let B := Localization.AtPrime q.asIdeal
  by_cases hq0 : q.asIdeal.primeHeight = 0
  · -- Proof comment: a height-zero localization of a domain is a field, hence regular local,
    -- contradicting the nonregular hypothesis.
    have hdim0 : ringKrullDim B = 0 := by
      calc
        ringKrullDim B = q.asIdeal.height := by
          simpa [B] using (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal B)
        _ = q.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 0 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hq0
    letI : Ring.KrullDimLE 0 B := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
    letI : Field B := (Ring.KrullDimLE.isField_of_isDomain (R := B)).toField
    have hreg : IsRegularLocalRing B := by
      infer_instance
    exact False.elim <| hnotreg <| by simpa [B] using hreg
  · -- Proof comment: once height zero is excluded, codimension `≤ 1` forces height exactly `1`,
    -- and the local Krull-dimension/height comparison gives the required equality.
    have hq1 : q.asIdeal.primeHeight = 1 := by
      exact le_antisymm hqle (ENat.one_le_iff_ne_zero.2 hq0)
    calc
      ringKrullDim B = q.asIdeal.height := by
        simpa [B] using (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal B)
      _ = q.asIdeal.primeHeight := by
        rw [Ideal.height_eq_primeHeight]
      _ = 1 := by
        simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hq1

/-- Helper for Lemma 10.161.14: either explicit source-style Serre-bad case forces the
corresponding localization to be nonnormal. -/
lemma not_isNormalRing_of_serre_bad_atPrime
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {q : PrimeSpectrum A}
    (hbad :
      (moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) < 2 ∧
          2 ≤ ringKrullDim (Localization.AtPrime q.asIdeal)) ∨
        (ringKrullDim (Localization.AtPrime q.asIdeal) = 1 ∧
          ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal))) :
    ¬ IsNormalRing (Localization.AtPrime q.asIdeal) := by
  let B := Localization.AtPrime q.asIdeal
  intro hnormal
  letI : IsNormalRing B := hnormal
  rcases hbad with hS2 | hR1
  · rcases hS2 with ⟨hdepth, hdim⟩
    -- Proof comment: a normal local domain satisfies the source `(S₂)` depth lower bound, so
    -- depth `< 2` is impossible once the dimension is at least `2`.
    have hdepth_ge :
        WithBot.some (moduleDepth B B : ℕ∞) ≥
          min (2 : WithBot ℕ∞) (ringKrullDim B) :=
      local_normal_domain_depth_ge_min_two B
    have hmin : min (2 : WithBot ℕ∞) (ringKrullDim B) = 2 := by
      exact min_eq_left <| by exact_mod_cast hdim
    have hdepth_ge_two : (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth B B : ℕ∞) := by
      simpa [hmin] using hdepth_ge
    have hdepth_lt_two : WithBot.some (moduleDepth B B : ℕ∞) < 2 := by
      change (((moduleDepth B B : ℕ∞) : WithBot ℕ∞) < 2)
      exact WithBot.coe_lt_coe.2 hdepth
    exact (not_lt_of_ge hdepth_ge_two) hdepth_lt_two
  · rcases hR1 with ⟨hdim, hnotreg⟩
    -- Proof comment: a one-dimensional normal local domain is a DVR, hence regular local.
    have hNormalDimOne :
        ∃ (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : IsDomain B)
          (_ : IsIntegrallyClosed B), ringKrullDim B = 1 := by
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim⟩
    have hRegDim : IsRegularLocalRing B ∧ ringKrullDim B = 1 := by
      exact ((discreteValuationRing_tfae (A := B)).out 4 2).mp hNormalDimOne
    exact hnotreg hRegDim.1

/-- Helper for Lemma 10.161.14: a nonnormal Noetherian domain has a prime localization where the
source proof's Case I or Case II witness appears explicitly. -/
lemma exists_serre_bad_prime_of_not_isNormalRing
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : ¬ IsNormalRing A) :
    ∃ q : PrimeSpectrum A,
      ¬ IsNormalRing (Localization.AtPrime q.asIdeal) ∧
        ((moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) < 2 ∧
            2 ≤ ringKrullDim (Localization.AtPrime q.asIdeal)) ∨
          (ringKrullDim (Localization.AtPrime q.asIdeal) = 1 ∧
            ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal))) := by
  have hSerre :
      ¬ (SerreConditionR A 1 ∧ SerreConditionS A 2) := by
    intro hASerre
    exact hA <|
      (isNormalRing_iff_serreConditionR_one_and_serreConditionS_two (R := A)).2 hASerre
  by_cases hR : SerreConditionR A 1
  · have hS : ¬ SerreConditionS A 2 := by
      intro hS
      exact hSerre ⟨hR, hS⟩
    have hSfail :
        ¬ ∀ q : PrimeSpectrum A,
          WithBot.some
              (moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :
                ℕ∞) ≥
            min (2 : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q.asIdeal)) := by
      simpa [serreConditionS_two_iff_forall_moduleDepth_ge_min (A := A)] using hS
    rcases not_forall.mp hSfail with ⟨q, hq⟩
    let B := Localization.AtPrime q.asIdeal
    have hfail :
        WithBot.some (moduleDepth B B : ℕ∞) <
          min (2 : WithBot ℕ∞) (ringKrullDim B) := by
      simpa [B] using lt_of_not_ge hq
    have hRlocal :
        ∀ q : PrimeSpectrum A,
          q.asIdeal.primeHeight ≤ 1 →
            IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
      (serreConditionR_one_iff_forall_isRegularLocalRing (A := A)).1 hR
    by_cases hdim : (2 : ℕ∞) ≤ ringKrullDim B
    · -- Proof comment: when the local dimension is at least `2`, failure of `(S₂)` is already
      -- the source Case I witness.
      have hmin : min (2 : WithBot ℕ∞) (ringKrullDim B) = 2 := by
        exact min_eq_left <| by exact_mod_cast hdim
      have hdepth' : WithBot.some (moduleDepth B B : ℕ∞) < 2 := by
        simpa [hmin] using hfail
      have hdepth : moduleDepth B B < 2 := by
        have hdepth'' : (((moduleDepth B B : ℕ∞) : WithBot ℕ∞) < 2) := by
          simpa [WithBot.some_eq_coe] using hdepth'
        exact WithBot.coe_lt_coe.mp hdepth''
      have hdim' : (2 : ℕ∞) ≤ ringKrullDim B := hdim
      have hbad :
          (moduleDepth B B < 2 ∧ 2 ≤ ringKrullDim B) := ⟨hdepth, hdim'⟩
      exact ⟨q, not_isNormalRing_of_serre_bad_atPrime (q := q) (Or.inl hbad), Or.inl hbad⟩
    · -- Proof comment: if the dimension were `< 2`, then `(R₁)` would make this localization
      -- regular, forcing Cohen-Macaulay depth equality and contradicting the failed `(S₂)` bound.
      have hdim_lt : ringKrullDim B < 2 := lt_of_not_ge hdim
      have hdim_lt' : (ringKrullDim B : WithBot ℕ∞) < 2 := by
        simpa [WithBot.some_eq_coe] using hdim_lt
      have hdim_le_one' : (ringKrullDim B : WithBot ℕ∞) ≤ 1 := by
        simpa using (ENat.WithBot.lt_add_one_iff).mp <| by simpa using hdim_lt'
      have hheight_le' : ((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
        calc
          ((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) = q.asIdeal.height := by
            rw [Ideal.height_eq_primeHeight]
          _ = ringKrullDim B := by
            simpa [B] using
              (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal B).symm
          _ ≤ 1 := hdim_le_one'
      have hheight_le : q.asIdeal.primeHeight ≤ 1 := by
        exact_mod_cast hheight_le'
      letI : IsRegularLocalRing B := hRlocal q hheight_le
      have hdepth_eq : WithBot.some (moduleDepth B B : ℕ∞) = ringKrullDim B := by
        have hCM : Module.CohenMacaulay B B := inferInstance
        simpa [Module.supportDim_self_eq_ringKrullDim] using hCM.supportDim_eq_moduleDepth.symm
      have hmin : min (2 : WithBot ℕ∞) (ringKrullDim B) = ringKrullDim B := by
        exact min_eq_right <| by exact_mod_cast (le_of_lt hdim_lt)
      rw [hmin, hdepth_eq] at hfail
      exact False.elim <| lt_irrefl _ hfail
  · have hRfail :
        ¬ ∀ q : PrimeSpectrum A,
          q.asIdeal.primeHeight ≤ 1 →
            IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
      simpa [serreConditionR_one_iff_forall_isRegularLocalRing (A := A)] using hR
    push Not at hRfail
    rcases hRfail with ⟨q, hqle, hnotreg⟩
    have hdim1 :
        ringKrullDim (Localization.AtPrime q.asIdeal) = 1 :=
      ringKrullDim_eq_one_of_height_le_one_and_not_regular q hqle hnotreg
    have hbad :
        ringKrullDim (Localization.AtPrime q.asIdeal) = 1 ∧
          ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
      ⟨hdim1, hnotreg⟩
    exact ⟨q, not_isNormalRing_of_serre_bad_atPrime (q := q) (Or.inr hbad), Or.inr hbad⟩

/-- Helper for Lemma 10.161.14: once `f ∈ q`, either explicit Serre-bad case at `R_q` makes the
closed point associated to the localized principal quotient in the stable `QuotSMulTop` model. -/
lemma maximalIdeal_mem_associatedPrimes_quotSMulTop_of_serre_bad_atPrime
    {f : R} (hf0 : f ≠ 0) {q : PrimeSpectrum R}
    (hfq : f ∈ q.asIdeal)
    (hbad :
      (moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) < 2 ∧
          2 ≤ ringKrullDim (Localization.AtPrime q.asIdeal)) ∨
        (ringKrullDim (Localization.AtPrime q.asIdeal) = 1 ∧
          ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal))) :
    maximalIdeal (Localization.AtPrime q.asIdeal) ∈
      associatedPrimes (Localization.AtPrime q.asIdeal)
        (QuotSMulTop (algebraMap R (Localization.AtPrime q.asIdeal) f)
          (Localization.AtPrime q.asIdeal)) := by
  let B := Localization.AtPrime q.asIdeal
  have hfB0 : algebraMap R B f ≠ 0 := by
    -- Proof comment: localization at a prime of a domain is injective.
    intro hfB
    apply hf0
    exact (IsLocalization.injective B q.asIdeal.primeCompl_le_nonZeroDivisors) (by simpa using hfB)
  have hfBM : algebraMap R B f ∈ maximalIdeal B := by
    -- Proof comment: membership in the maximal ideal of `R_q` is exactly membership in `q`.
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff B q.asIdeal f).2 hfq
  rcases hbad with hS2 | hR1
  · rcases hS2 with ⟨hdepth, _⟩
    -- Proof comment: the source Case I conclusion is already proved for the principal quotient,
    -- and we rewrite once to the stable `QuotSMulTop` model.
    have hprincipal :
        maximalIdeal B ∈ associatedPrimes B (B ⧸ Ideal.span ({algebraMap R B f} : Set B)) :=
      maximalIdeal_mem_associatedPrimes_principal_quotient_of_moduleDepth_lt_two
        (A := B) hfB0 hfBM hdepth
    simpa [B, associatedPrimes_principal_quotient_eq_associatedPrimes_quotSMulTop
      (A := B) (algebraMap R B f)] using hprincipal
  · rcases hR1 with ⟨hdim, hnotreg⟩
    -- Proof comment: the source Case II branch is exactly the one-dimensional local witness.
    simpa [B] using
      maximalIdeal_mem_associatedPrimes_quotSMulTop_of_ringKrullDim_eq_one
        (A := B) hfB0 hfBM hdim

omit [IsDomain R] in
/-- Helper for Lemma 10.161.14: a localized `QuotSMulTop` associated-prime witness at `q`
contracts to `q` as an associated prime over `R`. -/
lemma mem_associatedPrimes_quotSMulTop_of_localized_witness
    {f : R} {q : PrimeSpectrum R}
    (hq :
      maximalIdeal (Localization.AtPrime q.asIdeal) ∈
        associatedPrimes (Localization.AtPrime q.asIdeal)
          (QuotSMulTop (algebraMap R (Localization.AtPrime q.asIdeal) f)
            (Localization.AtPrime q.asIdeal))) :
    q.asIdeal ∈ associatedPrimes R (QuotSMulTop f R) := by
  let B := Localization.AtPrime q.asIdeal
  have hq_text :
      maximalIdeal B ∈ associatedPrimesOfModule B
        (QuotSMulTop (algebraMap R B f) B) := by
    -- Proof comment: switch once from the owner associated-prime API to the chapter textbook API.
    simpa [B, associatedPrimesOfModule_eq_associatedPrimes] using hq
  have hq_localized_text :
      maximalIdeal B ∈ associatedPrimesOfModule B
        (LocalizedModule.AtPrime q.asIdeal (QuotSMulTop f R)) := by
    -- Proof comment: compare the localized global quotient with the local quotient using the
    -- canonical `localized_quotSMulTop_atPrime_equiv`.
    simpa [LinearEquiv.associatedPrimesOfModule_eq (R := B)
      (M := LocalizedModule.AtPrime q.asIdeal (QuotSMulTop f R))
      (M' := QuotSMulTop (algebraMap R B f) B)
      (localized_quotSMulTop_atPrime_equiv (R := R) q f)] using hq_text
  have hq_global_text :
      q.asIdeal ∈ associatedPrimesOfModule R (QuotSMulTop f R) :=
    mem_associatedPrimesOfModule_of_mem_associatedPrimesOfModule_atPrime_of_fg
      hq_localized_text (Ideal.fg_of_isNoetherianRing q.asIdeal)
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq_global_text

omit [IsDomain R] in
/-- Helper for Lemma 10.161.14: the source Serre-bad Case I/Case II disjunction transports across
the canonical comparison between a prime of `Spec(Rₚ)` and its contraction to `Spec(R)`. -/
lemma serre_bad_case_of_atPrime_contracted_compare
    (p : PrimeSpectrum R) (qA : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (hbad :
      (moduleDepth (Localization.AtPrime qA.asIdeal) (Localization.AtPrime qA.asIdeal) < 2 ∧
          2 ≤ ringKrullDim (Localization.AtPrime qA.asIdeal)) ∨
        (ringKrullDim (Localization.AtPrime qA.asIdeal) = 1 ∧
          ¬ IsRegularLocalRing (Localization.AtPrime qA.asIdeal))) :
    (moduleDepth (Localization.AtPrime (qA.asIdeal.under R))
        (Localization.AtPrime (qA.asIdeal.under R)) < 2 ∧
      2 ≤ ringKrullDim (Localization.AtPrime (qA.asIdeal.under R))) ∨
      (ringKrullDim (Localization.AtPrime (qA.asIdeal.under R)) = 1 ∧
        ¬ IsRegularLocalRing (Localization.AtPrime (qA.asIdeal.under R))) := by
  let A := Localization.AtPrime (qA.asIdeal.under R)
  let B := Localization.AtPrime qA.asIdeal
  let e := atPrime_contracted_localization_compare_to_under (R := R) p qA.asIdeal
  rcases hbad with hS2 | hR1
  · rcases hS2 with ⟨hdepthB, hdimB⟩
    -- Proof comment: transport the self-module depth along the induced `A`-linear equivalence,
    -- then move from the `A`-module view of `B` back to the ring `B` using surjectivity.
    letI : Algebra A B := e.toRingHom.toAlgebra
    have hsurj : Function.Surjective (algebraMap A B) := by
      simpa [A, B, e] using e.surjective
    let eA : A ≃ₗ[A] B :=
      LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨by
        simpa [A, B, e] using e.injective, hsurj⟩
    letI : Module.Finite A B := Module.Finite.equiv eA
    have hdepthAB : moduleDepth A A = moduleDepth A B := by
      -- Proof comment: replace the target module `B` by the source ring `A` via the comparison
      -- equivalence.
      simpa [eA] using moduleDepth_eq_of_equiv (R := A) (e := eA)
    have hdepthBB : moduleDepth A B = moduleDepth B B := by
      -- Proof comment: the algebra map `A → B` is surjective because it is the ring equivalence
      -- underlying `e`.
      simpa [A, B] using
        (moduleDepth_eq_of_surjective_local_algebra (A := A) (B := B) (N := B) hsurj)
    have hdepthA : moduleDepth A A < 2 := by
      rw [hdepthAB, hdepthBB]
      exact hdepthB
    have hdimAB : ringKrullDim A = ringKrullDim B := by
      simpa [A, B, e] using (ringKrullDim_eq_of_ringEquiv e.toRingEquiv)
    have hdimA : 2 ≤ ringKrullDim A := by
      rw [hdimAB]
      exact hdimB
    exact Or.inl ⟨hdepthA, hdimA⟩
  · rcases hR1 with ⟨hdimB, hnotregB⟩
    -- Proof comment: Krull dimension and regular-locality both transport directly across the ring
    -- equivalence `e`.
    have hdimAB : ringKrullDim A = ringKrullDim B := by
      simpa [A, B, e] using (ringKrullDim_eq_of_ringEquiv e.toRingEquiv)
    have hdimA : ringKrullDim A = 1 := by
      rw [hdimAB]
      exact hdimB
    have hnotregA : ¬ IsRegularLocalRing A := by
      intro hregA
      letI : IsRegularLocalRing A := hregA
      have hregB : IsRegularLocalRing B :=
        IsRegularLocalRing.of_ringEquiv (R := A) e.toRingEquiv
      exact hnotregB <| by simpa [B] using hregB
    exact Or.inr ⟨hdimA, hnotregA⟩

omit [IsDomain R] in
/-- Helper for Lemma 10.161.14: a Serre-bad prime of `Spec(Rₚ)` contracts to a Serre-bad prime
`q ≤ p` of `Spec(R)`. -/
lemma contracted_serre_bad_prime_below
    (p : PrimeSpectrum R) (qA : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (hbad :
      (moduleDepth (Localization.AtPrime qA.asIdeal) (Localization.AtPrime qA.asIdeal) < 2 ∧
          2 ≤ ringKrullDim (Localization.AtPrime qA.asIdeal)) ∨
        (ringKrullDim (Localization.AtPrime qA.asIdeal) = 1 ∧
          ¬ IsRegularLocalRing (Localization.AtPrime qA.asIdeal))) :
    ∃ q : PrimeSpectrum R,
      q ≤ p ∧
        ((moduleDepth (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) < 2 ∧
            2 ≤ ringKrullDim (Localization.AtPrime q.asIdeal)) ∨
          (ringKrullDim (Localization.AtPrime q.asIdeal) = 1 ∧
            ¬ IsRegularLocalRing (Localization.AtPrime q.asIdeal))) := by
  let Rp := Localization.AtPrime p.asIdeal
  let qp : Set.Iic p :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso Rp p.asIdeal) qA
  let q : PrimeSpectrum R := qp.1
  have hqle : q ≤ p := qp.2
  have hq_comap : PrimeSpectrum.comap (algebraMap R Rp) qA = q := by
    -- Proof comment: the prime-spectrum order isomorphism for `R → Rₚ` is literally the
    -- contraction map together with the proof that the contracted prime lies below `p`.
    change ((IsLocalization.AtPrime.primeSpectrumOrderIso Rp p.asIdeal qA).1 = q)
    rfl
  have hq_asIdeal :
      q.asIdeal = qA.asIdeal.under R := by
    have hq_comap_asIdeal :
        Ideal.comap (algebraMap R Rp) qA.asIdeal = q.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq_comap
    simpa [Ideal.under_def] using hq_comap_asIdeal.symm
  have hbad_under :
      (moduleDepth (Localization.AtPrime (qA.asIdeal.under R))
          (Localization.AtPrime (qA.asIdeal.under R)) < 2 ∧
        2 ≤ ringKrullDim (Localization.AtPrime (qA.asIdeal.under R))) ∨
        (ringKrullDim (Localization.AtPrime (qA.asIdeal.under R)) = 1 ∧
          ¬ IsRegularLocalRing (Localization.AtPrime (qA.asIdeal.under R))) :=
    serre_bad_case_of_atPrime_contracted_compare (R := R) p qA hbad
  refine ⟨q, hqle, ?_⟩
  simpa [hq_asIdeal] using hbad_under

/-- Helper for Lemma 10.161.14: every nonnormal prime contains a smaller nonnormal associated
prime of the principal quotient `R / (f)` coming from the source-proof Serre failure. -/
lemma exists_nonnormal_associated_prime_below_of_not_mem_normalLocus
    {f : R} (hf0 : f ≠ 0) (hAway : IsNormalRing (Localization.Away f))
    {p : PrimeSpectrum R} (hp : p ∉ PrimeSpectrum.normalLocus R) :
    ∃ q : PrimeSpectrum R,
      q ≤ p ∧
        q ∉ PrimeSpectrum.normalLocus R ∧
        q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span ({f} : Set R)) := by
  -- Route correction: the localization step should stay on `QuotSMulTop` via the canonical
  -- imported `localized_quotSMulTop_atPrime_equiv`, and only the final global output should be
  -- rewritten to `R / (f)` using
  -- `associatedPrimes_principal_quotient_eq_associatedPrimes_quotSMulTop`.
  let Rp := Localization.AtPrime p.asIdeal
  have hpRp : ¬ IsNormalRing Rp := by
    simpa [Rp, PrimeSpectrum.mem_normalLocus] using hp
  obtain ⟨qA, _, hqA_bad⟩ :=
    exists_serre_bad_prime_of_not_isNormalRing (A := Rp) hpRp
  obtain ⟨q, hqle, hq_bad⟩ :=
    contracted_serre_bad_prime_below (R := R) p qA hqA_bad
  have hq_not_normal_ring : ¬ IsNormalRing (Localization.AtPrime q.asIdeal) :=
    not_isNormalRing_of_serre_bad_atPrime (q := q) hq_bad
  have hq_not_normal : q ∉ PrimeSpectrum.normalLocus R := by
    simpa [PrimeSpectrum.mem_normalLocus] using hq_not_normal_ring
  have hfq : f ∈ q.asIdeal := by
    by_contra hfq
    have hq_basic : q ∈ PrimeSpectrum.basicOpen f := by
      simpa [PrimeSpectrum.mem_basicOpen] using hfq
    have hq_normal : q ∈ PrimeSpectrum.normalLocus R :=
      mem_normalLocus_of_mem_basicOpen_of_normalAway (R := R) hAway hq_basic
    exact hq_not_normal hq_normal
  have hq_local_assoc :
      maximalIdeal (Localization.AtPrime q.asIdeal) ∈
        associatedPrimes (Localization.AtPrime q.asIdeal)
          (QuotSMulTop (algebraMap R (Localization.AtPrime q.asIdeal) f)
            (Localization.AtPrime q.asIdeal)) :=
    maximalIdeal_mem_associatedPrimes_quotSMulTop_of_serre_bad_atPrime
      (R := R) hf0 hfq hq_bad
  have hq_assoc_quotSMulTop :
      q.asIdeal ∈ associatedPrimes R (QuotSMulTop f R) :=
    mem_associatedPrimes_quotSMulTop_of_localized_witness (R := R) hq_local_assoc
  have hq_assoc :
      q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span ({f} : Set R)) := by
    simpa [associatedPrimes_principal_quotient_eq_associatedPrimes_quotSMulTop (A := R) f] using
      hq_assoc_quotSMulTop
  exact ⟨q, hqle, hq_not_normal, hq_assoc⟩

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.14: the normal locus is stable under generization. -/
lemma mem_normalLocus_of_le {p q : PrimeSpectrum R} (hq : q ≤ p)
    (hp : p ∈ PrimeSpectrum.normalLocus R) :
    q ∈ PrimeSpectrum.normalLocus R := by
  -- Proof comment: identify `R_q` as a prime localization of the already normal local ring `R_p`
  -- and then transport normality back along the canonical comparison equivalence.
  let Rp := Localization.AtPrime p.asIdeal
  let qp : PrimeSpectrum Rp :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso Rp p.asIdeal).symm ⟨q, hq⟩
  have hcomap :
      PrimeSpectrum.comap (algebraMap R Rp) qp = q := by
    have hqp :
        IsLocalization.AtPrime.primeSpectrumOrderIso Rp p.asIdeal qp = ⟨q, hq⟩ := by
      simpa [qp] using
        (IsLocalization.AtPrime.primeSpectrumOrderIso Rp p.asIdeal).apply_symm_apply ⟨q, hq⟩
    simpa using congrArg Subtype.val hqp
  have hcomap_asIdeal :
      Ideal.comap (algebraMap R Rp) qp.asIdeal = q.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap
  letI : IsNormalRing Rp := (PrimeSpectrum.mem_normalLocus p).1 hp
  have hqp_normal : IsNormalRing (Localization.AtPrime qp.asIdeal) :=
    isNormalRing_of_isLocalization qp.asIdeal.primeCompl
  letI : IsLocalization.AtPrime (Localization.AtPrime qp.asIdeal) q.asIdeal := by
    simpa [hcomap_asIdeal] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        p.asIdeal.primeCompl
        (Localization.AtPrime qp.asIdeal)
        qp.asIdeal)
  let e : Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime qp.asIdeal :=
    IsLocalization.algEquiv q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime qp.asIdeal)
  exact (PrimeSpectrum.mem_normalLocus q).2 <|
    isNormalRing_of_equiv e.symm.toRingEquiv

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.14: the basic open `D(f)` lies in the normal locus when `R_f`
is normal. -/
lemma mem_normalLocus_of_mem_basicOpen_of_isNormalRing_localizationAway
    {f : R} (hAway : IsNormalRing (Localization.Away f)) {p : PrimeSpectrum R}
    (hp : p ∈ PrimeSpectrum.basicOpen f) :
    p ∈ PrimeSpectrum.normalLocus R := by
  -- Proof comment: choose a prime of `Spec(R_f)` over `p`, localize the normal ring `R_f` there,
  -- and compare the resulting local ring with `R_p`.
  obtain ⟨qAway, hqAway⟩ :
      ∃ qAway : PrimeSpectrum (Localization.Away f),
        PrimeSpectrum.comap (algebraMap R (Localization.Away f)) qAway = p := by
    have hrange :
        p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      simpa [PrimeSpectrum.mem_basicOpen] using hp
    exact Set.mem_range.mp hrange
  letI : IsNormalRing (Localization.Away f) := hAway
  have hqAway_normal : IsNormalRing (Localization.AtPrime qAway.asIdeal) :=
    isNormalRing_of_isLocalization qAway.asIdeal.primeCompl
  have hqAway_asIdeal :
      Ideal.comap (algebraMap R (Localization.Away f)) qAway.asIdeal = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqAway
  letI : IsLocalization.AtPrime (Localization.AtPrime qAway.asIdeal) p.asIdeal := by
    simpa [hqAway_asIdeal] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers f)
        (Localization.AtPrime qAway.asIdeal)
        qAway.asIdeal)
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime qAway.asIdeal :=
    IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime qAway.asIdeal)
  exact (PrimeSpectrum.mem_normalLocus p).2 <|
    isNormalRing_of_equiv e.symm.toRingEquiv

/- Helper route sketch for Lemma 10.161.14:
the remaining source-faithful step is to descend from `p ∉ normalLocus` to a smaller
prime `q ≤ p` such that `q` is both nonnormal and associated to `R / (f)`. The proved
generization and `D(f)` lemmas above already isolate the topological and localization API. -/

/-- Helper for Lemma 10.161.14: the complement of the normal locus is the union of the zero loci
of the finitely many nonnormal associated primes of the principal quotient `R / (f)`. -/
lemma normalLocus_compl_eq_biUnion_zeroLocus_nonnormal_associatedPrimes
    {f : R} (hf0 : f ≠ 0) (hAway : IsNormalRing (Localization.Away f)) :
    (PrimeSpectrum.normalLocus R)ᶜ =
      ⋃ q ∈ { q : PrimeSpectrum R |
          q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span ({f} : Set R)) ∧
            q ∉ PrimeSpectrum.normalLocus R},
        PrimeSpectrum.zeroLocus (q.asIdeal : Set R) := by
  classical
  let E : Set (PrimeSpectrum R) :=
    { q : PrimeSpectrum R |
      q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span ({f} : Set R)) ∧
        q ∉ PrimeSpectrum.normalLocus R }
  ext p
  constructor
  · intro hp
    -- Proof comment: descend from a nonnormal prime `p` to the source-proof bad prime `q ≤ p`,
    -- then record that `p` lies in the closed set `V(q)`.
    rcases
        exists_nonnormal_associated_prime_below_of_not_mem_normalLocus
          (R := R) hf0 hAway hp with
      ⟨q, hqle, hq_not_normal, hq_assoc⟩
    have hqE : q ∈ E := ⟨hq_assoc, hq_not_normal⟩
    refine Set.mem_iUnion.2 ⟨q, ?_⟩
    refine Set.mem_iUnion.2 ⟨hqE, ?_⟩
    simpa [PrimeSpectrum.mem_zeroLocus] using hqle
  · intro hp
    -- Proof comment: any point in one of those zero loci specializes a bad prime `q`, and
    -- normality is stable under generization.
    rcases Set.mem_iUnion.mp hp with ⟨q, hpq⟩
    rcases Set.mem_iUnion.mp hpq with ⟨hqE, hp_zero⟩
    have hqle : q ≤ p := by
      simpa [PrimeSpectrum.mem_zeroLocus] using hp_zero
    intro hp_normal
    exact hqE.2 (mem_normalLocus_of_le hqle hp_normal)

-- Proof sketch: choose `f ≠ 0` such that `Localization.Away f` is normal, so the basic open
-- `D(f)` lies in the normal locus. If `p` is not in the normal locus, Serre's criterion
-- yields a prime `q ≤ p` where either `(S_2)` fails or a height-one localization is not regular;
-- since `R_f` is normal, necessarily `f ∈ q`. These bad primes `q` are controlled by the finitely
-- many associated and embedded associated primes of `R ⧸ Ideal.span ({f} : Set R)`, so the
-- complement of the normal locus is a finite union of closed subsets `V(q)`.
/-- Lemma 10.161.14: if `R` is a Noetherian domain and some nonzero localization `R_f` is normal,
then the normal locus is open in `PrimeSpectrum R`. -/
@[stacks 0332]
theorem isOpen_normal_locus_of_exists_isNormalRing_localizationAway
    (h : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f)) :
    IsOpen (PrimeSpectrum.normalLocus R) := by
  classical
  rcases h with ⟨f, hf0, hAway⟩
  let E : Set (PrimeSpectrum R) :=
    { q : PrimeSpectrum R |
      q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span ({f} : Set R)) ∧
        q ∉ PrimeSpectrum.normalLocus R }
  have hcompl :
      (PrimeSpectrum.normalLocus R)ᶜ =
        ⋃ q ∈ E, PrimeSpectrum.zeroLocus (q.asIdeal : Set R) := by
    simpa [E] using
      normalLocus_compl_eq_biUnion_zeroLocus_nonnormal_associatedPrimes
        (R := R) hf0 hAway
  have hassoc_finite :
      (associatedPrimes R (R ⧸ Ideal.span ({f} : Set R))).Finite :=
    associatedPrimes.finite R (R ⧸ Ideal.span ({f} : Set R))
  have hcarrier_finite :
      { q : PrimeSpectrum R |
        q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span ({f} : Set R)) }.Finite := by
    let e : PrimeSpectrum R ↪ Ideal R :=
      ⟨PrimeSpectrum.asIdeal, fun p q hpq ↦ PrimeSpectrum.ext hpq⟩
    simpa [e] using Set.Finite.preimage_embedding e hassoc_finite
  have hE_finite : E.Finite := by
    exact hcarrier_finite.subset fun q hq ↦ hq.1
  have hclosed_compl : IsClosed ((PrimeSpectrum.normalLocus R)ᶜ) := by
    rw [hcompl]
    exact hE_finite.isClosed_biUnion fun q _ ↦
      PrimeSpectrum.isClosed_zeroLocus (q.asIdeal : Set R)
  simpa using hclosed_compl.isOpen_compl

/-- Domain-case companion to Lemma 10.161.14: for a domain, the source-facing normality
hypothesis on `R_f` can be replaced by integrally closedness. -/
theorem isOpen_normal_locus_of_exists_isIntegrallyClosed_localizationAway
    (h : ∃ f : R, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f)) :
    IsOpen (PrimeSpectrum.normalLocus R) := by
  apply isOpen_normal_locus_of_exists_isNormalRing_localizationAway
  rcases h with ⟨f, hf, hclosed⟩
  letI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  letI : IsIntegrallyClosed (Localization.Away f) := hclosed
  exact ⟨f, hf, inferInstance⟩

end
