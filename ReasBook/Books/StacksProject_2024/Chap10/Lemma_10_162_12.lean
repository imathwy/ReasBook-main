import Mathlib
import StacksProject_2024.Chap10.Definition_10_67_1
import StacksProject_2024.Chap10.Definition_10_162_9
import StacksProject_2024.Chap10.Lemma_10_63_2
import StacksProject_2024.Chap10.Lemma_10_63_19
import StacksProject_2024.Chap10.Lemma_10_65_3
import StacksProject_2024.Chap10.Lemma_10_65_5
import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_119_1
import StacksProject_2024.Chap10.Lemma_10_119_7
import StacksProject_2024.Chap10.Lemma_10_162_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

open IsLocalRing
open scoped TensorProduct

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
variable {x : R}

local notation "A" => R ⧸ Ideal.span (Set.singleton x)
local notation "RCompletion" => AdicCompletion (maximalIdeal R) R
local notation "J" =>
  Ideal.map (algebraMap R RCompletion) (Ideal.span (Set.singleton x))

/- Domain-style sampling:
- primary domain: analytically unramified Noetherian local domains, associated primes of
  principal quotients, and the no-embedded-primes condition on that quotient;
- sampled owner declarations:
  `IsAnalyticallyUnramified`,
  `PrimeSpectrum.IsAnalyticallyUnramified`,
  `embeddedAssociatedPrimes`,
  and `IsAssociatedPrime`;
- best owner abstraction: the theorem itself remains `source-facing`, but the quotient hypotheses
  should be expressed via the existing owner predicates `embeddedAssociatedPrimes R A = ∅` and
  `IsAssociatedPrime p.asIdeal A` rather than a parallel minimality condition and raw membership
  tests;
- primitive data vs. derived API: the primitive source data are the nonzero element `x` in the
  maximal ideal and the owner-level hypotheses on the quotient `A = R / xR`; the old “every
  associated prime is minimal” clause is derived bridge API for `embeddedAssociatedPrimes R A = ∅`.
-/

-- Proof sketch: let `R^∧` be the maximal-ideal completion of `R`. To prove it is reduced, take
-- `y : R^∧` with `y ^ 2 = 0`. Since `R / xR` has no embedded primes, the associated primes of
-- `R^∧ / xR^∧` are exactly the associated primes lying over the associated primes of `R / xR`.
-- For each such prime `q`, the corresponding localization `(R^∧)_q` is regular by Lemma
-- `10.162.11`, hence a domain by Lemma `10.106.2`, so `y` vanishes in every such localization.
-- Lemma `10.63.19` then shows `y = x y'`. Because `x` is a nonzerodivisor on the completion,
-- `y'` is again nilpotent; iterating and applying Krull intersection gives `y = 0`.
omit [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: the support of `R / xR` is exactly the zero locus of `(x)`. -/
lemma support_quotient_span_singleton_le_iff
    (p : PrimeSpectrum R) :
    p ∈ Module.support R A ↔ Ideal.span ({x} : Set R) ≤ p.asIdeal := by
  -- Rewrite the support of the quotient through its annihilator and identify that annihilator.
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.mem_zeroLocus]
  exact Iff.rfl

omit [IsLocalRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: if an associated prime of `R / xR` is minimal among the
associated primes of the quotient, then it is a minimal prime over `(x)`. -/
lemma associatedPrime_quotient_mem_minimalPrimes_span_singleton
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (p : PrimeSpectrum R) (hp : IsAssociatedPrime p.asIdeal A) :
    p.asIdeal ∈ (Ideal.span ({x} : Set R)).minimalPrimes :=
by
  have hp_assoc : p.asIdeal ∈ associatedPrimes R A := by
    simpa using hp
  -- Route correction: first convert the no-embedded-primes hypothesis into minimality inside
  -- `associatedPrimes R A`, then descend to minimality over the principal ideal `(x)`.
  have hp_min_assoc : Minimal (· ∈ associatedPrimes R A) p.asIdeal :=
    (embeddedAssociatedPrimes_eq_empty_iff (R := R) (M := A)).1 hno_embedded p.asIdeal hp_assoc
  have hp_support : p ∈ Module.support R A := by
    simpa using IsAssociatedPrime.mem_support hp
  have hx_le : Ideal.span ({x} : Set R) ≤ p.asIdeal :=
    (support_quotient_span_singleton_le_iff (R := R) (x := x) p).1 hp_support
  refine ⟨⟨hp.isPrime, hx_le⟩, ?_⟩
  intro q hq hqp
  -- Any prime between `(x)` and `p` contains a minimal prime over `(x)`, and that minimal prime is
  -- associated to `R / xR`; minimality among associated primes then forces equality with `p`.
  have hq_min_exists :
      ∃ r ∈ (Ideal.span ({x} : Set R)).minimalPrimes, r ≤ q := by
    letI : q.IsPrime := hq.1
    exact Ideal.exists_minimalPrimes_le hq.2
  obtain ⟨r, hr_min, hrq⟩ := hq_min_exists
  have hr_assoc : r ∈ associatedPrimes R A := by
    have hr_ann : r ∈ (Module.annihilator R A).minimalPrimes := by
      simpa [Ideal.annihilator_quotient] using hr_min
    simpa using
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        (R := R) (M := A) hr_ann)
  have hp_le_r : p.asIdeal ≤ r :=
    hp_min_assoc.2 hr_assoc (hrq.trans hqp)
  exact hp_le_r.trans hrq

omit [IsLocalRing R] in
/-- Helper for Lemma 10.162.12: each associated prime of `R / xR` yields a DVR localization of
`R`. -/
lemma associatedPrime_quotient_localization_isDiscreteValuationRing
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (p : PrimeSpectrum R) (hp : IsAssociatedPrime p.asIdeal A) :
    ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
by
  have hp_min :
      p.asIdeal ∈ (Ideal.span ({x} : Set R)).minimalPrimes :=
    associatedPrime_quotient_mem_minimalPrimes_span_singleton
      (R := R) (x := x) hno_embedded p hp
  have hdim : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    -- The localization at a height-one prime over a nonzero principal ideal has Krull dimension
    -- one.
    have hheight : p.asIdeal.primeHeight = 1 :=
      primeHeight_eq_one_of_mem_minimalPrimes_span_singleton_of_nonzero
      (x := x) hx0 p.asIdeal hp_min
    have hheight' : p.asIdeal.height = 1 := by
      simpa [Ideal.height_eq_primeHeight] using hheight
    exact
      (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
        (Localization.AtPrime p.asIdeal)).trans <| by
          simpa using hheight'
  -- A one-dimensional regular local ring is a discrete valuation ring.
  simpa using
    (show
        (∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
            IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)) ↔
          IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
            ringKrullDim (Localization.AtPrime p.asIdeal) = 1 from
        discreteValuationRing_iff_regularLocalRing_dim_one).2
      ⟨hregular p hp, hdim⟩

omit [IsNoetherianRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: localizing a quotient class and then identifying it with the
quotient of the localized ring sends a class `[y]` to the class of the localized numerator. -/
lemma localizedQuotientEquiv_symm_apply_mk
    (I : Ideal RCompletion) (S : Submonoid RCompletion) (y : RCompletion) :
    (localizedQuotientEquiv S (I : Submodule RCompletion RCompletion)).symm
      (LocalizedModule.mkLinearMap S (RCompletion ⧸ I) (Ideal.Quotient.mk I y)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S RCompletion y) :=
by
  -- The canonical localization equivalence is characterized by its action on quotient generators.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := S)
      (f := (I : Submodule RCompletion RCompletion).toLocalizedQuotient S)
      (g := LocalizedModule.mkLinearMap S (RCompletion ⧸ I))
      (x := Ideal.Quotient.mk I y))

/-- Helper for Lemma 10.162.12: quotienting the completion by `x R^∧` agrees with tensoring the
completion with `R / xR`. -/
noncomputable def completion_quotient_tensorQuotient_algEquiv :
    (RCompletion ⧸ J) ≃ₐ[RCompletion] (RCompletion ⊗[R] A) :=
  Algebra.TensorProduct.quotIdealMapEquivTensorQuot RCompletion
    (Ideal.span ({x} : Set R))

omit [IsDomain R] in
/-- Helper for Lemma 10.162.12: an associated prime of `R^∧ / xR^∧` contracts to an associated
prime of `R / xR`. -/
lemma completionQuotient_associatedPrime_under
    (q : PrimeSpectrum RCompletion)
    (hq : IsAssociatedPrime q.asIdeal (RCompletion ⧸ J)) :
    IsAssociatedPrime (PrimeSpectrum.comap (algebraMap R RCompletion) q).asIdeal A := by
  letI : Module.Flat R RCompletion := inferInstance
  letI : IsNoetherianRing RCompletion :=
    completion_isNoetherianRing (R := R)
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R RCompletion) q
  have hq_quot :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⧸ J) := by
    have hq_assoc : q.asIdeal ∈ associatedPrimes RCompletion (RCompletion ⧸ J) := by
      simpa using hq
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq_assoc
  have htransport :
      associatedPrimesOfModule RCompletion (RCompletion ⧸ J) =
        associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq (R := RCompletion)
        (M := RCompletion ⧸ J) (M' := RCompletion ⊗[R] A)
        (completion_quotient_tensorQuotient_algEquiv (R := R) (x := x)).toLinearEquiv)
  have hq_tensor :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    -- Transport the associated-prime witness across the quotient/tensor comparison first.
    exact htransport ▸ hq_quot
  have hq_fiber :
      q ∈ relativeAssassin R RCompletion RCompletion ∩
        { q : PrimeSpectrum RCompletion | q.asIdeal.under R ∈ associatedPrimesOfModule R A } := by
    rw [← associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
      (R := R) (S := RCompletion) (M := A) (N := RCompletion)]
    exact hq_tensor
  -- The contraction component of the flat-base-change theorem is the source associated prime.
  have hp_assoc_module : Ideal.IsAssociatedToModule R A p.asIdeal := by
    simpa [p, mem_associatedPrimesOfModule_iff] using hq_fiber.2
  exact (Ideal.isAssociatedToModule_iff_isAssociatedPrime R A p.asIdeal).mp hp_assoc_module

omit [IsDomain R] in
/-- Helper for Lemma 10.162.12: an associated prime of `R^∧ / xR^∧` lies on the branch over its
contracted source associated prime. -/
lemma completionQuotient_associatedPrime_branch
    (q : PrimeSpectrum RCompletion)
    (hq : IsAssociatedPrime q.asIdeal (RCompletion ⧸ J)) :
    IsAssociatedPrime q.asIdeal
      (RCompletion ⧸
        Ideal.map (algebraMap R RCompletion)
          (PrimeSpectrum.comap (algebraMap R RCompletion) q).asIdeal) := by
  letI : Module.Flat R RCompletion := inferInstance
  letI : IsNoetherianRing RCompletion :=
    completion_isNoetherianRing (R := R)
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R RCompletion) q
  have hq_quot :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⧸ J) := by
    have hq_assoc : q.asIdeal ∈ associatedPrimes RCompletion (RCompletion ⧸ J) := by
      simpa using hq
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq_assoc
  have htransport :
      associatedPrimesOfModule RCompletion (RCompletion ⧸ J) =
        associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq (R := RCompletion)
        (M := RCompletion ⧸ J) (M' := RCompletion ⊗[R] A)
        (completion_quotient_tensorQuotient_algEquiv (R := R) (x := x)).toLinearEquiv)
  have hq_tensor :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    -- Reuse the quotient/tensor comparison before applying the fiberwise associated-prime theorem.
    exact htransport ▸ hq_quot
  have hq_fiber :
      q ∈ relativeAssassin R RCompletion RCompletion ∩
        { q : PrimeSpectrum RCompletion | q.asIdeal.under R ∈ associatedPrimesOfModule R A } := by
    rw [← associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
      (R := R) (S := RCompletion) (M := A) (N := RCompletion)]
    exact hq_tensor
  have hq_afin : q ∈ relativeAssassinAfin R RCompletion RCompletion := by
    -- Route correction: rewrite the fiber witness to `A_fin` first, then transport the quotient.
    rw [← relativeAssassinA_eq_relativeAssassinAfin_of_flat
      (R := R) (S := RCompletion) (N := RCompletion)]
    exact hq_fiber.1
  have hq_source_branch :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion
        (relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal) := by
    simpa [mem_relativeAssassinAfin_iff, p] using hq_afin
  let e :
      relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal ≃ₗ[RCompletion]
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) :=
    Submodule.quotEquivOfEq _ _ (by
      calc
        Ideal.map (algebraMap R RCompletion) p.asIdeal • (⊤ : Submodule RCompletion RCompletion) =
            ((Ideal.map (algebraMap R RCompletion) p.asIdeal) * ⊤ : Ideal RCompletion) := by
              exact Ideal.smul_eq_mul _ _
        _ = Ideal.map (algebraMap R RCompletion) p.asIdeal := Ideal.mul_top _)
  have hbranch_transport :
      associatedPrimesOfModule RCompletion
          (relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal) =
        associatedPrimesOfModule RCompletion
          (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq (R := RCompletion)
        (M := relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal)
        (M' := RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) e)
  have hq_branch :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
    -- The relative-assassin quotient is literally the completion quotient by the extended ideal.
    exact hbranch_transport ▸ hq_source_branch
  have hq_assoc_module :
      Ideal.IsAssociatedToModule RCompletion
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) q.asIdeal := by
    simpa [mem_associatedPrimesOfModule_iff] using hq_branch
  exact
    (Ideal.isAssociatedToModule_iff_isAssociatedPrime RCompletion
      (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) q.asIdeal).mp
      hq_assoc_module

omit [IsNoetherianRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: a nilpotent element of the completion vanishes after localizing at
an associated prime once the localized ring is known to be a domain. -/
lemma localized_completion_nilpotent_eq_zero
    (q : PrimeSpectrum RCompletion)
    [IsDomain (Localization.AtPrime q.asIdeal)]
    {y : RCompletion} (hy : IsNilpotent y) :
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl RCompletion y = 0 := by
  -- Compare module localization with the actual ring localization, then kill the transported
  -- nilpotent element inside the localized domain.
  have hy_zero :
      Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal) y = 0 := by
    exact IsNilpotent.eq_zero (hy.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal)))
  have hloc :
      (IsLocalizedModule.iso q.asIdeal.primeCompl
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal) y) =
      (IsLocalizedModule.iso q.asIdeal.primeCompl
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm 0 := by
    exact congrArg
      ((IsLocalizedModule.iso q.asIdeal.primeCompl
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm) hy_zero
  calc
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl RCompletion y =
        (IsLocalizedModule.iso q.asIdeal.primeCompl
          (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm
          (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal) y) := by
            symm
            exact IsLocalizedModule.iso_symm_apply q.asIdeal.primeCompl
              (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal)) y
    _ =
        (IsLocalizedModule.iso q.asIdeal.primeCompl
          (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm 0 := hloc
    _ = 0 := by
          rw [map_zero]

/-- Helper for Lemma 10.162.12: the localized class of a nilpotent completion element vanishes at
every associated prime of `R^∧ / xR^∧`. -/
lemma localized_nilpotent_quotientClass_zero_of_associatedPrime
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    (q : PrimeSpectrum RCompletion)
    (hq : IsAssociatedPrime q.asIdeal (RCompletion ⧸ J))
    {y : RCompletion} (hy : IsNilpotent y) :
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
      (Ideal.Quotient.mk J y) = 0 :=
by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R RCompletion) q
  have hp_assoc : IsAssociatedPrime p.asIdeal A :=
    completionQuotient_associatedPrime_under (R := R) (x := x) q hq
  have hp_dvr :
      ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
    associatedPrime_quotient_localization_isDiscreteValuationRing
      (R := R) (x := x) hx0 hno_embedded hregular p hp_assoc
  have hq_branch :
      IsAssociatedPrime q.asIdeal
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) :=
    completionQuotient_associatedPrime_branch (R := R) (x := x) q hq
  obtain ⟨hq_domain, _hq_dvr⟩ :=
    completion_localizationAt_associatedPrime_isDiscreteValuationRing
      (R := R) p q hp_dvr (h_analytic p hp_assoc) hq_branch
  letI : IsDomain (Localization.AtPrime q.asIdeal) := hq_domain
  -- Route correction: rewrite the localized quotient generator through the canonical quotient
  -- comparison, then reduce to vanishing of the localized numerator in a domain.
  let e :=
    localizedQuotientEquiv q.asIdeal.primeCompl
      (J : Submodule RCompletion RCompletion)
  have hzero' :
      e.symm (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
        (Ideal.Quotient.mk J y)) = 0 := by
    rw [localizedQuotientEquiv_symm_apply_mk]
    have hmem :
        LocalizedModule.mkLinearMap q.asIdeal.primeCompl RCompletion y ∈
          Submodule.localized q.asIdeal.primeCompl (J : Submodule RCompletion RCompletion) := by
      rw [localized_completion_nilpotent_eq_zero (R := R) q hy]
      exact Submodule.zero_mem
        (Submodule.localized q.asIdeal.primeCompl
          (J : Submodule RCompletion RCompletion))
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem
  calc
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
        (Ideal.Quotient.mk J y) =
      e (e.symm (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
        (Ideal.Quotient.mk J y))) := by
          rw [LinearEquiv.apply_symm_apply]
    _ = e 0 := by rw [hzero']
    _ = 0 := e.map_zero

/-- Helper for Lemma 10.162.12: every nilpotent element of the completion already lies in the
extended ideal `x R^∧`. -/
lemma completion_nilpotent_mem_quotientIdeal
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    {y : RCompletion} (hy : IsNilpotent y) :
    y ∈ J :=
by
  letI : IsNoetherianRing RCompletion :=
    completion_isNoetherianRing (R := R)
  have hquot_zero : Ideal.Quotient.mk J y = 0 := by
    have hf_injective := 
      to_pi_localization_at_associated_primes_injective
        (R := RCompletion) (M := RCompletion ⧸ J)
    apply hf_injective
    funext q
    let qSpec : PrimeSpectrum RCompletion := ⟨q.1, q.2.1⟩
    have hq_assoc : IsAssociatedPrime qSpec.asIdeal (RCompletion ⧸ J) := by
      exact q.2
    -- Evaluate the associated-prime localization map on the quotient class and use the pointwise
    -- localized vanishing already established above.
    simpa [qSpec] using
      localized_nilpotent_quotientClass_zero_of_associatedPrime
        (R := R) (x := x) hx0 hno_embedded hregular h_analytic qSpec hq_assoc hy
  exact Ideal.Quotient.eq_zero_iff_mem.mp hquot_zero

/-- Helper for Lemma 10.162.12: a nilpotent element of the completion lies in every power of the
extended principal ideal `x R^∧`. -/
lemma completion_nilpotent_mem_all_powers_quotientIdeal
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    {y : RCompletion} (hy : IsNilpotent y) :
    ∀ n : ℕ, y ∈ J ^ n := by
  let xhat : RCompletion := algebraMap R RCompletion x
  have hJ_span : J = Ideal.span ({xhat} : Set RCompletion) := by
    -- Normalize the extended ideal of `x` to the principal ideal generated by its image.
    rw [show J = Ideal.map (algebraMap R RCompletion) (Ideal.span ({x} : Set R)) by rfl]
    rw [Ideal.map_span]
    simp [xhat]
  have hflat : Module.Flat R RCompletion := by
    -- The maximal-ideal completion is faithfully flat over the source local ring.
    exact (RingHom.flat_algebraMap_iff).mp
      (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R).flat
  have hx_regular : IsSMulRegular RCompletion x := by
    -- Since `R` is a domain and `x ≠ 0`, flatness keeps multiplication by `x` injective on
    -- the completion.
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := RCompletion) (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)
  intro n
  induction n generalizing y with
  | zero =>
      -- The zeroth power is the unit ideal.
      simp
  | succ n ih =>
      have hy_mem_J : y ∈ J :=
        completion_nilpotent_mem_quotientIdeal
          (R := R) (x := x) hx0 hno_embedded hregular h_analytic hy
      rw [hJ_span] at hy_mem_J
      obtain ⟨y1, hy_eq⟩ := Ideal.mem_span_singleton'.mp hy_mem_J
      have hy_eq' : xhat * y1 = y := by
        simpa [xhat, mul_comm] using hy_eq
      have hy1_nilpotent : IsNilpotent y1 := by
        rcases hy with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        -- Cancel the regular factor `x^m` from the nilpotence equation `(x̂ * y1)^m = 0`.
        have hsmul_zero : (x ^ m) • y1 ^ m = (x ^ m) • (0 : RCompletion) := by
          calc
            (x ^ m) • y1 ^ m = algebraMap R RCompletion (x ^ m) * y1 ^ m := by
              rfl
            _ = xhat ^ m * y1 ^ m := by
              simp [xhat, map_pow]
            _ = (xhat * y1) ^ m := by
              simp [mul_pow, mul_comm]
            _ = y ^ m := by
              simpa using congrArg (fun z : RCompletion ↦ z ^ m) hy_eq'
            _ = 0 := hm
            _ = (x ^ m) • (0 : RCompletion) := by
              simp
        exact (hx_regular.pow m) hsmul_zero
      have hy1_mem : y1 ∈ J ^ n := ih hy1_nilpotent
      have hxhat_mem : xhat ∈ J := by
        rw [hJ_span]
        exact Ideal.subset_span (by simp [xhat])
      -- Reinsert one factor of `x̂` to climb from `J^n` to `J^(n + 1)`.
      have hy_mul_mem : xhat * y1 ∈ J * J ^ n :=
        Ideal.mul_mem_mul hxhat_mem hy1_mem
      simpa [pow_succ'] using (hy_eq'.symm ▸ hy_mul_mem)

/-- Helper for Lemma 10.162.12: every nilpotent element of the completion vanishes. -/
lemma completion_nilpotent_eq_zero
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    {y : RCompletion} (hy : IsNilpotent y) :
    y = 0 :=
by
  letI : IsAdicComplete (maximalIdeal R) RCompletion :=
    AdicCompletion.isAdicComplete (I := maximalIdeal R) (M := R)
      (maximalIdeal R).fg_of_isNoetherianRing
  have hy_mem_pow :
      ∀ n : ℕ, y ∈ J ^ n :=
    completion_nilpotent_mem_all_powers_quotientIdeal
      (R := R) (x := x) hx0 hno_embedded hregular h_analytic hy
  have hJ_le_max :
      J ≤ Ideal.map (algebraMap R RCompletion) (maximalIdeal R) := by
    -- The extended principal ideal generated by `x` lies inside the extended maximal ideal.
    exact Ideal.map_mono
      ((Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx)
  have hy_mod_zero :
      ∀ n : ℕ, y ≡ 0 [SMOD (maximalIdeal R ^ n • (⊤ : Submodule R RCompletion))] := by
    intro n
    rw [SModEq.zero]
    have hy_map :
        y ∈ Ideal.map (algebraMap R RCompletion) (maximalIdeal R ^ n) := by
      exact (by
        simpa [Ideal.map_pow] using
          (Ideal.pow_right_mono hJ_le_max n) (hy_mem_pow n))
    -- Rewrite the extended ideal as the corresponding `R`-submodule of the completion.
    simpa [Ideal.smul_top_eq_map, Ideal.map_pow] using hy_map
  -- Route correction: instead of forcing a local-ring structure on the completion, use that the
  -- maximal-ideal completion is Hausdorff for the source maximal ideal and kill `y` directly.
  exact IsHausdorff.haus (I := maximalIdeal R) (M := RCompletion) inferInstance y hy_mod_zero

/-- Lemma 10.162.12: if `(R, 𝔪)` is a Noetherian local domain, `x ∈ 𝔪` is nonzero, `R / xR` has
no embedded primes, and every associated prime of `R / xR` is regular and analytically
unramified, then `R` is analytically unramified. -/
theorem isAnalyticallyUnramified_of_nonzero_in_maximalIdeal_of_associatedPrimes_quotient_regular
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p) :
    IsAnalyticallyUnramified R := by
  rw [isAnalyticallyUnramified_iff]
  -- It is enough to show that every nilpotent element of the maximal-ideal completion vanishes.
  refine ⟨fun y hy ↦ ?_⟩
  exact completion_nilpotent_eq_zero
    (R := R) (x := x) hx hx0 hno_embedded hregular h_analytic hy

end
