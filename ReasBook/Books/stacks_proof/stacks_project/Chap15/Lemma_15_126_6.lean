import Mathlib
import StacksProject_2024.Chap15.Lemma_15_126_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalRing A]

/- Domain-style sampling for Lemma 15.126.6:
- primary domain: two-dimensional local commutative algebra, with height-one primes, principal
  divisors, and reduced principal quotients;
- sampled owner declarations:
  `exists_mem_heightOnePrimes_with_reduced_principal_quotient`,
  `IsNormalRing`,
  `IsLocalRing.notMem_maximalIdeal`,
  `principalIdeal`,
  `IsReduced`,
  `Ideal.height`;
- best owner abstraction: the source-facing input remains the single nonzero element
  `a ≠ 0`, while the canonical chapter owner driving the construction is the finite-family
  height-one-prime theorem `exists_mem_heightOnePrimes_with_reduced_principal_quotient`; the
  local-ring owner `IsLocalRing.notMem_maximalIdeal` shows that the extra source-side hypothesis
  `a ∈ maximalIdeal A` is redundant for the resulting divisibility conclusion;
- primitive data vs. derived API:
  primitive data is the element `a` together with `a ≠ 0`;
  derived API is the resulting nonzero element `c` with reduced principal quotient and a power of
  `c` divisible by `a`.

Source/core/bridge triage:
- `source-facing`: the divisibility statement for one nonzero element, with the source
  maximal-ideal formulation recovered as the nonunit case;
- `core/canonical`: `IsNormalRing`, `exists_mem_heightOnePrimes_with_reduced_principal_quotient`,
  `principalIdeal`, `IsReduced`, and the height-one-prime API on ideals;
- `bridge/view`: passing from the finite family of height-one primes appearing in the divisor of
  `a` to the single-element divisibility consequence. -/

-- Proof sketch: if `a ∉ maximalIdeal A`, then `a` is a unit by
-- `IsLocalRing.notMem_maximalIdeal`, so the conclusion is trivial with `c = 1` and `n = 0`.
-- Otherwise `a` lies in the maximal ideal, and Lemma `15.126.5` applied to the finite family of
-- height-one primes occurring in the divisor of `a` yields a common nonzero element `c` with
-- `A ⧸ (c)` reduced. For any exponent `n` at least as large as all coefficients in `div(a)`, the
-- divisor `-div(a) + div(c ^ n)` is effective, and Lemma `10.157.6` then identifies this
-- effectivity with the divisibility relation `a ∣ c ^ n`.

/-- Helper for Lemma 15.126.6: a local ring identifies with the localization at the complement of
its maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

attribute [local instance] self_isLocalization_primeCompl_maximalIdeal

/-- Helper for Lemma 15.126.6: a Noetherian local normal ring is a domain. -/
private theorem local_normal_ring_isDomain :
    IsDomain A := by
  let e : Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
    Localization.algEquiv (maximalIdeal A).primeCompl A
  -- Transport the domain structure from the maximal-ideal localization back to `A`.
  exact Function.Injective.isDomain e.symm e.symm.injective

attribute [local instance] local_normal_ring_isDomain

/-- Helper for Lemma 15.126.6: a minimal prime over `(a)` is an associated prime of `A / (a)`. -/
private theorem minimal_prime_principalIdeal_is_associated
    (a : A) {p : Ideal A} (hp : p ∈ (principalIdeal a).minimalPrimes) :
    p ∈ associatedPrimes A (A ⧸ principalIdeal a) := by
  -- Rewrite the annihilator of the principal quotient so that the standard minimal-prime bridge
  -- applies directly.
  have hp_ann : p ∈ (Module.annihilator A (A ⧸ principalIdeal a)).minimalPrimes := by
    simpa [Ideal.annihilator_quotient] using hp
  exact
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      A (A ⧸ principalIdeal a) hp_ann

/-- Helper for Lemma 15.126.6: every minimal prime over `(a)` has height exactly `1` when `a` is
nonzero. -/
private theorem minimal_prime_principalIdeal_height_eq_one
    (a : A) (ha0 : a ≠ 0) {p : Ideal A} (hp : p ∈ (principalIdeal a).minimalPrimes) :
    p.height = 1 := by
  letI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
  -- Krull's principal ideal theorem gives the upper bound `height p ≤ 1`.
  have hp_le_one : p.height ≤ 1 := by
    simpa using Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (principalIdeal a) p hp
  -- The prime cannot be minimal in the whole domain, because it contains the nonzero element `a`.
  have hp_not_minimal : p ∉ minimalPrimes A := by
    intro hpmin
    have hp_eq_bot : p = (⊥ : Ideal A) := by
      simpa [IsDomain.minimalPrimes_eq_singleton_bot A] using hpmin
    have ha_mem_p : a ∈ p := by
      exact hp.1.2 (by simpa [principalIdeal] using Ideal.mem_span_singleton_self a)
    exact ha0 (by simpa [hp_eq_bot] using ha_mem_p)
  -- Since `height p` is a finite extended natural number at most `1`, the only remaining
  -- possibility is `1`.
  rcases (ENat.le_coe_iff).1 hp_le_one with ⟨n, hn, hn_le⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have hp_height_zero : p.height = 0 := by
      simpa [hn_zero] using hn
    have hp_primeHeight_zero : p.primeHeight = 0 := by
      simpa [Ideal.height_eq_primeHeight p] using hp_height_zero
    exact hp_not_minimal ((Ideal.primeHeight_eq_zero_iff).1 hp_primeHeight_zero)
  have hn_eq_one : n = 1 := by
    omega
  simpa [hn_eq_one] using hn

/-- Helper for Lemma 15.126.6: the minimal primes over `(a)` form a finite family of height-one
prime-spectrum points. -/
private theorem principalIdeal_minimalPrimes_height_one_finset
    (a : A) (ha0 : a ≠ 0) :
    ∃ ps : Finset { q : PrimeSpectrum A // q.asIdeal.height = 1 },
      ∀ p ∈ (principalIdeal a).minimalPrimes, ∃ q ∈ ps, q.1.asIdeal = p := by
  classical
  -- The quotient `A / (a)` has finitely many associated primes, hence only finitely many minimal
  -- primes over `(a)`.
  have hassoc_finite : (associatedPrimes A (A ⧸ principalIdeal a)).Finite :=
    associatedPrimes.finite A (A ⧸ principalIdeal a)
  have hmin_finite : ((principalIdeal a).minimalPrimes).Finite := by
    refine hassoc_finite.subset ?_
    intro p hp
    exact minimal_prime_principalIdeal_is_associated (a := a) hp
  let s : Finset (Ideal A) := hmin_finite.toFinset
  let f :
      { p : Ideal A // p ∈ s } → { q : PrimeSpectrum A // q.asIdeal.height = 1 } :=
    fun p ↦
      let hp : p.1 ∈ (principalIdeal a).minimalPrimes := by
        exact (Set.Finite.mem_toFinset hmin_finite).1 p.2
      ⟨⟨p.1, Ideal.minimalPrimes_isPrime hp⟩,
        minimal_prime_principalIdeal_height_eq_one (a := a) ha0 hp⟩
  let ps : Finset { q : PrimeSpectrum A // q.asIdeal.height = 1 } := s.attach.image f
  refine ⟨ps, ?_⟩
  intro p hp
  have hp_mem_s : p ∈ s := (Set.Finite.mem_toFinset hmin_finite).2 hp
  let p' : { p : Ideal A // p ∈ s } := ⟨p, hp_mem_s⟩
  -- Repackage each minimal prime ideal as the corresponding height-one point of `Spec A`.
  refine ⟨f p', ?_, rfl⟩
  exact Finset.mem_image.mpr ⟨p', by simp, rfl⟩

/-- Helper for Lemma 15.126.6: membership in every minimal prime over `I` implies membership in
`√I`. -/
private theorem mem_radical_of_mem_minimalPrimes
    (I : Ideal A) {x : A} (hx : ∀ p ∈ I.minimalPrimes, x ∈ p) :
    x ∈ I.radical := by
  -- It suffices to test membership in every prime ideal containing `I`; each such prime contains
  -- a minimal prime over `I`.
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  intro J hJ
  letI : J.IsPrime := hJ.2
  obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le hJ.1
  exact hpJ (hx p hp)

/-- Lemma 15.126.6: in a two-dimensional Noetherian normal local domain, every nonzero element
divides a power of some nonzero element `c` such that the principal quotient
`A ⧸ principalIdeal c` is reduced. -/
@[stacks 0AXI]
theorem exists_nonzero_reduced_principal_quotient_dvd_pow
    (hdim : ringKrullDim A = 2) (a : A) (ha0 : a ≠ 0) :
    ∃ c : A, c ≠ 0 ∧ IsReduced (A ⧸ principalIdeal c) ∧ ∃ n : ℕ, a ∣ c ^ n := by
  classical
  -- Route correction: rather than importing the unavailable associated-prime owner file, we keep
  -- the source-faithful route through the minimal primes of `(a)` and upgrade them to height one
  -- using the principal ideal theorem inside the present domain.
  rcases principalIdeal_minimalPrimes_height_one_finset (A := A) a ha0 with ⟨ps, hcover⟩
  rcases exists_mem_heightOnePrimes_with_reduced_principal_quotient (R := A) hdim ps with
    ⟨c, hc0, hc_mem, hc_red⟩
  have hc_min : ∀ p ∈ (principalIdeal a).minimalPrimes, c ∈ p := by
    intro p hp
    obtain ⟨q, hq_mem, hq_eq⟩ := hcover p hp
    simpa [hq_eq] using hc_mem q hq_mem
  have hc_rad : c ∈ (principalIdeal a).radical :=
    mem_radical_of_mem_minimalPrimes (I := principalIdeal a) hc_min
  rcases (Ideal.mem_radical_iff).1 hc_rad with ⟨n, hpow⟩
  refine ⟨c, hc0, hc_red, n, ?_⟩
  -- Membership in the principal ideal `(a)` is exactly divisibility by `a`.
  simpa [principalIdeal] using (Ideal.mem_span_singleton.mp hpow)

end
