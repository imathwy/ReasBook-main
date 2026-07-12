import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Lemma_10_60_13
import StacksProject_2024.Chap10.Lemma_10_119_7
import StacksProject_2024.Chap15.Lemma_15_126_2
import StacksProject_2024.Chap15.Lemma_15_126_4
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped BigOperators

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalRing R]

/-
Domain-style sampling:
- primary domain: two-dimensional local commutative algebra, with height-one prime ideals and
  principal quotients;
- sampled owner declarations:
  `IsNormalRing`,
  `principalIdeal`,
  `PrimeSpectrum R`,
  `IsReduced`,
  `Ideal.height`,
  `chinese_remainder_prod_eq_iInf`,
  `exists_power_sum_ne_zero`;
- best owner abstraction: the source-facing input is a finite distinct collection of height-one
  prime ideals, so the right owner surface here is a
  `Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }` rather than an indexed family plus a
  separate injectivity witness;
  mathlib's `IsDedekindDomain.HeightOneSpectrum` is too specific for this normal local setting,
  while the quotient by the chosen element should use the chapter owner `principalIdeal` rather
  than restating `Ideal.span ({f} : Set R)`;
- primitive data vs. derived API:
  primitive data is the finite set `ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }`;
  derived API is the existence of a common nonzero element whose principal quotient is reduced.

Source/core/bridge triage:
- `source-facing`: the common-element existence statement for a finite family of pairwise distinct
  height-one primes;
- `core/canonical`: `IsNormalRing`, `principalIdeal`, `IsReduced`, and the height API on ideals;
- `bridge/view`: none beyond the canonical direct subtype
  `{ p : PrimeSpectrum R // p.asIdeal.height = 1 }`.
-/

/-- Helper for Lemma 15.126.5: a local ring is already the localization at the complement of its
maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal R).primeCompl R := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

attribute [local instance] self_isLocalization_primeCompl_maximalIdeal

/-- Helper for Lemma 15.126.5: a Noetherian local normal ring is a domain. -/
private theorem local_normal_ring_isDomain :
    IsDomain R := by
  let e : Localization.AtPrime (maximalIdeal R) ≃ₐ[R] R :=
    Localization.algEquiv (maximalIdeal R).primeCompl R
  -- Transport the domain structure from the maximal-ideal localization back to `R`.
  exact Function.Injective.isDomain e.symm e.symm.injective

attribute [local instance] local_normal_ring_isDomain

/-- Helper for Lemma 15.126.5: a nonfield local ring contains a nonzero element of its maximal
ideal. -/
private theorem exists_mem_maximalIdeal_ne_zero_of_not_isField
    (hR : ¬ IsField R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ≠ 0 := by
  have hm_ne : maximalIdeal R ≠ (⊥ : Ideal R) := by
    intro hbot
    exact hR ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot)
  have hlt : (⊥ : Ideal R) < maximalIdeal R := bot_lt_iff_ne_bot.mpr hm_ne
  rcases SetLike.exists_of_lt hlt with ⟨x, hxmem, hxnotmem⟩
  refine ⟨x, hxmem, ?_⟩
  intro hx0
  exact hxnotmem (hx0 ▸ Ideal.zero_mem _)

/-- Helper for Lemma 15.126.5: a height-one prime ideal in the present domain cannot be zero. -/
private theorem height_one_prime_ne_bot
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    p.1.asIdeal ≠ (⊥ : Ideal R) := by
  have hbot_height : (⊥ : Ideal R).height = 0 := by
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff,
      IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  intro hpbot
  simpa [hpbot, hbot_height] using p.2

/-- Helper for Lemma 15.126.5: each prescribed height-one prime contains a nonzero element. -/
private theorem exists_nonzero_mem_height_one_prime
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    ∃ x : R, x ∈ p.1.asIdeal ∧ x ≠ 0 := by
  have hp_lt : (⊥ : Ideal R) < p.1.asIdeal := by
    exact bot_lt_iff_ne_bot.mpr (height_one_prime_ne_bot (R := R) p)
  rcases SetLike.exists_of_lt hp_lt with ⟨x, hxmem, hxnotmem⟩
  refine ⟨x, hxmem, ?_⟩
  intro hx0
  exact hxnotmem (hx0 ▸ Ideal.zero_mem _)

/-- Helper for Lemma 15.126.5: there is a nonzero maximal-ideal element lying in every prescribed
height-one prime. -/
private theorem exists_nonzero_mem_all_heightOnePrimes
    (hdim : ringKrullDim R = 2)
    (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    ∃ f0 : maximalIdeal R, (f0 : R) ≠ 0 ∧
      ∀ p ∈ ps, (f0 : R) ∈ p.1.asIdeal := by
  classical
  by_cases hps : ps.Nonempty
  · let a : { p : PrimeSpectrum R // p.asIdeal.height = 1 } → R := fun p ↦
        if hp : p ∈ ps then (exists_nonzero_mem_height_one_prime (R := R) p).choose else 1
    let f : R := ∏ p ∈ ps, a p
    have hf_ne_zero : f ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro p hp
      have hp_ne_zero :
          (exists_nonzero_mem_height_one_prime (R := R) p).choose ≠ 0 :=
        (exists_nonzero_mem_height_one_prime (R := R) p).choose_spec.2
      simpa [a, hp] using hp_ne_zero
    have hf_mem : ∀ p ∈ ps, f ∈ p.1.asIdeal := by
      intro p hp
      have hp_factor :
          a p ∈ p.1.asIdeal := by
        simpa [a, hp] using
          (exists_nonzero_mem_height_one_prime (R := R) p).choose_spec.1
      have hprod :
          (∏ q ∈ ps, a q) ∈ p.1.asIdeal ↔
            ∃ q ∈ ps, a q ∈ p.1.asIdeal := by
        exact Ideal.IsPrime.prod_mem_iff
      exact hprod.mpr ⟨p, hp, hp_factor⟩
    obtain ⟨p0, hp0⟩ := hps
    have hf_max : f ∈ maximalIdeal R := by
      exact (IsLocalRing.le_maximalIdeal_of_isPrime p0.1.asIdeal) (hf_mem p0 hp0)
    let f0 : maximalIdeal R := ⟨f, hf_max⟩
    refine ⟨f0, hf_ne_zero, ?_⟩
    intro p hp
    exact hf_mem p hp
  · have hnotField : ¬ IsField R := by
      intro hfield
      rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
      norm_num at hdim
    rcases exists_mem_maximalIdeal_ne_zero_of_not_isField (R := R) hnotField with
      ⟨x, hxmem, hxne⟩
    have hx_max : x ∈ maximalIdeal R := hxmem
    refine ⟨⟨x, hx_max⟩, hxne, ?_⟩
    intro p hp
    exact False.elim (hps ⟨p, hp⟩)

/-- Helper for Lemma 15.126.5: localizing a two-dimensional Noetherian normal domain at a
height-one prime yields a discrete valuation ring. -/
private theorem localizationAtHeightOnePrime_isDiscreteValuationRing
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) := by
  let S := Localization.AtPrime p.1.asIdeal
  have hnormal_dim_one :
      ∃ (_ : IsLocalRing S) (_ : IsNoetherianRing S) (_ : IsDomain S)
        (_ : IsIntegrallyClosed S), ringKrullDim S = 1 := by
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    -- Identify the localized dimension with the height of the chosen prime.
    calc
      ringKrullDim S = ↑p.1.asIdeal.height := by
        simpa [S] using
          (IsLocalization.AtPrime.ringKrullDim_eq_height p.1.asIdeal S)
      _ = (1 : WithBot ℕ∞) := by
        simpa [p.2] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat p.2).symm
  have hdvr :
      ∃ (_ : IsDomain S), IsDiscreteValuationRing S := by
    have htfae :=
      (show List.TFAE
          [ (∃ (_ : IsDomain S), IsDiscreteValuationRing S),
            ∃ (_ : IsDomain S) (_ : IsNoetherianRing S), ValuationRing S ∧ ¬ IsField S,
            IsRegularLocalRing S ∧ ringKrullDim S = 1,
            ∃ (_ : IsLocalRing S) (_ : IsNoetherianRing S) (_ : IsDomain S),
              maximalIdeal S ≠ ⊥ ∧ (maximalIdeal S).IsPrincipal,
            ∃ (_ : IsLocalRing S) (_ : IsNoetherianRing S) (_ : IsDomain S)
              (_ : IsIntegrallyClosed S), ringKrullDim S = 1 ] from
        discreteValuationRing_tfae (A := S))
    -- Clause `(5) → (1)` is the localized DVR criterion from Lemma `10.119.7`.
    exact (htfae.out 4 0).mp hnormal_dim_one
  exact hdvr.choose_spec

/-- Helper for Lemma 15.126.5: in a one-dimensional local ring, a principal ideal of definition
cannot be generated by an element inside a minimal prime. -/
private theorem not_mem_minimalPrimes_of_principalIdeal_isIdealOfDefinition_dim_one
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (hdim : ringKrullDim S = 1) {x : maximalIdeal S}
    (hxdef : (principalIdeal (x : S)).IsIdealOfDefinition) :
    ∀ q ∈ minimalPrimes S, (x : S) ∉ q := by
  intro q hq hxq
  letI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  have hspan_le_q : principalIdeal (x : S) ≤ q := by
    rw [principalIdeal, Ideal.span_singleton_le_iff_mem]
    exact hxq
  have hmax_le_q : maximalIdeal S ≤ q := by
    -- The radical of a defining principal ideal is the maximal ideal, so any prime containing the
    -- generator must contain the closed point.
    have hrad : (principalIdeal (x : S)).radical = maximalIdeal S := by
      simpa [Ideal.IsIdealOfDefinition] using hxdef
    have hrad_le_q : (principalIdeal (x : S)).radical ≤ q := by
      simpa [show q.radical = q by simpa using (show q.IsPrime from inferInstance).radical] using
        Ideal.radical_mono hspan_le_q
    simpa [hrad] using hrad_le_q
  have hq_eq_max : q = maximalIdeal S := by
    -- In a local ring every prime sits below the maximal ideal, so containment both ways gives
    -- equality.
    exact le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime q) hmax_le_q
  have hq_primeHeight_zero : q.primeHeight = 0 :=
    (Ideal.primeHeight_eq_zero_iff (I := q)).mpr hq
  have hmax_primeHeight_one : (maximalIdeal S).primeHeight = 1 := by
    -- Rewrite the height of the closed point using the ambient one-dimensionality.
    have hmax_primeHeight_one' : ((maximalIdeal S).primeHeight : WithBot ℕ∞) = 1 := by
      simpa [IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim] using hdim
    exact_mod_cast hmax_primeHeight_one'
  have hzero_ne_one : (0 : ℕ∞) ≠ 1 := by
    simp
  exact hzero_ne_one <| by
    have hq_primeHeight_one : q.primeHeight = 1 := by
      simpa [hq_eq_max] using hmax_primeHeight_one
    exact hq_primeHeight_zero.symm.trans hq_primeHeight_one

/-- Helper for Lemma 15.126.5: an admissible perturbation is a high-order maximal-ideal element
lying in every prescribed height-one prime. -/
private def admissible_perturbation
    (n : ℕ) (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (h : maximalIdeal R) : Prop :=
  ((h : R) ∈ maximalIdeal R ^ (n + 1)) ∧
    ∀ p ∈ ps, (h : R) ∈ p.1.asIdeal

/-- Helper for Lemma 15.126.5: the branch count of a perturbation is the number of minimal primes
of the corresponding principal quotient. -/
private noncomputable def perturbation_branch_count
    (f0 : maximalIdeal R) (h : maximalIdeal R) : ℕ :=
  (minimalPrimes (R ⧸ principalIdeal (((f0 + h : maximalIdeal R) : R)))).encard.toNat

/-- Helper for Lemma 15.126.5: the zero perturbation is always admissible. -/
private theorem zero_is_admissible_perturbation
    (n : ℕ) (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    admissible_perturbation (R := R) n ps 0 := by
  constructor
  · simpa using (show (0 : R) ∈ maximalIdeal R ^ (n + 1) from Ideal.zero_mem _)
  · intro p hp
    exact Ideal.zero_mem _

/-- Helper for Lemma 15.126.5: adding an admissible perturbation preserves membership in the
prescribed height-one primes. -/
private theorem add_admissible_perturbation_mem_heightOnePrimes
    {n : ℕ} {ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }}
    {f0 h : maximalIdeal R}
    (hf0 : ∀ p ∈ ps, (f0 : R) ∈ p.1.asIdeal)
    (hh : admissible_perturbation (R := R) n ps h) :
    ∀ p ∈ ps, (((f0 + h : maximalIdeal R) : R)) ∈ p.1.asIdeal := by
  intro p hp
  exact p.1.asIdeal.add_mem (hf0 p hp) (hh.2 p hp)

/-- Helper for Lemma 15.126.5: a uniformly bounded branch-count function attains its maximum on
the admissible perturbations. -/
private theorem exists_maximizing_admissible_perturbation
    (n : ℕ) (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (score : maximalIdeal R → ℕ) (B : ℕ)
    (hbound : ∀ h : maximalIdeal R,
      admissible_perturbation (R := R) n ps h → score h ≤ B) :
    ∃ hmax : maximalIdeal R, admissible_perturbation (R := R) n ps hmax ∧
      ∀ h : maximalIdeal R, admissible_perturbation (R := R) n ps h →
        score h ≤ score hmax := by
  classical
  let good : ℕ → Prop := fun m ↦
    ∃ h : maximalIdeal R, admissible_perturbation (R := R) n ps h ∧ score h = m
  have hzero_adm : admissible_perturbation (R := R) n ps 0 :=
    zero_is_admissible_perturbation (R := R) n ps
  have hscore0_le : score (0 : maximalIdeal R) ≤ B := hbound 0 hzero_adm
  have hgood0 : good (score (0 : maximalIdeal R)) := by
    exact ⟨0, hzero_adm, rfl⟩
  let mmax := Nat.findGreatest good B
  have hmmax_good : good mmax := by
    exact Nat.findGreatest_spec hscore0_le hgood0
  rcases hmmax_good with ⟨hmax, hhmax_adm, hhmax_score⟩
  refine ⟨hmax, hhmax_adm, ?_⟩
  intro h hh
  have hscore_le : score h ≤ B := hbound h hh
  have hgood_h : good (score h) := by
    exact ⟨h, hh, rfl⟩
  calc
    score h ≤ mmax := Nat.le_findGreatest hscore_le hgood_h
    _ = score hmax := hhmax_score.symm

/-- Helper for Lemma 15.126.5: every admissible perturbation has branch count bounded by the
fixed two-parameter quotient length. -/
private theorem perturbation_branch_count_le_fixed_parameter_length
    {f0 g : maximalIdeal R} {n : ℕ}
    (hsop : IsSystemOfParameters (Fin.cons f0 ![g]))
    (hstable : ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (n + 1)) →
      IsSystemOfParameters (Fin.cons (f0 + h) ![g]) ∧
        Module.length R (R ⧸ parameterIdeal (Fin.cons f0 ![g])) =
          Module.length R (R ⧸ parameterIdeal (Fin.cons (f0 + h) ![g])))
    (h : maximalIdeal R)
    (hhpow : (h : R) ∈ maximalIdeal R ^ (n + 1)) :
    perturbation_branch_count (R := R) f0 h ≤
      (Module.length R (R ⧸ parameterIdeal (Fin.cons f0 ![g]))).toNat := by
  let f : R := ((f0 + h : maximalIdeal R) : R)
  let I : Ideal R := principalIdeal f
  let A : Type u := R ⧸ I
  let π : R →+* A := Ideal.Quotient.mk I
  have hpert := hstable h hhpow
  have hsop' : IsSystemOfParameters (Fin.cons (f0 + h) ![g]) := hpert.1
  have hlen' :
      Module.length R (R ⧸ parameterIdeal (Fin.cons f0 ![g])) =
        Module.length R (R ⧸ parameterIdeal (Fin.cons (f0 + h) ![g])) := hpert.2
  by_cases hf : f = 0
  · -- Route correction: the source proof works on the one-dimensional quotient by `f`.
    -- The only exceptional case is `f = 0`, where the quotient is `R` itself and one must bound
    -- the single domain branch directly from the positivity of the perturbed quotient length.
    -- TODO: identify `parameterIdeal (Fin.cons (f0 + h) ![g])` with `(g)` under `hf`, show its
    -- quotient has positive length because it is a proper ideal of definition, and transport that
    -- positivity back along `hlen'`.
    sorry
  · have hf_not_mem_minimalPrimes :
      ∀ p ∈ minimalPrimes R, f ∉ p := by
      intro p hp hfp
      have hp_eq_bot : p = (⊥ : Ideal R) := by
        simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hp
      exact hf (by simpa [f, hp_eq_bot] using hfp)
    have hA_dim : ringKrullDim A = 1 := by
      -- Quotienting by `f` drops the dimension by exactly one because `f` avoids all minimal
      -- primes of the domain.
      have hquot :
          ringKrullDim R = ringKrullDim A + 1 := by
        simpa [A, I, f, principalIdeal] using
          ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
            (R := R) f (show f ∈ maximalIdeal R by
              change (((f0 + h : maximalIdeal R) : R)) ∈ maximalIdeal R
              exact (f0 + h).property) hf_not_mem_minimalPrimes
      have hdim_two : ringKrullDim R = 1 + 1 := by
        simpa using hsop'.1
      simpa [Nat.succ_eq_add_one] using hquot.symm.trans hdim_two
    have hI_ne_top : I ≠ ⊤ := by
      intro hI_top
      have hunit : IsUnit f := by
        exact (Ideal.span_singleton_eq_top).mp (by simpa [I, principalIdeal] using hI_top)
      exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) (show f ∈ maximalIdeal R by
        change (((f0 + h : maximalIdeal R) : R)) ∈ maximalIdeal R
        exact (f0 + h).property)
    letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 hI_ne_top
    letI : IsLocalRing A := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
    letI : Ring.KrullDimLE 1 A := (Ring.krullDimLE_iff (R := A)).2 (by simpa [hA_dim])
    let gbar : maximalIdeal A := by
      refine ⟨π (g : R), ?_⟩
      rw [← IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem π g.property
    -- TODO: show that the principal ideal `(gbar)` is an ideal of definition in `A` by
    -- identifying `A ⧸ (gbar)` with the two-step quotient by `f` and `g`. Then
    -- `not_mem_minimalPrimes_of_principalIdeal_isIdealOfDefinition_dim_one` supplies the
    -- minimal-prime avoidance needed for `encard_minimalPrimes_le_ord`, and the remaining work is
    -- the quotient-of-quotient length transport back to `parameterIdeal (Fin.cons (f0 + h) ![g])`.
    let _ := hA_dim
    let _ := gbar
    let _ := hlen'
    sorry

/-- Helper for Lemma 15.126.5: after reaching a maximizing admissible perturbation, one further
admissible correction can make the principal quotient reduced. -/
private theorem exists_reduced_perturbation_of_maximizer
    {f0 g hmax : maximalIdeal R} {n : ℕ}
    (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (hf0_ne_zero : (f0 : R) ≠ 0)
    (hf0_mem : ∀ p ∈ ps, (f0 : R) ∈ p.1.asIdeal)
    (hsop : IsSystemOfParameters (Fin.cons f0 ![g]))
    (hstable : ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (n + 1)) →
      IsSystemOfParameters (Fin.cons (f0 + h) ![g]) ∧
        Module.length R (R ⧸ parameterIdeal (Fin.cons f0 ![g])) =
          Module.length R (R ⧸ parameterIdeal (Fin.cons (f0 + h) ![g])))
    (hhmax : admissible_perturbation (R := R) n ps hmax)
    (hmaximal : ∀ h : maximalIdeal R, admissible_perturbation (R := R) n ps h →
      perturbation_branch_count (R := R) f0 h ≤
        perturbation_branch_count (R := R) f0 hmax) :
    ∃ hgood : maximalIdeal R, admissible_perturbation (R := R) n ps hgood ∧
      (((f0 + hgood : maximalIdeal R) : R) ≠ 0) ∧
        IsReduced (R ⧸ principalIdeal (((f0 + hgood : maximalIdeal R) : R))) := by
  -- Route correction: the source proof does not make the maximizer itself reduced.
  -- It constructs one additional admissible correction and then uses maximality to rule out new
  -- branches after the old ones are made simple in each DVR localization.
  let _ := hf0_ne_zero
  let _ := hf0_mem
  let _ := hsop
  let _ := hstable
  let _ := hhmax
  let _ := hmaximal
  sorry

-- Proof sketch: start with any nonzero element in the finite intersection of the given height-one
-- primes and apply the stable-perturbation lemma from the previous item to vary it by a deep
-- maximal-ideal element. Interpreting the resulting principal divisor through the discrete
-- valuation rings at the height-one primes, choose the perturbation so that the number of minimal
-- primes of the quotient is maximal; then all valuation multiplicities become `1`, which is
-- equivalent to the quotient by the principal ideal being reduced.
/-- Lemma 15.126.5: in a two-dimensional Noetherian local normal ring, any finite family of
pairwise distinct height-one prime ideals has a common nonzero element whose principal quotient is
reduced. -/
theorem exists_mem_heightOnePrimes_with_reduced_principal_quotient
    (hdim : ringKrullDim R = 2)
    (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    ∃ f : R, f ≠ 0 ∧ (∀ p ∈ ps, f ∈ p.1.asIdeal) ∧ IsReduced (R ⧸ principalIdeal f) := by
  rcases exists_nonzero_mem_all_heightOnePrimes (R := R) hdim ps with
    ⟨f0, hf0_ne_zero, hf0_mem⟩
  have hf0_not_mem_minimalPrimes :
      ∀ p ∈ minimalPrimes R, ((f0 : maximalIdeal R) : R) ∉ p := by
    intro p hp hmem
    have hp_eq_bot : p = (⊥ : Ideal R) := by
      simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hp
    exact hf0_ne_zero (by simpa [hp_eq_bot] using hmem)
  rcases
    exists_systemOfParameters_cons_singleton_stable_under_highOrder_perturbation_of_not_mem_minimalPrimes
      (R := R) hdim f0 hf0_not_mem_minimalPrimes with
    ⟨g, n, hsop, hstable⟩
  have hbound :
      ∀ h : maximalIdeal R, admissible_perturbation (R := R) n ps h →
        perturbation_branch_count (R := R) f0 h ≤
          (Module.length R (R ⧸ parameterIdeal (Fin.cons f0 ![g]))).toNat := by
    intro h hh
    -- The branch-count maximization needs a uniform finite bound on the admissible family.
    exact perturbation_branch_count_le_fixed_parameter_length (R := R) hsop hstable h hh.1
  rcases
    exists_maximizing_admissible_perturbation (R := R) n ps
      (perturbation_branch_count (R := R) f0)
      (Module.length R (R ⧸ parameterIdeal (Fin.cons f0 ![g]))).toNat hbound with
    ⟨hmax, hhmax, hmaximal⟩
  obtain ⟨hgood, hhgood, hgood_nonzero, hgood_reduced⟩ :=
    exists_reduced_perturbation_of_maximizer (R := R) ps hf0_ne_zero hf0_mem hsop hstable
      hhmax hmaximal
  refine ⟨((f0 + hgood : maximalIdeal R) : R), hgood_nonzero, ?_, hgood_reduced⟩
  -- The final corrected perturbation is still admissible, so it remains in every chosen branch.
  exact add_admissible_perturbation_mem_heightOnePrimes (R := R) hf0_mem hhgood

end
