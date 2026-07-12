import Mathlib
import StacksProject_2024.Chap10.Lemma_10_106_2
import StacksProject_2024.Chap10.Lemma_10_120_6
import StacksProject_2024.Chap10.Lemma_10_120_7_Nagata_s_criterion_for_factoriality
import StacksProject_2024.Chap15.Lemma_15_10_5
import StacksProject_2024.Chap15.Lemma_15_48_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open IsLocalRing

/- Domain-style sampling for Lemma 15.122.2:
- primary domain: commutative algebra of regular local rings, height-one prime ideals, and the
  canonical factoriality owner `UniqueFactorizationMonoid`;
- sampled owner declarations:
  `regularLocalRing_isDomain`,
  `uniqueFactorizationMonoid_iff_forall_height_one_prime_isPrincipal`,
  `UniqueFactorizationMonoid`,
  `IsRegularLocalRing`;
- best owner abstraction: the public owner is `UniqueFactorizationMonoid R`; the height-one-prime
  principal criterion is derived bridge API imported from Chapter 10 rather than primitive local
  data for this file;
- primitive vs. derived:
  the primitive data are only the ambient regular-local hypotheses on `R`;
  the height-one-principal criterion used in the proof is derived from the Chapter 10 owner bridge.

Source/core/bridge triage:
- `source-facing`: the instance below expressing that a regular local ring is factorial;
- `core/canonical`: `UniqueFactorizationMonoid R`;
- `bridge/view`: `uniqueFactorizationMonoid_iff_forall_height_one_prime_isPrincipal`. -/

-- Proof sketch: by Lemma `10.120.6`, it is enough to prove that every height-one prime ideal of a
-- regular local ring is principal. Proceed by induction on the dimension. Choose
-- `x ∈ maximalIdeal R \ maximalIdeal R ^ 2`; then `R ⧸ (x)` is again regular, hence a domain, so
-- `x` is a prime element. For a height-one prime `p`, either `x ∈ p`, in which case `p = (x)`, or
-- after localizing away from `x`, the localizations at nonmaximal primes are regular local rings
-- of smaller dimension, so the induction hypothesis shows `p` becomes invertible and hence
-- principal on `Rₓ`. A generator coming from a factor of an element of `p` is then prime in `R`
-- by Nagata's criterion, and its principal ideal equals `p`.
/-- Helper for Lemma 15.122.2: positive Krull dimension lets us choose a parameter outside `𝔪²`
whose principal ideal is prime. This is the source-level parameter used in the inductive step. -/
theorem exists_prime_parameter_of_positive_dim (hdim_pos : 0 < ringKrullDim R) :
    ∃ x : R,
      x ∈ maximalIdeal R ∧
        x ∉ maximalIdeal R ^ 2 ∧
        (Ideal.span ({x} : Set R)).IsPrime := by
  -- Convert regularity into the cotangent-space dimension formula for the maximal ideal.
  have hregdim : ringKrullDim R = (maximalIdeal R).spanFinrank := by
    simpa using ((isRegularLocalRing_iff R).1 inferInstance).symm
  have hspan_pos : 0 < (maximalIdeal R).spanFinrank := by
    -- A zero-dimensional cotangent space would force `ringKrullDim R = 0`, contradicting the
    -- positive-dimension hypothesis.
    by_contra hspan_zero
    have hdim0 : ringKrullDim R = 0 := by
      simpa [Nat.eq_zero_of_not_pos hspan_zero] using hregdim
    exact (lt_irrefl (0 : WithBot ℕ∞)) (hdim0 ▸ hdim_pos)
  -- Choose a regular system of parameters of full length and take its first parameter.
  obtain ⟨z, hz⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters
      (R := R) (d := (maximalIdeal R).spanFinrank) hregdim).1 inferInstance
  let i0 : Fin ((maximalIdeal R).spanFinrank) := ⟨0, hspan_pos⟩
  have hcot_ne_zero : (maximalIdeal R).toCotangent (z i0) ≠ 0 := by
    simpa [regularSystemOfParameters_cotangentBasis_apply] using
      (regularSystemOfParameters_cotangentBasis hz).ne_zero i0
  refine ⟨z i0, (z i0).2, ?_, ?_⟩
  · -- A nonzero cotangent class is exactly the statement that the chosen parameter avoids `𝔪²`.
    intro hx_sq
    exact hcot_ne_zero ((Ideal.toCotangent_eq_zero (maximalIdeal R) (z i0)).2 hx_sq)
  · -- Quotienting by a single parameter stays regular local, hence the principal ideal is prime.
    have hpart :
        IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank
          (fun _ : Fin 1 ↦ z i0) :=
      isPartOfRegularSystemOfParameters_singleton_of_not_mem_maximalIdeal_sq
        (A := R) (z i0) (by
          intro hx_sq
          exact hcot_ne_zero ((Ideal.toCotangent_eq_zero (maximalIdeal R) (z i0)).2 hx_sq))
    have hquot_param :
        IsRegularLocalRing (R ⧸ parameterIdeal (fun _ : Fin 1 ↦ z i0)) :=
      IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal hpart
    let eParam :
        (R ⧸ parameterIdeal (fun _ : Fin 1 ↦ z i0)) ≃ₐ[R]
          (R ⧸ principalIdeal (z i0 : R)) :=
      Ideal.quotientEquivAlgOfEq R (parameterIdeal_fin1_eq_principalIdeal (A := R) (z i0))
    have hquot_principal : IsRegularLocalRing (R ⧸ principalIdeal (z i0 : R)) :=
      IsRegularLocalRing.of_ringEquiv eParam.toRingEquiv
    have hquot_domain : IsDomain (R ⧸ principalIdeal (z i0 : R)) := by
      let _ : IsRegularLocalRing (R ⧸ principalIdeal (z i0 : R)) := hquot_principal
      infer_instance
    -- Kernels of quotient maps to domains are prime; here the kernel is the principal ideal.
    change (principalIdeal (z i0 : R)).IsPrime
    refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
    · intro htop
      have hle : principalIdeal (z i0 : R) ≤ maximalIdeal R := by
        rw [principalIdeal, Ideal.span_le]
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact (z i0).2
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (htop ▸ hle))
    · intro a b hab
      have hmul_zero : Ideal.Quotient.mk (principalIdeal (z i0 : R)) (a * b) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 hab
      have hmul_zero' :
          Ideal.Quotient.mk (principalIdeal (z i0 : R)) a *
            Ideal.Quotient.mk (principalIdeal (z i0 : R)) b = 0 := by
        simpa using hmul_zero
      have hzero :
          Ideal.Quotient.mk (principalIdeal (z i0 : R)) a = 0 ∨
            Ideal.Quotient.mk (principalIdeal (z i0 : R)) b = 0 :=
        eq_zero_or_eq_zero_of_mul_eq_zero hmul_zero'
      rcases hzero with ha0 | hb0
      · left
        exact Ideal.Quotient.eq_zero_iff_mem.1 ha0
      · right
        exact Ideal.Quotient.eq_zero_iff_mem.1 hb0

/-- Helper for Lemma 15.122.2: a height-one prime forces positive dimension, so one can choose a
parameter `x ∈ maximalIdeal R \ maximalIdeal R ^ 2` whose principal ideal is prime. -/
lemma exists_prime_parameter_of_height_one_prime (p : Ideal R) (hp : p.IsPrime)
    (hheight : p.height = 1) :
    ∃ x : R,
      x ∈ maximalIdeal R ∧
        x ∉ maximalIdeal R ^ 2 ∧
        (Ideal.span ({x} : Set R)).IsPrime := by
  -- A height-one prime forces positive dimension, so the shared source-faithful parameter chooser
  -- applies directly.
  have hp_height_le : p.height ≤ ringKrullDim R :=
    Ideal.height_le_ringKrullDim_of_ne_top hp.ne_top
  have hdim_pos : 0 < ringKrullDim R := by
    have hone_le : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
      simpa [hheight] using hp_height_le
    exact lt_of_lt_of_le (by simp) hone_le
  exact exists_prime_parameter_of_positive_dim (R := R) hdim_pos

/-- Helper for Lemma 15.122.2: a nonzero prime parameter lying in a height-one prime ideal already
generates that height-one prime ideal. -/
lemma height_one_prime_eq_span_of_mem_prime_parameter (x : R) (hx_ne_zero : x ≠ 0)
    (hxprime : (Ideal.span ({x} : Set R)).IsPrime) (p : Ideal R) (hp : p.IsPrime)
    (hheight : p.height = 1) (hxmem : x ∈ p) :
    p = Ideal.span ({x} : Set R) := by
  -- Route correction: this is exactly the easy branch from Lemma `10.120.6`.
  have hbot_height : (⊥ : Ideal R).height = 0 := by
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff,
      IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hbot_primeHeight : (⊥ : Ideal R).primeHeight = 0 := by
    simpa [Ideal.height_eq_primeHeight] using hbot_height
  have hxp : Ideal.span ({x} : Set R) ≤ p :=
    (Ideal.span_singleton_le_iff_mem p).2 hxmem
  letI : (Ideal.span ({x} : Set R)).IsPrime := hxprime
  have hxspan_mem : Ideal.span ({x} : Set R) ∈ (Ideal.span ({x} : Set R)).minimalPrimes := by
    simp [Ideal.minimalPrimes_eq_subsingleton_self]
  have hxspan_height_le : (Ideal.span ({x} : Set R)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span ({x} : Set R)) (Ideal.span ({x} : Set R)) hxspan_mem
  have hbot_lt : (⊥ : Ideal R) < Ideal.span ({x} : Set R) := by
    refine bot_lt_iff_ne_bot.2 ?_
    simpa [Ideal.span_singleton_eq_bot] using hx_ne_zero
  have hxspan_height_ge : 1 ≤ (Ideal.span ({x} : Set R)).height := by
    have := Ideal.primeHeight_add_one_le_of_lt hbot_lt
    simpa [hbot_primeHeight, Ideal.height_eq_primeHeight] using this
  have hxspan_height : (Ideal.span ({x} : Set R)).height = 1 :=
    le_antisymm hxspan_height_le hxspan_height_ge
  haveI : p.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]
    right
    rw [hheight]
    simp
  have hp_min : p ∈ (Ideal.span ({x} : Set R)).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_eq hxp (by simp [hheight, hxspan_height])
  simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hp_min

/-- Helper for Lemma 15.122.2: a prime element contained in a height-one prime ideal already
generates that height-one prime ideal. -/
lemma height_one_prime_eq_span_of_mem_prime_element (y : R) (hyprime : Prime y)
    (p : Ideal R) (hp : p.IsPrime) (hheight : p.height = 1) (hymem : y ∈ p) :
    p = Ideal.span ({y} : Set R) := by
  -- Convert the prime element into a prime principal ideal and reuse the height-one closing lemma.
  have hyspan_prime : (Ideal.span ({y} : Set R)).IsPrime :=
    (Ideal.span_singleton_prime hyprime.ne_zero).2 hyprime
  exact
    height_one_prime_eq_span_of_mem_prime_parameter y hyprime.ne_zero hyspan_prime p hp hheight
      hymem

/-- Helper for Lemma 15.122.2: localizing a prime ideal away from an element that it avoids keeps
the extended ideal prime. -/
lemma away_map_isPrime_of_not_mem (p : Ideal R) (hp : p.IsPrime) {x : R} (hxnotmem : x ∉ p) :
    (Ideal.map (algebraMap R (Localization.Away x)) p).IsPrime := by
  -- First show that no power of `x` lies in `p`, so `p` is disjoint from the localization powers.
  have hpow_not_mem : ∀ n : ℕ, x ^ n ∉ p := by
    intro n
    induction n with
    | zero =>
        intro h1
        exact hp.ne_top <|
          p.eq_top_of_isUnit_mem h1 (by simpa using (isUnit_one : IsUnit (1 : R)))
    | succ n ihn =>
        intro hpow_mem
        have hmul_mem : x ^ n * x ∈ p := by
          simpa [pow_succ] using hpow_mem
        rcases hp.mem_or_mem hmul_mem with hxn_mem | hx_mem
        · exact ihn hxn_mem
        · exact hxnotmem hx_mem
  have hdisj : Disjoint (Submonoid.powers x : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    intro y hyS hyP
    rcases hyS with ⟨n, rfl⟩
    exact hpow_not_mem n hyP
  -- Then apply the standard localization theorem for primes disjoint from the denominator set.
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) (Localization.Away x)
    p hp hdisj

/-- Helper for Lemma 15.122.2: localizing at a nonmaximal prime strictly lowers Krull dimension in
a regular local ring. -/
lemma localizationAtPrime_ringKrullDim_lt_of_not_isMaximal
    (p : PrimeSpectrum R) (hp_not_max : ¬ p.asIdeal.IsMaximal) :
    ringKrullDim (Localization.AtPrime p.asIdeal) < ringKrullDim R := by
  -- In a local ring, every prime lies below the maximal ideal; nonmaximality makes the inclusion
  -- strict, which is the exact source-side input for the height drop.
  have hp_lt_max : p.asIdeal < maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal) ?_
    intro hp_eq_max
    exact hp_not_max (hp_eq_max ▸ IsLocalRing.maximalIdeal.isMaximal R)
  have hp_step :
      p.asIdeal.primeHeight + 1 ≤ (maximalIdeal R).primeHeight :=
    Ideal.primeHeight_add_one_le_of_lt hp_lt_max
  have hp_primeHeight_ne_top : p.asIdeal.primeHeight ≠ ⊤ := by
    have hmax_ne_top : (maximalIdeal R).primeHeight ≠ ⊤ := by
      simpa [Ideal.height_eq_primeHeight, IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using
        (ringKrullDim_ne_top (R := R))
    intro htop
    exact hmax_ne_top (by simpa [htop] using hp_step)
  have hp_height_lt_max :
      p.asIdeal.height < (maximalIdeal R).height := by
    -- Convert the strict prime-height drop into the corresponding strict height drop.
    simpa [Ideal.height_eq_primeHeight] using
      (ENat.add_one_le_iff hp_primeHeight_ne_top).mp hp_step
  -- Rewrite both Krull dimensions as heights at the relevant primes and conclude.
  calc
    ringKrullDim (Localization.AtPrime p.asIdeal) = p.asIdeal.height := by
      exact IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
        (Localization.AtPrime p.asIdeal)
    _ < (maximalIdeal R).height := by
      exact_mod_cast hp_height_lt_max
    _ = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim

/-- Helper for Lemma 15.122.2: every stalk of an away localization at a prime is again a regular
local ring, and in the nonunit local-ring branch its Krull dimension drops strictly. -/
lemma away_localization_at_prime_regular_local_dimension_lt
    {x : R} (hxmax : x ∈ maximalIdeal R) (q : PrimeSpectrum (Localization.Away x)) :
    IsRegularLocalRing (Localization.AtPrime q.asIdeal) ∧
      ringKrullDim (Localization.AtPrime q.asIdeal) < ringKrullDim R := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (Localization.Away x)) q
  have hxnotmem : x ∉ p.asIdeal := comap_away_not_mem x q
  have hx_jac : x ∈ Ring.jacobson R := by
    -- In a local ring the maximal ideal lies in the Jacobson radical, so the chosen parameter
    -- gives the source-faithful nonmaximality witness after contraction.
    have hmaxJac : maximalIdeal R ≤ Ring.jacobson R := by
      simpa [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
    exact hmaxJac hxmax
  have hp_not_max : ¬ p.asIdeal.IsMaximal :=
    not_isMaximal_of_mem_jacobson_of_not_mem hx_jac p hxnotmem
  let e :
      Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers x) q.asIdeal
  have hp_reg : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
    -- First move to the contracted prime of `R`, where regularity comes from the ambient regular
    -- ring, and only then transport once across the iterated-localization equivalence.
    let _ : IsRegularRing R := inferInstance
    simpa [p] using (IsRegularRing.isRegularLocalRing_atPrime p)
  constructor
  · let _ : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hp_reg
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv
  · -- The canonical iterated-localization equivalence preserves Krull dimension, so the strict
    -- drop is exactly the previously established nonmaximal-prime inequality on `R`.
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal)
          = ringKrullDim (Localization.AtPrime p.asIdeal) := by
              simpa using (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
      _ < ringKrullDim R :=
        localizationAtPrime_ringKrullDim_lt_of_not_isMaximal p hp_not_max

/-- Helper for Lemma 15.122.2: if the localization of a height-one prime ideal away from `x` is
generated by the image of a prime element `y : R`, then the original height-one prime ideal is
already the principal ideal `(y)`. -/
lemma height_one_prime_eq_span_of_localized_prime_generator
    {x y : R} (p : Ideal R) (hp : p.IsPrime) (hxnotmem : x ∉ p) (hyprime : Prime y)
    (hmap :
      Ideal.map (algebraMap R (Localization.Away x)) p =
        Ideal.span ({algebraMap R (Localization.Away x) y} : Set (Localization.Away x))) :
    p = Ideal.span ({y} : Set R) := by
  let hxspan : Ideal R := Ideal.span ({y} : Set R)
  have hxspan_prime : hxspan.IsPrime := by
    -- Convert the prime element into the corresponding prime principal ideal.
    simpa [hxspan] using (Ideal.span_singleton_prime hyprime.ne_zero).2 hyprime
  have hdisj_p : Disjoint (Submonoid.powers x : Set R) (p : Set R) := by
    -- The localization identity for `p` needs disjointness from the denominator powers of `x`.
    rw [Ideal.disjoint_powers_iff_notMem x hp.isRadical]
    exact hxnotmem
  have hcomap_p :
      Ideal.comap (algebraMap R (Localization.Away x))
        (Ideal.map (algebraMap R (Localization.Away x)) p) = p := by
    -- Contracting the extension of a prime ideal disjoint from the denominator set recovers it.
    simpa using
      (IsLocalization.comap_map_of_isPrime_disjoint
        (Submonoid.powers x) (Localization.Away x) hp hdisj_p)
  have hy_mem_p : y ∈ p := by
    -- The localized generator lies in the extended ideal, so its numerator lies in `p`.
    have hy_mem_map :
        algebraMap R (Localization.Away x) y ∈
          Ideal.map (algebraMap R (Localization.Away x)) p := by
      rw [hmap]
      exact Ideal.mem_span_singleton_self _
    have hy_mem_comap :
        y ∈ Ideal.comap (algebraMap R (Localization.Away x))
          (Ideal.map (algebraMap R (Localization.Away x)) p) := by
      rwa [Ideal.mem_comap]
    simpa [hcomap_p] using hy_mem_comap
  have hyspan_le_p : hxspan ≤ p := by
    -- Once `y ∈ p`, the principal ideal `(y)` is contained in `p`.
    exact (Ideal.span_singleton_le_iff_mem p).2 hy_mem_p
  have hx_not_mem_span : x ∉ hxspan := by
    -- The containment `(y) ≤ p` propagates the avoidance of `x`.
    intro hxmem
    exact hxnotmem (hyspan_le_p hxmem)
  have hdisj_span : Disjoint (Submonoid.powers x : Set R) (hxspan : Set R) := by
    -- The principal prime `(y)` is likewise disjoint from the denominator powers of `x`.
    rw [Ideal.disjoint_powers_iff_notMem x hxspan_prime.isRadical]
    exact hx_not_mem_span
  have hcomap_span :
      Ideal.comap (algebraMap R (Localization.Away x))
        (Ideal.map (algebraMap R (Localization.Away x)) hxspan) = hxspan := by
    -- Contracting the extension of `(y)` across the same localization also recovers `(y)`.
    simpa using
      (IsLocalization.comap_map_of_isPrime_disjoint
        (Submonoid.powers x) (Localization.Away x) hxspan_prime hdisj_span)
  -- Compare the two contracted extended ideals after rewriting the principal ideal map.
  calc
    p = Ideal.comap (algebraMap R (Localization.Away x))
          (Ideal.map (algebraMap R (Localization.Away x)) p) := hcomap_p.symm
    _ = Ideal.comap (algebraMap R (Localization.Away x))
          (Ideal.span ({algebraMap R (Localization.Away x) y} : Set (Localization.Away x))) := by
            rw [hmap]
    _ = Ideal.comap (algebraMap R (Localization.Away x))
          (Ideal.map (algebraMap R (Localization.Away x)) hxspan) := by
            rw [Ideal.map_span, Set.image_singleton]
    _ = hxspan := hcomap_span

/-- Helper for Lemma 15.122.2: localizing the away-localized ideal `pR_x` further at a prime
`q` agrees with localizing `p` directly along the composite map `R → R_x → (R_x)_q`. -/
lemma away_map_then_atPrime_eq_direct_map
    {x : R} (p : Ideal R) (q : PrimeSpectrum (Localization.Away x)) :
    Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime q.asIdeal))
      (Ideal.map (algebraMap R (Localization.Away x)) p) =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p := by
  -- Collapse the iterated ideal extension along the localization tower.
  rw [Ideal.map_map]
  congr 1
  ext r
  simp [RingHom.comp_apply]

/-- Helper for Lemma 15.122.2: if `p` is not contained in the contraction of
`q ∈ Spec(R_x)`, then the further localization of `pR_x` at `q` is already the unit ideal. -/
lemma away_map_then_atPrime_eq_top_of_not_le
    {x : R} (p : Ideal R) (q : PrimeSpectrum (Localization.Away x))
    (hnot_le :
      ¬ p ≤ (PrimeSpectrum.comap (algebraMap R (Localization.Away x)) q).asIdeal) :
    Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime q.asIdeal))
      (Ideal.map (algebraMap R (Localization.Away x)) p) = ⊤ := by
  classical
  let q0 : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (Localization.Away x)) q
  have hy_exists : ∃ y : R, y ∈ p ∧ y ∉ q0.asIdeal := by
    -- Negating the ideal inclusion produces a witness from `p` that avoids the contracted prime.
    by_contra hy_exists_neg
    apply hnot_le
    intro y hy_mem
    by_contra hy_not_mem
    exact hy_exists_neg ⟨y, hy_mem, hy_not_mem⟩
  rcases hy_exists with ⟨y, hy_mem_p, hy_not_mem_q0⟩
  have hy_not_mem_q :
      algebraMap R (Localization.Away x) y ∉ q.asIdeal := by
    -- Membership in the contraction is exactly membership after applying `R → R_x`.
    simpa [q0, Ideal.mem_comap] using hy_not_mem_q0
  have hy_mem_map :
      algebraMap (Localization.Away x) (Localization.AtPrime q.asIdeal)
        (algebraMap R (Localization.Away x) y) ∈
          Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime q.asIdeal))
            (Ideal.map (algebraMap R (Localization.Away x)) p) := by
    -- The chosen witness remains in the extended ideal after both localization steps.
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hy_mem_p)
  have hy_unit :
      IsUnit
        (algebraMap (Localization.Away x) (Localization.AtPrime q.asIdeal)
          (algebraMap R (Localization.Away x) y)) := by
    -- An element avoiding `q` becomes a unit in the localization at `q`.
    exact
      IsLocalization.map_units (Localization.AtPrime q.asIdeal)
        ⟨algebraMap R (Localization.Away x) y, hy_not_mem_q⟩
  -- A proper ideal containing a unit is the whole ring.
  exact Ideal.eq_top_of_isUnit_mem _ hy_mem_map hy_unit

/-- Helper for Lemma 15.122.2: after localizing a height-one prime away from the chosen parameter,
the source proof first trivializes the resulting line module and then clears denominators to obtain
a generator from the base ring. -/
lemma localized_height_one_prime_has_base_generator
    (n : ℕ)
    (ih :
      ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S],
        ringKrullDim S ≤ n → UniqueFactorizationMonoid S)
    (hdim : ringKrullDim R ≤ n + 1)
    (x : R) (hxmax : x ∈ maximalIdeal R) (hxsq : x ∉ maximalIdeal R ^ 2)
    (hxprime : (Ideal.span ({x} : Set R)).IsPrime) (p : Ideal R) (hp : p.IsPrime)
    (hheight : p.height = 1) (hxnotmem : x ∉ p) :
    ∃ f : R,
      f ∈ p ∧
        Ideal.map (algebraMap R (Localization.Away x)) p =
          Ideal.span ({algebraMap R (Localization.Away x) f} : Set (Localization.Away x)) := by
  -- TODO: the complementary prime-local branch is now isolated by
  -- `away_map_then_atPrime_eq_top_of_not_le`; the remaining source-faithful work is the hard
  -- branch `p ≤ q₀`, where one must show the stalks of
  -- `Ideal.map (algebraMap R (Localization.Away x)) p` are free of rank `1`, globalize that
  -- rank-one statement over `Rₓ`, trivialize the resulting invertible module, and then clear
  -- denominators to replace the localized generator by the image of an element of `p`.
  sorry

/-- Helper for Lemma 15.122.2: if the product of a multiset of ring elements lies in a prime
ideal, then one of the factors already lies in that prime ideal. -/
lemma exists_mem_of_prod_mem_prime (p : Ideal R) (hp : p.IsPrime) (s : Multiset R)
    (hs : s.prod ∈ p) :
    ∃ y : R, y ∈ s ∧ y ∈ p := by
  -- Induct on the multiset and use primality on the head-times-tail product.
  induction s using Multiset.induction_on with
  | empty =>
      have hp_top : p = ⊤ :=
        p.eq_top_of_isUnit_mem hs (by simpa using (isUnit_one : IsUnit (1 : R)))
      exact False.elim (hp.ne_top hp_top)
  | @cons a s ih =>
      have hmul_mem : a * s.prod ∈ p := by
        simpa using hs
      rcases hp.mem_or_mem hmul_mem with ha_mem | hs_mem
      · exact ⟨a, by simp, ha_mem⟩
      · rcases ih hs_mem with ⟨y, hy_mem_s, hy_mem_p⟩
        exact ⟨y, by simp [hy_mem_s], hy_mem_p⟩

/-- Helper for Lemma 15.122.2: a factor appearing in a multiset divides the product of that
multiset. -/
lemma dvd_prod_of_mem_multiset (s : Multiset R) {y : R} (hy : y ∈ s) :
    y ∣ s.prod := by
  -- Induct on the multiset and peel off the chosen occurrence of `y`.
  induction s using Multiset.induction_on with
  | empty =>
      cases hy
  | @cons a s ih =>
      rcases Multiset.mem_cons.1 hy with rfl | hy_mem_s
      · exact ⟨s.prod, by simp⟩
      · rcases ih hy_mem_s with ⟨c, hc⟩
        exact ⟨a * c, by simpa [hc, mul_assoc, mul_left_comm, mul_comm]⟩

/-- Helper for Lemma 15.122.2: once the localized height-one prime is generated by the image of an
element `f ∈ p`, the source proof factors `f`, chooses an irreducible factor in `p`, and applies
Nagata's criterion to descend a prime generator back to `R`. -/
lemma localized_prime_generator_of_base_generator
    {x : R} (hxprime : (Ideal.span ({x} : Set R)).IsPrime)
    (p : Ideal R) (hp : p.IsPrime) (hheight : p.height = 1) (hxnotmem : x ∉ p)
    {f : R} (hfmem : f ∈ p)
    (hmap :
      Ideal.map (algebraMap R (Localization.Away x)) p =
        Ideal.span ({algebraMap R (Localization.Away x) f} : Set (Localization.Away x))) :
    ∃ y : R,
      Prime y ∧
        Ideal.map (algebraMap R (Localization.Away x)) p =
          Ideal.span ({algebraMap R (Localization.Away x) y} : Set (Localization.Away x)) := by
  let Rx := Localization.Away x
  have hmap_prime : (Ideal.map (algebraMap R Rx) p).IsPrime :=
    away_map_isPrime_of_not_mem (R := R) p hp hxnotmem
  have hp_ne_bot : p ≠ ⊥ := by
    -- A height-one prime ideal cannot be the zero ideal.
    intro hbot
    simpa [hbot] using hheight
  have hdisj_p : Disjoint (Submonoid.powers x : Set R) (p : Set R) := by
    -- The denominator powers stay disjoint from `p` because `x ∉ p`.
    rw [Ideal.disjoint_powers_iff_notMem x hp.isRadical]
    exact hxnotmem
  have hcomap_p :
      Ideal.comap (algebraMap R Rx) (Ideal.map (algebraMap R Rx) p) = p := by
    -- Contracting the localized prime ideal recovers the original prime.
    simpa using
      (IsLocalization.comap_map_of_isPrime_disjoint
        (Submonoid.powers x) Rx hp hdisj_p)
  have hf_loc_ne_zero : algebraMap R Rx f ≠ 0 := by
    -- If the localized generator vanished, then the localized prime ideal would be zero, forcing
    -- `p = ⊥`, contrary to height `1`.
    intro hf_loc_zero
    have hmap_bot : Ideal.map (algebraMap R Rx) p = ⊥ := by
      rw [hmap, hf_loc_zero]
      simp
    have hp_bot : p = ⊥ := by
      have hdenom :
          Submonoid.powers x ≤ nonZeroDivisors R := by
        have hx_ne_zero' : x ≠ 0 := by
          intro hx_zero
          exact hxnotmem (hx_zero ▸ Ideal.zero_mem p)
        intro z hz
        rcases hz with ⟨n, rfl⟩
        exact pow_mem (mem_nonZeroDivisors_iff_ne_zero.mpr hx_ne_zero') n
      calc
        p = Ideal.comap (algebraMap R Rx) (Ideal.map (algebraMap R Rx) p) := hcomap_p.symm
        _ = Ideal.comap (algebraMap R Rx) ⊥ := by rw [hmap_bot]
        _ = ⊥ := Ideal.comap_bot_of_injective (algebraMap R Rx)
              (IsLocalization.injective Rx hdenom)
    exact hp_ne_bot hp_bot
  have hf_ne_zero : f ≠ 0 := by
    -- Nonvanishing in the localization forces nonvanishing already in the base domain.
    intro hf_zero
    exact hf_loc_ne_zero (by simp [hf_zero])
  have hf_not_unit : ¬ IsUnit f := by
    -- A unit cannot lie in the proper prime ideal `p`.
    intro hf_unit
    exact hp.ne_top (p.eq_top_of_isUnit_mem hfmem hf_unit)
  have hf_loc_prime : Prime (algebraMap R Rx f) := by
    -- The chosen localized generator spans the localized prime ideal, so it is a prime element.
    have hspan_prime : (Ideal.span ({algebraMap R Rx f} : Set Rx)).IsPrime := by
      rw [← hmap]
      exact hmap_prime
    exact (Ideal.span_singleton_prime hf_loc_ne_zero).1 hspan_prime
  let _ : WfDvdMonoid R :=
    WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt Ideal.setOf_isPrincipal_wellFoundedOn_gt
  obtain ⟨factors, hfactors_irreducible, hfactors_prod, _⟩ :=
    (WfDvdMonoid.not_unit_iff_exists_factors_eq f hf_ne_zero).1 hf_not_unit
  have hfactor_mem :
      ∃ y : R, y ∈ factors ∧ y ∈ p := by
    -- Primality of `p` forces one irreducible factor of `f` to lie in `p`.
    have hprod_mem : factors.prod ∈ p := by
      simpa [hfactors_prod] using hfmem
    exact exists_mem_of_prod_mem_prime (R := R) p hp factors hprod_mem
  rcases hfactor_mem with ⟨y, hy_mem_factors, hy_mem_p⟩
  have hy_irreducible : Irreducible y := hfactors_irreducible y hy_mem_factors
  have hy_dvd_prod : y ∣ factors.prod := by
    -- Membership in the factor multiset gives divisibility of its product by `y`.
    exact dvd_prod_of_mem_multiset (R := R) factors hy_mem_factors
  have hy_dvd_f : y ∣ f := by
    -- Rewriting the factorization turns the product divisibility into divisibility of `f`.
    rcases hy_dvd_prod with ⟨c, hc⟩
    exact ⟨c, by
      calc
        y * c = factors.prod := hc
        _ = f := hfactors_prod⟩
  have hx_ne_zero : x ≠ 0 := by
    -- The chosen denominator avoids `p`, whereas `0 ∈ p`.
    intro hx_zero
    exact hxnotmem (hx_zero ▸ Ideal.zero_mem p)
  have hx_prime_element : Prime x :=
    (Ideal.span_singleton_prime hx_ne_zero).1 hxprime
  have hpowers_prime :
      (Submonoid.powers x : Submonoid R) ≤ Submonoid.closure {z : R | Prime z} := by
    -- The denominator submonoid is generated by the single prime element `x`.
    intro z hz
    rcases hz with ⟨n, rfl⟩
    have hx_mem_closure : x ∈ Submonoid.closure {z : R | Prime z} :=
      Submonoid.subset_closure (by simpa using hx_prime_element)
    exact pow_mem hx_mem_closure n
  have hy_loc_mem_map : algebraMap R Rx y ∈ Ideal.map (algebraMap R Rx) p :=
    Ideal.mem_map_of_mem (algebraMap R Rx) hy_mem_p
  have hy_loc_not_unit : ¬ IsUnit (algebraMap R Rx y) := by
    -- An element of the proper localized prime ideal cannot be a unit.
    intro hy_loc_unit
    exact hmap_prime.ne_top
      ((Ideal.map (algebraMap R Rx) p).eq_top_of_isUnit_mem hy_loc_mem_map hy_loc_unit)
  have hy_loc_irreducible : Irreducible (algebraMap R Rx y) := by
    -- Localizing an irreducible away from a prime element keeps it irreducible or turns it into a
    -- unit; here the prime-ideal membership rules out the unit branch.
    exact
      (localization_irreducible_or_isUnit_of_irreducible
        (A := R) (S := Submonoid.powers x) hpowers_prime hy_irreducible).resolve_right
        hy_loc_not_unit
  have hy_loc_dvd_f : algebraMap R Rx y ∣ algebraMap R Rx f := by
    -- Divisibility is preserved by the localization map.
    rcases hy_dvd_f with ⟨c, hc⟩
    exact ⟨algebraMap R Rx c, by simpa [map_mul] using congrArg (algebraMap R Rx) hc⟩
  have hy_loc_assoc_f : Associated (algebraMap R Rx y) (algebraMap R Rx f) :=
    hy_loc_irreducible.associated_of_dvd hf_loc_prime.irreducible hy_loc_dvd_f
  have hy_loc_prime : Prime (algebraMap R Rx y) := by
    -- Associated elements generate the same principal ideal, so the localized factor also spans
    -- the localized prime ideal and is therefore prime.
    have hy_span_prime : (Ideal.span ({algebraMap R Rx y} : Set Rx)).IsPrime := by
      rw [Ideal.span_singleton_eq_span_singleton.2 hy_loc_assoc_f]
      rw [← hmap]
      exact hmap_prime
    exact (Ideal.span_singleton_prime hy_loc_irreducible.ne_zero).1 hy_span_prime
  have hy_prime : Prime y := by
    -- Nagata's criterion descends primality from the localization back to `R`.
    exact
      (prime_iff_localization_prime_or_isUnit_of_irreducible
        (A := R) (S := Submonoid.powers x) hpowers_prime hy_irreducible).2
        (Or.inl hy_loc_prime)
  refine ⟨y, hy_prime, ?_⟩
  -- Replacing `f` by the associated localized factor does not change the generated ideal.
  calc
    Ideal.map (algebraMap R Rx) p =
      Ideal.span ({algebraMap R Rx f} : Set Rx) := hmap
    _ = Ideal.span ({algebraMap R Rx y} : Set Rx) := by
      rw [Ideal.span_singleton_eq_span_singleton.2 hy_loc_assoc_f]

/-- Helper for Lemma 15.122.2: the hard branch of the source induction is the case of a height-one
prime ideal avoiding the chosen prime parameter. -/
-- Route correction: the previous file closed the theorem through the out-of-scope shared owner.
-- The remaining blocker is exactly the source-faithful localization-and-Nagata argument for this
-- branch, so it is isolated here as the single open frontier.
theorem height_one_prime_isPrincipal_of_not_mem_prime_parameter
    (n : ℕ)
    (ih :
      ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S],
        ringKrullDim S ≤ n → UniqueFactorizationMonoid S)
    (hdim : ringKrullDim R ≤ n + 1)
    (x : R) (hxmax : x ∈ maximalIdeal R) (hxsq : x ∉ maximalIdeal R ^ 2)
    (hxprime : (Ideal.span ({x} : Set R)).IsPrime) (p : Ideal R) (hp : p.IsPrime)
    (hheight : p.height = 1) (hxnotmem : x ∉ p) :
    p.IsPrincipal := by
  -- First obtain a localized generator coming from an element of the base ring.
  obtain ⟨f, hfmem, hbase_gen⟩ :=
    localized_height_one_prime_has_base_generator
      (R := R) n (ih := ih) hdim x hxmax hxsq hxprime p hp hheight hxnotmem
  -- Then run the source factorization/Nagata step to replace it by a prime element of `R`.
  obtain ⟨y, hyprime, hygen⟩ :=
    localized_prime_generator_of_base_generator
      (R := R) (x := x) hxprime p hp hheight hxnotmem hfmem hbase_gen
  -- A prime generator surviving in the localization already generates the original height-one
  -- prime ideal.
  have hp_eq :
      p = Ideal.span ({y} : Set R) :=
    height_one_prime_eq_span_of_localized_prime_generator
      (R := R) (x := x) (y := y) p hp hxnotmem hyprime hygen
  exact hp_eq ▸ inferInstance

/-- Helper for Lemma 15.122.2: a dimension bound gives the unique factorization owner by induction
on the Krull dimension. -/
theorem regularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_local
    (n : ℕ) (hdim : ringKrullDim R ≤ n) : UniqueFactorizationMonoid R := by
  induction n generalizing R with
  | zero =>
      -- In dimension `0`, the regular local ring is a field, hence factorial.
      have hdim0 : ringKrullDim R = 0 := by
        apply le_antisymm hdim
        exact ringKrullDim_nonneg_of_nontrivial
      let _ : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
      let hfield : IsField R := Ring.KrullDimLE.isField_of_isDomain (R := R)
      let _ : Field R := hfield.toField
      infer_instance
  | succ n ih =>
      -- Apply the height-one-prime criterion and then split at a single prime parameter.
      refine
        (uniqueFactorizationMonoid_iff_forall_height_one_prime_isPrincipal).2 ?_
      intro p hp hheight
      obtain ⟨x, hxmax, hxsq, hxprime⟩ :=
        exists_prime_parameter_of_height_one_prime p hp hheight
      have hx_ne_zero : x ≠ 0 := by
        intro hx0
        exact hxsq (by simpa [hx0] using (show (0 : R) ∈ maximalIdeal R ^ 2 from Ideal.zero_mem _))
      by_cases hxmem : x ∈ p
      · -- If the prime parameter lies in `p`, the height-one ideal is already principal.
        have hp_eq : p = Ideal.span ({x} : Set R) :=
          height_one_prime_eq_span_of_mem_prime_parameter x hx_ne_zero hxprime p hp hheight hxmem
        exact hp_eq ▸ inferInstance
      · -- Otherwise the remaining work is the localized source argument isolated above.
        exact
          height_one_prime_isPrincipal_of_not_mem_prime_parameter
            (R := R) n (ih := ih) hdim
            x hxmax hxsq hxprime p hp hheight hxmem

/-- Helper for Lemma 15.122.2: specialize the local dimension-bounded induction theorem at the
actual Krull dimension of the regular local ring. -/
noncomputable abbrev regularLocalRing_uniqueFactorizationMonoid_of_isRegularLocalRing :
    UniqueFactorizationMonoid R := by
  let n : ℕ := ((ringKrullDim R).unbotD 0).toNat
  have hdim_eq :
      ringKrullDim R = ((((ringKrullDim R).unbotD 0).toNat : ℕ∞) : WithBot ℕ∞) := by
    have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
    cases hs : ringKrullDim R with
    | bot =>
        exact (hbot hs).elim
    | coe d =>
        have hd_ne_top : d ≠ ⊤ := by
          intro hd_top
          exact htop <| by simp [hs, hd_top]
        simpa [hs] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hd_ne_top).symm
  have hdim : ringKrullDim R ≤ n := by
    simp [n] at hdim_eq ⊢
    exact hdim_eq.le
  exact regularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_local
    (R := R) (n := n) hdim

/-- Lemma 15.122.2: a regular local ring is a unique factorization domain. -/
instance regularLocalRing_uniqueFactorizationMonoid : UniqueFactorizationMonoid R := by
  -- The final instance is the direct specialization helper above.
  exact regularLocalRing_uniqueFactorizationMonoid_of_isRegularLocalRing (R := R)

end
