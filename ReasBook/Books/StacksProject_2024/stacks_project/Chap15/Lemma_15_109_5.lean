import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_151_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_153_11
import StacksProject_2024.stacks_project.Chap10.Lemma_10_62_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_7
import StacksProject_2024.stacks_project.Chap10.Proposition_10_152_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_43_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_109_1.Index
import StacksProject_2024.stacks_project.Chap15.Lemma_15_109_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_109_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

noncomputable section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "AhCompletion" => AdicCompletion (maximalIdeal Ah) Ah

/-- Helper for Lemma 15.109.5: regard the completion as an `Ah`-algebra through the canonical
comparison map. -/
local instance completionComparisonAlgebra : Algebra Ah ACompletion :=
  (henselizationCompletionComparison A Ah).toAlgebra

/-
Domain-style sampling:
- primary domain: minimal-prime comparison between a Noetherian local ring's henselization and
  maximal-ideal completion;
- sampled owner declarations:
  `minimalPrimes`,
  `henselizationCompletionComparison`,
  `branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime`,
  `ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion`;
- best owner abstraction: the source-facing theorem is a `bridge/view` statement over the
  canonical comparison map `henselizationCompletionComparison A Ah`, while the minimal-prime data
  should use the owner subtype `minimalPrimes _` rather than a raw ideal together with a separate
  membership hypothesis;
- primitive data: a minimal prime `q : minimalPrimes ACompletion` whose quotient has Krull
  dimension `1`;
- derived API: existence of a minimal prime `qh : minimalPrimes Ah` whose extension to
  `ACompletion` has radical `q`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below for a one-dimensional completed branch;
- `core/canonical`: `minimalPrimes`, `AdicCompletion`, `Ideal.map`, `Ideal.radical`, and the
  completion comparison owner `henselizationCompletionComparison`;
- `bridge/view`: passage from the chosen henselization to the completion along that canonical map.
-/

/-- Helper for Lemma 15.109.5: the contraction of a completion minimal prime along the canonical
comparison map is a minimal prime of the henselization. -/
lemma contracted_completion_minimalPrime_mem_minimalPrimes
    (q : minimalPrimes ACompletion) :
    Ideal.comap (henselizationCompletionComparison A Ah) q ∈ minimalPrimes Ah := by
  -- Rewrite the comparison map as the ambient `Ah`-algebra map and reuse Lemma `15.109.2`.
  simpa [completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
    comap_mem_minimalPrimes_of_completion_minimalPrime (A := A) (Ah := Ah) q

/-- Helper for Lemma 15.109.5: the canonical candidate in the henselization is the contraction of
the chosen completion branch. -/
noncomputable abbrev contracted_completion_minimalPrime
    (q : minimalPrimes ACompletion) : minimalPrimes Ah :=
  ⟨Ideal.comap (henselizationCompletionComparison A Ah) q,
    contracted_completion_minimalPrime_mem_minimalPrimes (A := A) (Ah := Ah) q⟩

/-- Helper for Lemma 15.109.5: the source branch-kernel is the kernel of localizing the
completion at the chosen minimal prime. -/
noncomputable abbrev completion_branch_kernel
    (q : minimalPrimes ACompletion) : Ideal ACompletion :=
  RingHom.ker (algebraMap ACompletion (Localization.AtPrime q.1))

/-- Helper for Lemma 15.109.5: localizing the completion at a minimal prime produces a
zero-dimensional local ring. This is the source step `dim((A^\wedge)_q) = 0`. -/
lemma completion_branch_localization_ringKrullDim_eq_zero
    (q : minimalPrimes ACompletion) :
    ringKrullDim (Localization.AtPrime q.1) = 0 := by
  -- The localization dimension is the height of `q`, and minimal primes have height `0`.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.1 (Localization.AtPrime q.1)]
  exact (Ideal.primeHeight_eq_zero_iff (I := q.1)).mpr q.2

/-- Helper for Lemma 15.109.5: some power of the chosen completion minimal prime lands in the
kernel of the localization map at that prime. This is the first concrete source reduction
`q^n ⊆ J`. -/
lemma exists_pow_completion_minimalPrime_le_completion_branch_kernel
    (q : minimalPrimes ACompletion) :
    ∃ n : ℕ, 0 < n ∧ q.1 ^ n ≤ completion_branch_kernel q := by
  let Bq := Localization.AtPrime q.1
  letI : IsNoetherianRing Bq :=
    IsLocalization.isNoetherianRing q.1.primeCompl Bq inferInstance
  have hdim0 : ringKrullDim Bq = 0 :=
    completion_branch_localization_ringKrullDim_eq_zero (A := A) q
  letI : Ring.KrullDimLE 0 Bq :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
  letI : IsArtinianRing Bq := (isArtinianRing_iff_krullDimLE_zero).mpr inferInstance
  have hnil : IsNilpotent (maximalIdeal Bq) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal Bq).mp inferInstance
  rcases hnil with ⟨n, hn⟩
  have hn_pos : 0 < n := by
    cases n with
    | zero =>
        simp at hn
    | succ n =>
        exact Nat.succ_pos _
  refine ⟨n, hn_pos, ?_⟩
  have hmap_q :
      Ideal.map (algebraMap ACompletion Bq) q.1 = maximalIdeal Bq := by
    -- In a localization at a prime, the extended prime is the closed point.
    simpa [Bq] using IsLocalization.AtPrime.map_eq_maximalIdeal q.1 Bq
  have hmap_pow :
      Ideal.map (algebraMap ACompletion Bq) (q.1 ^ n) = ⊥ := by
    -- After passing to the localization, the prime becomes the nilpotent maximal ideal.
    calc
      Ideal.map (algebraMap ACompletion Bq) (q.1 ^ n) =
          Ideal.map (algebraMap ACompletion Bq) q.1 ^ n := by
            rw [Ideal.map_pow]
      _ = maximalIdeal Bq ^ n := by
            rw [hmap_q]
      _ = ⊥ := hn
  -- Convert the vanishing of the localized power into kernel containment in the source ring.
  exact (Ideal.map_eq_bot_iff_le_ker).mp hmap_pow

/-- Helper for Lemma 15.109.5: the kernel of localization at the chosen minimal prime is already
contained in that prime. This is the source inclusion `J ⊆ q`. -/
lemma completion_branch_kernel_le_completion_minimalPrime
    (q : minimalPrimes ACompletion) :
    completion_branch_kernel (A := A) q ≤ q.1 := by
  intro x hx
  -- Vanishing in the localization forces the source element into the localized prime.
  exact
    (IsLocalization.to_map_eq_zero_iff (Localization.AtPrime q.1)
      q.1.primeCompl_le_nonZeroDivisors).mp hx

/-- Helper for Lemma 15.109.5: the branch kernel has the chosen minimal prime as its radical. This
packages the source relation `q^n ⊆ J ⊆ q` into `√J = q`. -/
lemma radical_completion_branch_kernel_eq_completion_minimalPrime
    (q : minimalPrimes ACompletion) :
    Ideal.radical (completion_branch_kernel (A := A) q) = q.1 := by
  obtain ⟨n, _hn, hpow⟩ :=
    exists_pow_completion_minimalPrime_le_completion_branch_kernel (A := A) q
  apply le_antisymm
  · -- First use `J ⊆ q`, then the primality of `q` to remove the radical.
    calc
      Ideal.radical (completion_branch_kernel (A := A) q) ≤ Ideal.radical q.1 :=
        Ideal.radical_mono (completion_branch_kernel_le_completion_minimalPrime (A := A) q)
      _ = q.1 := Ideal.radical_eq_iff.mpr (Ideal.minimalPrimes_isPrime q.2).isRadical
  · -- Conversely `q^n ⊆ J` puts every element of `q` into `√J`.
    intro x hx
    rw [Ideal.mem_radical]
    exact ⟨n, hpow (Ideal.pow_mem_pow hx n)⟩

/-- Helper for Lemma 15.109.5: every ideal annihilates its own cotangent module `I / I²`. -/
lemma ideal_le_annihilator_cotangent {R : Type u} [CommRing R] (I : Ideal R) :
    I ≤ Module.annihilator R I.Cotangent := by
  intro x hx
  rw [Module.mem_annihilator]
  intro z
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I z
  -- A product of two elements of `I` lies in `I²`, so its cotangent class is zero.
  have hxy_sq : (((x : R) • y : I) : R) ∈ I ^ 2 := by
    change x * (y : R) ∈ I ^ 2
    simpa [pow_two] using Ideal.mul_mem_mul hx y.2
  exact (Ideal.toCotangent_eq_zero I ((x : R) • y)).2 hxy_sq

/-- Helper for Lemma 15.109.5: the cotangent module of a finitely generated ideal is finite over
the quotient ring. -/
lemma ideal_cotangent_finite_of_fg {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) :
    Module.Finite (R ⧸ I) I.Cotangent := by
  letI : Module.Finite R I := Module.Finite.of_fg hI
  have hfiniteCotangent : Module.Finite R I.Cotangent := by
    -- The cotangent module is a quotient of the finitely generated ideal `I`.
    exact Module.Finite.of_surjective (Ideal.toCotangent I) (Ideal.toCotangent_surjective I)
  letI : Module.Finite R I.Cotangent := hfiniteCotangent
  letI : IsScalarTower R (R ⧸ I) I.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent I)
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent

/-- Helper for Lemma 15.109.5: in a one-dimensional Noetherian local ring, every nonclosed prime
is minimal. -/
lemma nonmaximal_prime_mem_minimalPrimes_of_local_krullDimLE_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ maximalIdeal R) :
    p.asIdeal ∈ minimalPrimes R := by
  -- A nonclosed prime sits strictly below the maximal ideal in a local ring.
  have hp_lt_max : p.asIdeal < maximalIdeal R := by
    exact lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal) hp
  have hdim : ringKrullDim R ≤ 1 := (Ring.krullDimLE_iff (R := R)).mp inferInstance
  have hmax_primeHeight_le_one : (maximalIdeal R).primeHeight ≤ 1 := by
    have hmax_primeHeight_le_one' : ((maximalIdeal R).primeHeight : WithBot ℕ∞) ≤ 1 := by
      simpa [IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim] using hdim
    exact_mod_cast hmax_primeHeight_le_one'
  have hp_add_one_le_one : p.asIdeal.primeHeight + 1 ≤ 1 := by
    -- Strict containment below the closed point forces the height to drop by at least one.
    exact calc
      p.asIdeal.primeHeight + 1 ≤ (maximalIdeal R).primeHeight := by
        simpa [Ideal.height_eq_primeHeight] using
          Ideal.primeHeight_add_one_le_of_lt hp_lt_max
      _ ≤ 1 := hmax_primeHeight_le_one
  have hp_primeHeight_lt_one : p.asIdeal.primeHeight < 1 := by
    have hp_primeHeight_ne_top : p.asIdeal.primeHeight ≠ ⊤ := by
      exact Ideal.primeHeight_ne_top_of_isPrime p.asIdeal
    exact (ENat.add_one_le_iff hp_primeHeight_ne_top).mp hp_add_one_le_one
  have hp_primeHeight_zero : p.asIdeal.primeHeight = 0 :=
    ENat.lt_one_iff_eq_zero.mp hp_primeHeight_lt_one
  -- Height zero is exactly the minimal-prime condition for a prime ideal.
  exact (Ideal.primeHeight_eq_zero_iff (I := p.asIdeal)).mp hp_primeHeight_zero

/-- Helper for Lemma 15.109.5: if one element outside a prime ideal annihilates a module, then
its localization at that prime is zero. -/
lemma localized_subsingleton_of_annihilator_not_mem_prime
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] {s : R}
    (hs : s ∉ p) (hs_ann : s ∈ Module.annihilator R M) :
    Subsingleton (LocalizedModule.AtPrime p M) := by
  rw [LocalizedModule.subsingleton_iff (S := p.primeCompl) (M := M)]
  intro y
  refine ⟨s, hs, ?_⟩
  exact (Module.mem_annihilator.mp hs_ann) y

/-- Helper for Lemma 15.109.5: the source inclusion `q^n ⊆ J` already implies that a positive
power of `q` annihilates the branch-kernel cotangent module `J / J²`. -/
lemma completion_branch_kernel_cotangent_annihilated_by_completion_minimalPrime_power
    (q : minimalPrimes ACompletion) :
    ∃ n : ℕ, 0 < n ∧
      q.1 ^ n ≤
        Module.annihilator ACompletion (completion_branch_kernel (A := A) q).Cotangent := by
  obtain ⟨n, hn, hpow⟩ :=
    exists_pow_completion_minimalPrime_le_completion_branch_kernel (A := A) q
  refine ⟨n, hn, hpow.trans ?_⟩
  -- Once an element lands in `J`, it kills `J / J²` for formal reasons.
  exact ideal_le_annihilator_cotangent (completion_branch_kernel (A := A) q)

/-- Helper for Lemma 15.109.5: localizing the cotangent module of the branch kernel at the chosen
minimal prime gives zero. This is the source step `(J / J²)_q = 0`. -/
lemma completion_branch_kernel_cotangent_localized_subsingleton
    (q : minimalPrimes ACompletion) :
    Subsingleton
      (LocalizedModule.AtPrime q.1 (completion_branch_kernel (A := A) q).Cotangent) := by
  rw [LocalizedModule.subsingleton_iff (S := q.1.primeCompl)
    (M := (completion_branch_kernel (A := A) q).Cotangent)]
  intro z
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (completion_branch_kernel (A := A) q) z
  have hy_zero :
      algebraMap ACompletion (Localization.AtPrime q.1) (y : ACompletion) = 0 := by
    -- Elements of the branch kernel vanish after localizing at `q` by definition.
    simpa [completion_branch_kernel, RingHom.mem_ker] using y.2
  obtain ⟨s, hs_mul_zero⟩ :=
    (IsLocalization.map_eq_zero_iff q.1.primeCompl
      (Localization.AtPrime q.1) (y : ACompletion)).mp hy_zero
  refine ⟨s, s.2, ?_⟩
  have hs_sq :
      ((((s : ACompletion) • y : completion_branch_kernel (A := A) q) : ACompletion)) ∈
        completion_branch_kernel (A := A) q ^ 2 := by
    -- The chosen denominator kills the representative outright, hence its cotangent class is zero.
    change (s : ACompletion) * (y : ACompletion) ∈ completion_branch_kernel (A := A) q ^ 2
    rw [hs_mul_zero]
    exact (completion_branch_kernel (A := A) q ^ 2).zero_mem
  exact
    (Ideal.toCotangent_eq_zero (completion_branch_kernel (A := A) q)
      ((s : ACompletion) • y)).2 hs_sq

/-- Helper for Lemma 15.109.5: away from primes containing `q`, the branch-kernel cotangent
module localizes to zero by inverting an annihilating element of `q`. -/
lemma completion_branch_kernel_cotangent_localized_subsingleton_of_not_le
    (q : minimalPrimes ACompletion) {p : PrimeSpectrum ACompletion}
    (hqp : ¬ q.1 ≤ p.asIdeal) :
    Subsingleton
      (LocalizedModule.AtPrime p.asIdeal (completion_branch_kernel (A := A) q).Cotangent) := by
  obtain ⟨n, hn, hann⟩ :=
    completion_branch_kernel_cotangent_annihilated_by_completion_minimalPrime_power
      (A := A) q
  rcases SetLike.not_le_iff_exists.mp hqp with ⟨s, hsq, hsp⟩
  have hs_pow_ann :
      s ^ n ∈ Module.annihilator ACompletion (completion_branch_kernel (A := A) q).Cotangent :=
    hann (Ideal.pow_mem_pow hsq n)
  have hs_pow_not_mem : s ^ n ∉ p.asIdeal := by
    intro hs_pow_mem
    exact hsp (p.asIdeal.isPrime.mem_of_pow_mem n hs_pow_mem)
  -- The inverted power of `s` annihilates the whole cotangent module after localization.
  exact
    localized_subsingleton_of_annihilator_not_mem_prime
      (p := p.asIdeal) hs_pow_not_mem hs_pow_ann

/-- Helper for Lemma 15.109.5: for every nonclosed prime of the completion, the cotangent module
of the branch kernel localizes to zero. This is the pointwise support calculation from the source
proof. -/
lemma completion_branch_kernel_cotangent_localized_subsingleton_of_ne_closedPoint
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1)
    {p : PrimeSpectrum ACompletion} (hp : p.asIdeal ≠ maximalIdeal ACompletion) :
    Subsingleton
      (LocalizedModule.AtPrime p.asIdeal (completion_branch_kernel (A := A) q).Cotangent) := by
  by_cases hqp : q.1 ≤ p.asIdeal
  · let B : Type u := ACompletion ⧸ q.1
    let π : ACompletion →+* B := Ideal.Quotient.mk q.1
    letI : CommRing B := inferInstance
    letI : IsLocalRing B := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
    letI : IsNoetherianRing B := inferInstance
    letI : IsDomain B := Ideal.Quotient.isDomain q.1
    letI : Ring.KrullDimLE 1 B := by
      exact (Ring.krullDimLE_iff (R := B)).mpr (by simpa [B] using hdim.le)
    let pbar : PrimeSpectrum B :=
      ⟨Ideal.map π p.asIdeal,
        Ideal.IsPrime.map_of_surjective_of_ker_le
          (f := π) Ideal.Quotient.mk_surjective (by
            simpa [π, Ideal.mk_ker] using hqp)⟩
    have hpbar_ne_max : pbar.asIdeal ≠ maximalIdeal B := by
      intro hpbar_eq_max
      have hp_eq_max : p.asIdeal = maximalIdeal ACompletion := by
        calc
          p.asIdeal = Ideal.comap π (Ideal.map π p.asIdeal) := by
            simpa [π] using (Ideal.comap_map_mk hqp)
          _ = Ideal.comap π (maximalIdeal B) := by simpa [pbar] using hpbar_eq_max
          _ = Ideal.comap π (Ideal.map π (maximalIdeal ACompletion)) := by
            rw [IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective]
          _ = maximalIdeal ACompletion := by
            rw [Ideal.comap_map_mk (IsLocalRing.le_maximalIdeal (q.1 : Ideal ACompletion))]
      exact hp hp_eq_max
    have hpbar_min :
        pbar.asIdeal ∈ minimalPrimes B :=
      nonmaximal_prime_mem_minimalPrimes_of_local_krullDimLE_one pbar hpbar_ne_max
    have hpbar_eq_bot : pbar.asIdeal = (⊥ : Ideal B) := by
      simpa [IsDomain.minimalPrimes_eq_singleton_bot B] using hpbar_min
    have hp_eq_q : p.asIdeal = q.1 := by
      calc
        p.asIdeal = Ideal.comap π (Ideal.map π p.asIdeal) := by
          simpa [π] using (Ideal.comap_map_mk hqp)
        _ = Ideal.comap π (⊥ : Ideal B) := by simpa [pbar] using hpbar_eq_bot
        _ = q.1 := by
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    -- Once `p = q`, reduce to the already established localization-at-`q` computation.
    simpa [hp_eq_q] using
      completion_branch_kernel_cotangent_localized_subsingleton (A := A) q
  · -- If `q` is not contained in `p`, invert an annihilating element of `q`.
    exact
      completion_branch_kernel_cotangent_localized_subsingleton_of_not_le
        (A := A) q hqp

/-- Helper for Lemma 15.109.5: a power of the closed point annihilates the branch-kernel
cotangent module. This packages the support calculation needed for Lemma `15.109.4`. -/
lemma completion_branch_kernel_cotangent_annihilated_by_closed_point_power
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    ∃ c : ℕ,
      maximalIdeal ACompletion ^ c ≤
        Module.annihilator ACompletion (completion_branch_kernel (A := A) q).Cotangent := by
  let J : Ideal ACompletion := completion_branch_kernel (A := A) q
  let M := J.Cotangent
  letI : Module.Finite (ACompletion ⧸ J) M :=
    ideal_cotangent_finite_of_fg (I := J) (Ideal.fg_of_isNoetherianRing J)
  letI : IsScalarTower ACompletion (ACompletion ⧸ J) M :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent J)
  letI : Module.Finite ACompletion M :=
    Module.Finite.of_restrictScalars_finite ACompletion (ACompletion ⧸ J) M
  have hsupport :
      Module.support ACompletion M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal ACompletion) := by
    intro p hp
    by_cases hpmax : p.asIdeal = maximalIdeal ACompletion
    · -- The closed point obviously belongs to the zero locus of the maximal ideal.
      simpa [PrimeSpectrum.zeroLocus_eq_singleton, IsLocalRing.closedPoint, hpmax]
    · have hp_sub :
          Subsingleton (LocalizedModule.AtPrime p.asIdeal M) := by
          simpa [M, J] using
            completion_branch_kernel_cotangent_localized_subsingleton_of_ne_closedPoint
              (A := A) q hdim hpmax
      exact False.elim <|
        (not_nontrivial_iff_subsingleton.mpr hp_sub) (Module.mem_support_iff.mp hp)
  -- Convert the pointwise support computation into a uniform annihilator power.
  exact
    (Module.exists_pow_le_annihilator_iff_support_subset_zeroLocus
      (M := M) (maximalIdeal ACompletion)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal ACompletion))).mpr hsupport

/-- Helper for Lemma 15.109.5: extending an ideal or first taking its radical gives the same
radical upstairs. -/
lemma radical_map_radical_eq
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R) :
    Ideal.radical (Ideal.map f (Ideal.radical I)) = Ideal.radical (Ideal.map f I) := by
  apply le_antisymm
  · -- First map the radical into the radical of the mapped ideal, then remove the outer radical.
    calc
      Ideal.radical (Ideal.map f (Ideal.radical I)) ≤
          Ideal.radical (Ideal.radical (Ideal.map f I)) := by
            exact Ideal.radical_mono (Ideal.map_radical_le (f := f) (I := I))
      _ = Ideal.radical (Ideal.map f I) := by
            simpa using (Ideal.radical_isRadical (Ideal.map f I)).radical
  · -- The original ideal sits inside its radical, so the same holds after extension.
    exact Ideal.radical_mono (Ideal.map_mono (Ideal.subset_radical I))

/-- Helper for Lemma 15.109.5: the maximal-ideal completion of the henselization `Ah` is
canonically identified with the maximal-ideal completion of `A`, viewed as an `A`-algebra
equivalence. -/
noncomputable def completion_compare_algEquiv :
    ACompletion ≃ₐ[A] AhCompletion := by
  letI : IsNoetherianRing Ah := isNoetherianRing_henselization A Ah
  letI : Module.Flat A Ah := henselizationMap_faithfullyFlat.flat
  let eRing : ACompletion ≃+* AhCompletion :=
    RingEquiv.ofBijective (maximalIdealCompletionMap (algebraMap A Ah))
      (maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
        (A := A) (B := Ah)
        IsHenselizationOf.map_maximalIdeal
        IsHenselizationOf.residueField_bijective)
  refine AlgEquiv.ofRingEquiv eRing ?_
  intro x
  -- The completion comparison extends the original local map `A → Ah`.
  simpa [eRing, RingHom.comp_apply] using
    DFunLike.congr_fun
      (maximalIdealCompletionMap_comp (algebraMap A Ah)) x

/-- Helper for Lemma 15.109.5: the canonical map from the henselization to the common completion
still sends the closed point of `Ah` to the closed point of the completion. -/
lemma henselization_completionComparison_map_maximalIdeal :
    Ideal.map (algebraMap Ah ACompletion) (maximalIdeal Ah) = maximalIdeal ACompletion := by
  -- First rewrite the henselization closed point as the image of the base maximal ideal.
  calc
    Ideal.map (algebraMap Ah ACompletion) (maximalIdeal Ah) =
        Ideal.map (algebraMap Ah ACompletion)
          (Ideal.map (algebraMap A Ah) (maximalIdeal A)) := by
          rw [IsHenselizationOf.map_maximalIdeal]
    _ = Ideal.map
          ((algebraMap Ah ACompletion).comp (algebraMap A Ah))
          (maximalIdeal A) := by
          rw [Ideal.map_map]
    _ = Ideal.map (algebraMap A ACompletion) (maximalIdeal A) := by
          rfl
    _ = maximalIdeal ACompletion := by
          simpa [ACompletion] using completion_map_maximalIdeal_eq_maximalIdeal A

/-- Helper for Lemma 15.109.5: the canonical map from the henselization to the common completion
is a local homomorphism. -/
local instance henselization_completionComparison_isLocalHom :
    IsLocalHom (algebraMap Ah ACompletion) := by
  refine IsLocalHom.mk ?_
  intro x hx_unit
  by_contra hx_nonunit
  have hx_mem : x ∈ maximalIdeal Ah := by
    exact (IsLocalRing.mem_maximalIdeal x).2 hx_nonunit
  have hmap_mem : algebraMap Ah ACompletion x ∈ maximalIdeal ACompletion := by
    -- Mapping a nonunit of the henselization lands in the closed point of the completion.
    rw [← henselization_completionComparison_map_maximalIdeal (A := A) (Ah := Ah)]
    exact Ideal.mem_map_of_mem _ hx_mem
  exact ((IsLocalRing.mem_maximalIdeal _).1 hmap_mem) hx_unit

/-- Helper for Lemma 15.109.5: the canonical map from the henselization to the common completion
induces a bijection on residue fields. -/
lemma henselization_completionComparison_residueField_bijective :
    Function.Bijective (ResidueField.map (algebraMap Ah ACompletion)) := by
  have hAres :
      Function.Bijective (ResidueField.map (algebraMap A ACompletion)) :=
    maximalIdealCompletion_residueField_bijective A
  have hAhres :
      Function.Bijective (ResidueField.map (algebraMap A Ah)) :=
    IsHenselizationOf.residueField_bijective
  have hcomp :
      (ResidueField.map (algebraMap Ah ACompletion)).comp
          (ResidueField.map (algebraMap A Ah)) =
        ResidueField.map (algebraMap A ACompletion) := by
    -- Both residue-field maps come from the same composite local map `A → Ah → A^∧`.
    ext x
    simp [IsScalarTower.algebraMap_eq A Ah ACompletion]
  constructor
  · intro x y hxy
    obtain ⟨x₀, rfl⟩ := hAhres.2 x
    obtain ⟨y₀, rfl⟩ := hAhres.2 y
    apply hAhres.1
    apply hAres.1
    simpa [Function.comp, hcomp] using hxy
  · intro z
    obtain ⟨z₀, hz₀⟩ := hAres.2 z
    obtain ⟨w, rfl⟩ := hAhres.2 z₀
    refine ⟨w, ?_⟩
    simpa [Function.comp, hcomp] using hz₀

/-- Helper for Lemma 15.109.5: the common completion can be viewed directly as the maximal-ideal
completion of the henselization, now as an `Ah`-algebra equivalence. -/
noncomputable def completion_compare_algEquiv_henselization :
    AhCompletion ≃ₐ[Ah] ACompletion := by
  letI : IsNoetherianRing Ah := isNoetherianRing_henselization A Ah
  letI : Module.Flat Ah ACompletion :=
    RingHom.flat_algebraMap_iff.mp <| by
      simpa [completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
        (henselizationCompletionComparison_flat (A := A) (Ah := Ah))
  let eRing : AhCompletion ≃+* ACompletion :=
    RingEquiv.ofBijective (maximalIdealCompletionMap (algebraMap Ah ACompletion))
      (maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
        (A := Ah) (B := ACompletion)
        (henselization_completionComparison_map_maximalIdeal (A := A) (Ah := Ah))
        (henselization_completionComparison_residueField_bijective (A := A) (Ah := Ah)))
  refine AlgEquiv.ofRingEquiv eRing ?_
  intro x
  -- The `Ah`-linear completion comparison extends the original map `Ah → A^∧`.
  simpa [eRing, RingHom.comp_apply] using
    DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap Ah ACompletion)) x

/-- Helper for Lemma 15.109.5: transport the completed branch kernel from `ACompletion` to the
common completion viewed as an `Ah`-algebra. -/
noncomputable abbrev henselization_completion_branch_kernel
    (q : minimalPrimes ACompletion) : Ideal AhCompletion :=
  Ideal.comap
    (completion_compare_algEquiv_henselization (A := A) (Ah := Ah)).toRingHom
    (completion_branch_kernel (A := A) q)

/-- Helper for Lemma 15.109.5: quotienting the henselization completion by the transported branch
kernel recovers the original completed branch quotient. -/
noncomputable def henselization_completion_branch_kernel_quotient_equiv
    (q : minimalPrimes ACompletion) :
    (AhCompletion ⧸ henselization_completion_branch_kernel (A := A) (Ah := Ah) q) ≃ₐ[Ah]
      (ACompletion ⧸ completion_branch_kernel (A := A) q) := by
  let e := completion_compare_algEquiv_henselization (A := A) (Ah := Ah)
  -- The quotient comparison is the canonical quotient transport along the completion equivalence.
  refine Ideal.quotientEquivAlg _ _ e ?_
  simpa [henselization_completion_branch_kernel] using
    (Ideal.map_comap_of_surjective e.toRingHom e.surjective
      (completion_branch_kernel (A := A) q))

/-- Helper for Lemma 15.109.5: an annihilator bound for the completion-side branch-kernel
cotangent module transports across the common completion equivalence to the henselization-side
branch-kernel cotangent module. -/
lemma henselization_completion_branch_kernel_cotangent_transport
    (q : minimalPrimes ACompletion) {c : ℕ}
    (hc :
      maximalIdeal ACompletion ^ c ≤
        Module.annihilator ACompletion (completion_branch_kernel (A := A) q).Cotangent) :
    maximalIdeal AhCompletion ^ c ≤
      Module.annihilator AhCompletion
        (henselization_completion_branch_kernel (A := A) (Ah := Ah) q).Cotangent := by
  let e := completion_compare_algEquiv_henselization (A := A) (Ah := Ah)
  let J : Ideal ACompletion := completion_branch_kernel (A := A) q
  let Jh : Ideal AhCompletion := henselization_completion_branch_kernel (A := A) (Ah := Ah) q
  have hmapJh : Ideal.map e.toRingHom Jh = J := by
    -- Proof comment: `Jh` was defined as the transport of `J` along the completion equivalence.
    simpa [Jh, J] using Ideal.map_comap_of_surjective e.toRingHom e.surjective J
  have hcomapJh_sq : Ideal.comap e.toRingHom (J ^ 2) = Jh ^ 2 := by
    -- Proof comment: squares commute with transport because `e` is a surjective ring
    -- equivalence.
    calc
      Ideal.comap e.toRingHom (J ^ 2) =
          Ideal.comap e.toRingHom (Ideal.map e.toRingHom (Jh ^ 2)) := by
            rw [Ideal.map_pow, hmapJh]
      _ = Jh ^ 2 ⊔ Ideal.comap e.toRingHom (⊥ : Ideal ACompletion) := by
            exact Ideal.comap_map_of_surjective e.toRingHom e.surjective (Jh ^ 2)
      _ = Jh ^ 2 := by
            simp
  intro x hx
  rw [Module.mem_annihilator]
  intro z
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective Jh z
  have hxJ : e x ∈ maximalIdeal ACompletion ^ c := by
    -- Proof comment: rewrite source closed-point powers by contracting them along the ring
    -- equivalence `e`.
    rw [← ringEquiv_comap_maximalIdeal_pow_eq (e := e.toRingEquiv) (n := c)] at hx
    exact hx
  have hxe_ann : e x ∈ Module.annihilator ACompletion J.Cotangent := hc hxJ
  have hyJ : (e y : ACompletion) ∈ J := y.2
  have hxy_toCot_zero :
      J.toCotangent ((e x : ACompletion) • (⟨e y, hyJ⟩ : J)) = 0 := by
    -- Proof comment: evaluate the transported annihilator statement on the cotangent class of
    -- `y`.
    simpa using Module.mem_annihilator.mp hxe_ann (J.toCotangent ⟨e y, hyJ⟩)
  have hxy_sq :
      ((((e x : ACompletion) • (⟨e y, hyJ⟩ : J)) : J) : ACompletion) ∈ J ^ 2 := by
    -- Proof comment: vanishing of a cotangent class is equivalent to membership in the square.
    exact (Ideal.toCotangent_eq_zero J ((e x : ACompletion) • (⟨e y, hyJ⟩ : J))).1 hxy_toCot_zero
  have hpull_sq :
      ((((x : AhCompletion) • y : Jh) : AhCompletion)) ∈ Jh ^ 2 := by
    -- Proof comment: contract the square-membership statement back along the common completion
    -- equivalence.
    have hmem_comap :
        ((((x : AhCompletion) • y : Jh) : AhCompletion)) ∈ Ideal.comap e.toRingHom (J ^ 2) := by
      change e ((((x : AhCompletion) • y : Jh) : AhCompletion)) ∈ J ^ 2
      simpa using hxy_sq
    rw [hcomapJh_sq] at hmem_comap
    exact hmem_comap
  exact (Ideal.toCotangent_eq_zero Jh ((x : AhCompletion) • y)).2 hpull_sq

/-- Helper for Lemma 15.109.5: after transporting the branch kernel to the `Ah`-side, a power of
the closed point of `AhCompletion` annihilates its cotangent module. -/
lemma henselization_completion_branch_kernel_cotangent_annihilated_by_closed_point_power
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    ∃ c : ℕ,
      maximalIdeal AhCompletion ^ c ≤
        Module.annihilator AhCompletion
          (henselization_completion_branch_kernel (A := A) (Ah := Ah) q).Cotangent := by
  -- Proof comment: first get the source-side annihilator power for the completion branch kernel.
  obtain ⟨c, hc⟩ :=
    completion_branch_kernel_cotangent_annihilated_by_closed_point_power
      (A := A) q hdim
  refine ⟨c, ?_⟩
  -- Proof comment: then transport that annihilator bound back across the common completion
  -- equivalence.
  exact
    henselization_completion_branch_kernel_cotangent_transport
      (A := A) (Ah := Ah) q hc

/-- Helper for Lemma 15.109.5: Lemma `15.109.4` over `Ah` algebraizes the completed branch
quotient once the transported cotangent-annihilator hypothesis is in place. -/
lemma exists_finiteType_henselization_model_of_completion_branch_kernel
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra Ah D) (_ : Algebra.FiniteType Ah D),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap Ah D) (maximalIdeal Ah)) D ≃ₐ[Ah]
          (ACompletion ⧸ completion_branch_kernel (A := A) q)) := by
  -- First transport the cotangent-annihilator bound to the canonical quotient by `Jh`.
  obtain ⟨c, hc⟩ :=
    henselization_completion_branch_kernel_cotangent_annihilated_by_closed_point_power
      (A := A) (Ah := Ah) q hdim
  have hmap_pow :
      Ideal.map (algebraMap Ah AhCompletion) (maximalIdeal Ah ^ c) =
        maximalIdeal AhCompletion ^ c := by
    -- The common completion identifies the closed points of `Ah` and `A`.
    rw [Ideal.map_pow, henselization_completionComparison_map_maximalIdeal (A := A) (Ah := Ah)]
  have hker :
      Ideal.map (algebraMap Ah AhCompletion) (maximalIdeal Ah ^ c) ≤
        Module.annihilator AhCompletion
          (RingHom.ker
            (Ideal.Quotient.mkₐ Ah
              (henselization_completion_branch_kernel (A := A) (Ah := Ah) q))).Cotangent := by
    -- For the canonical quotient map, the kernel is definitionally the transported branch ideal.
    simpa [hmap_pow, Ideal.Quotient.mkₐ_eq_mk AhCompletion, Ideal.mk_ker] using hc
  -- Now Lemma `15.109.4` applies directly to the canonical quotient map `AhCompletion → AhCompletion / Jh`.
  obtain ⟨D, instD, algD, finiteD, hD⟩ :=
    exists_finiteType_algebra_with_completion_algEquiv_of_kernelCotangent_annihilated
      (A := Ah) (B := Ah)
      (C := AhCompletion ⧸ henselization_completion_branch_kernel (A := A) (Ah := Ah) q)
      (I := maximalIdeal Ah)
      (φ := Ideal.Quotient.mkₐ Ah
        (henselization_completion_branch_kernel (A := A) (Ah := Ah) q))
      (hφ := Ideal.Quotient.mkₐ_surjective Ah
        (henselization_completion_branch_kernel (A := A) (Ah := Ah) q))
      c hker
  refine ⟨D, instD, algD, finiteD, ?_⟩
  rcases hD with ⟨e⟩
  -- Compose the algebraized `AhCompletion / Jh` model with the quotient comparison back to
  -- `ACompletion / J`.
  exact ⟨e.trans
    (henselization_completion_branch_kernel_quotient_equiv (A := A) (Ah := Ah) q)⟩

/-- Helper for Lemma 15.109.5: once the finite type `Ah`-model has the same closed fiber as `Ah`,
the henselian source argument shows that the model is already a quotient `Ah ⧸ I`. -/
lemma finiteType_henselization_model_is_quotient
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1)
    {D : Type u} [CommRing D] [Algebra Ah D] [Algebra.FiniteType Ah D]
    (hD :
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap Ah D) (maximalIdeal Ah)) D ≃ₐ[Ah]
          (ACompletion ⧸ completion_branch_kernel (A := A) q))) :
    ∃ I : Ideal Ah, Nonempty (D ≃ₐ[Ah] Ah ⧸ I) := by
  -- Route correction: after Lemma `15.109.4`, the source proof does not compare ideals
  -- immediately. It first computes the closed fiber of the finite type `Ah`-model, proves that
  -- `Ah → D` is unramified at the closed point, and only then uses the henselian lifting step to
  -- identify `D` with a quotient of `Ah`.
  --
  -- TODO: compute the closed fiber of `D` from `hD`, invoke the unramified-at-the-closed-point
  -- criterion, pass to a standard étale neighborhood, and use the henselian residue-field lifting
  -- theorem to retract that neighborhood back to `Ah`.
  let _ := q
  let _ := hdim
  let _ := hD
  sorry

/-- Helper for Lemma 15.109.5: the source-faithful algebraization and henselian descent should
produce an ideal of the henselization whose extension is the branch kernel and whose radical is
the contracted completed branch. -/
lemma exists_henselization_ideal_of_completion_branch_kernel
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    ∃ I : Ideal Ah,
      completion_branch_kernel (A := A) q =
        Ideal.map (henselizationCompletionComparison A Ah) I ∧
      Ideal.radical I =
        contracted_completion_minimalPrime (A := A) (Ah := Ah) q := by
  -- Route correction: the unresolved source step is no longer the final primality claim itself.
  -- The exact remaining task is to algebraize `ACompletion ⧸ J` via Lemma `15.109.4`, descend
  -- the resulting finite-type `Ah`-algebra to a quotient `Ah ⧸ I`, and then compare completions
  -- to identify `J = I ACompletion` with `√I` equal to the contracted prime.
  --
  -- TODO: after `exists_finiteType_henselization_model_of_completion_branch_kernel` and
  -- `finiteType_henselization_model_is_quotient`, compare the completion of `Ah ⧸ I` with
  -- `ACompletion ⧸ completion_branch_kernel q` via quotient-completion exactness to obtain
  -- `completion_branch_kernel q = map (henselizationCompletionComparison A Ah) I`, and then
  -- contract/radicalize to recover `Ideal.radical I = contracted_completion_minimalPrime q`.
  obtain ⟨D, instD, algD, finiteD, hD⟩ :=
    exists_finiteType_henselization_model_of_completion_branch_kernel
      (A := A) (Ah := Ah) q hdim
  let _ : CommRing D := instD
  let _ : Algebra Ah D := algD
  let _ : Algebra.FiniteType Ah D := finiteD
  obtain ⟨I, hDI⟩ :=
    finiteType_henselization_model_is_quotient
      (A := A) (Ah := Ah) q hdim (D := D) hD
  let _ := hDI
  sorry

/-- Helper for Lemma 15.109.5: once the radical of the extended contracted prime is known to be
prime, the chosen completion minimal prime is exactly that radical. -/
lemma completion_minimalPrime_eq_radical_map_of_radical_prime
    (q : minimalPrimes ACompletion)
    (hprime :
      (Ideal.radical
        (Ideal.map (henselizationCompletionComparison A Ah)
          (contracted_completion_minimalPrime (A := A) (Ah := Ah) q))).IsPrime) :
    (q : Ideal ACompletion) =
      Ideal.radical
        (Ideal.map (henselizationCompletionComparison A Ah)
          (contracted_completion_minimalPrime (A := A) (Ah := Ah) q)) := by
  let qh : minimalPrimes Ah := contracted_completion_minimalPrime (A := A) (Ah := Ah) q
  let I : Ideal ACompletion := Ideal.map (algebraMap Ah ACompletion) qh
  have hprime' : (Ideal.radical I).IsPrime := by
    -- First rewrite the radical to the algebra-map form used by Lemma `15.109.2`.
    simpa [I, qh, completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using hprime
  have hfiber :
      ∃! Q : minimalPrimes ACompletion, Ideal.comap (algebraMap Ah ACompletion) Q = qh := by
    -- Primality of the radical is exactly the singleton-fiber criterion from Lemma `15.109.2`.
    exact
      (radical_map_minimal_prime_is_prime_iff_exists_unique_completion_minimal_prime
        (A := A) (Ah := Ah) qh).mp hprime'
  have hrad_mem : Ideal.radical I ∈ I.minimalPrimes := by
    -- A prime radical is itself the minimal prime over the extended ideal.
    refine ⟨⟨hprime', Ideal.le_radical⟩, ?_⟩
    intro J hJ hIJ
    calc
      Ideal.radical I ≤ J.radical := Ideal.radical_mono hJ.2
      _ = J := Ideal.radical_eq_iff.mpr hJ.1.isRadical
  let qrad : minimalPrimes ACompletion :=
    ⟨Ideal.radical I,
      completion_mem_minimalPrimes_of_mem_mapped_ideal_minimalPrimes
        (A := A) (Ah := Ah) qh hrad_mem⟩
  have hq_contraction : Ideal.comap (algebraMap Ah ACompletion) q = qh := by
    -- By construction, `qh` is exactly the contraction of `q`.
    simp [qh, contracted_completion_minimalPrime, completionComparisonAlgebra,
      RingHom.algebraMap_toAlgebra]
  have hqrad_contraction : Ideal.comap (algebraMap Ah ACompletion) qrad = qh :=
    contraction_eq_of_mem_mapped_ideal_minimalPrimes (A := A) (Ah := Ah) qh hrad_mem
  have hq_eq_qrad : q = qrad := by
    -- The singleton-fiber criterion identifies `q` with the radical branch.
    rcases hfiber with ⟨Q0, hQ0, huniq⟩
    exact (huniq q hq_contraction).trans (huniq qrad hqrad_contraction).symm
  -- Reading equality on the underlying ideals gives the desired radical identity.
  simpa [I, qh, completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
    congrArg Subtype.val hq_eq_qrad

/-- Helper for Lemma 15.109.5: the remaining source-style branch-kernel argument should prove that
the radical of the extended contracted prime is prime when the chosen completed branch has Krull
dimension `1`. -/
lemma radical_map_contracted_completion_minimalPrime_isPrime_of_dim_one
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    (Ideal.radical
      (Ideal.map (henselizationCompletionComparison A Ah)
        (contracted_completion_minimalPrime (A := A) (Ah := Ah) q))).IsPrime := by
  rcases
      exists_henselization_ideal_of_completion_branch_kernel
        (A := A) (Ah := Ah) q hdim with
    ⟨I, hbranch, hradicalI⟩
  have hradicalMap :
      Ideal.radical
        (Ideal.map (henselizationCompletionComparison A Ah)
          (contracted_completion_minimalPrime (A := A) (Ah := Ah) q)) = q.1 := by
    -- Rewrite the contracted prime as `√I`, then compare radicals after extension.
    calc
      Ideal.radical
          (Ideal.map (henselizationCompletionComparison A Ah)
            (contracted_completion_minimalPrime (A := A) (Ah := Ah) q)) =
          Ideal.radical
            (Ideal.map (henselizationCompletionComparison A Ah) (Ideal.radical I)) := by
              rw [← hradicalI]
      _ = Ideal.radical
            (Ideal.map (henselizationCompletionComparison A Ah) I) := by
              exact
                radical_map_radical_eq
                  (f := henselizationCompletionComparison A Ah) I
      _ = Ideal.radical (completion_branch_kernel (A := A) q) := by
              rw [hbranch]
      _ = q.1 := radical_completion_branch_kernel_eq_completion_minimalPrime (A := A) q
  -- The identified radical is the prime ideal `q`, so the desired primality follows immediately.
  rw [hradicalMap]
  exact Ideal.minimalPrimes_isPrime q.2

-- Proof sketch: reduce first to the henselian case using the standard identification of the
-- completions of `A` and `Ah`. Then apply Lemma `15.109.4` to the quotient of `ACompletion` by the
-- kernel of the localization map at `q`, use the one-dimensional minimal-prime hypothesis to
-- algebraize that quotient, and finally descend along the henselian local map to obtain a minimal
-- prime `qh` of `Ah` whose extension to the completion has radical `q`.
/-- Lemma 15.109.5: let `(A, 𝔪)` be a Noetherian local ring with chosen henselization `Ah`, let
`ACompletion = AdicCompletion (maximalIdeal A) A`, and let `q` be a minimal prime of
`ACompletion` such that `dim (ACompletion / q) = 1`. Then there exists a minimal prime `qh` of
`Ah` such that `q = √(qh ACompletion)`, where `qh ACompletion` is taken along the canonical
comparison map `Ah → ACompletion`. -/
theorem exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    ∃ qh : minimalPrimes Ah,
      (q : Ideal ACompletion) =
        Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) qh) := by
  let qh : minimalPrimes Ah := contracted_completion_minimalPrime (A := A) (Ah := Ah) q
  refine ⟨qh, ?_⟩
  -- Once the radical is known to be prime, the completed branch is the corresponding unique
  -- minimal prime over the contracted henselization branch.
  exact completion_minimalPrime_eq_radical_map_of_radical_prime
    (A := A) (Ah := Ah) q
    (radical_map_contracted_completion_minimalPrime_isPrime_of_dim_one
      (A := A) (Ah := Ah) q hdim)

end
