import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_66_2
import stacks_proof.stacks_project.Chap10.Lemma_10_66_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-
Domain triage:
* `source-facing`: the textbook item identifies the image of `WeakAss_S(M)` in `Spec R` under a
  finite ring map.
* `core/canonical`: the owner abstraction in this chapter is the set-valued declaration
  `weaklyAssociatedPrimes R M`.
* `bridge/view`: the only primitive module-theoretic datum needed pointwise is the annihilator
  ideal `Ideal.torsionOf _ _ m`; the set-level equality should be expressed directly in terms of
  the owner set rather than by a parallel wrapper declaration.
-/

namespace weaklyAssociatedPrimes

omit [Module.Finite R S] in
private theorem comap_torsionOf_eq (m : M) :
    Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m) = Ideal.torsionOf R M m := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/-- Helper for Chap10 Lemma 10 66 13: restricting scalars contracts the cyclic annihilator
`(⊥ : Submodule B N).colon {x}` to `(⊥ : Submodule A N).colon {x}`. -/
private theorem comap_colon_singleton_eq
    {A : Type*} {B : Type*} {N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (x : N) :
    Ideal.comap (algebraMap A B) ((⊥ : Submodule B N).colon ({x} : Set N)) =
      (⊥ : Submodule A N).colon ({x} : Set N) := by
  -- Membership on both sides is the same scalar-annihilation equation, transported through the
  -- scalar tower.
  ext a
  rw [Ideal.mem_comap]
  simp [Submodule.mem_colon, algebraMap_smul]

/-- Helper for Chap10 Lemma 10 66 13: an associated prime in the radical-annihilator sense
contracts along restriction of scalars. -/
private theorem IsAssociatedPrime.comap_restrictScalars
    {A : Type*} {B : Type*} {N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    {Q : Ideal B} (hQ : IsAssociatedPrime Q N) :
    IsAssociatedPrime (Ideal.comap (algebraMap A B) Q) N := by
  rcases hQ with ⟨hQprime, x, hx⟩
  -- Contract the radical-annihilator presentation of `Q`; radicals commute with comap, and the
  -- previous helper identifies the contracted annihilator.
  refine ⟨hQprime.comap (algebraMap A B), x, ?_⟩
  calc
    Ideal.comap (algebraMap A B) Q =
        Ideal.comap (algebraMap A B) (((⊥ : Submodule B N).colon ({x} : Set N)).radical) := by
          rw [hx]
    _ = (Ideal.comap (algebraMap A B) ((⊥ : Submodule B N).colon ({x} : Set N))).radical := by
          rw [Ideal.comap_radical]
    _ = ((⊥ : Submodule A N).colon ({x} : Set N)).radical := by
          rw [comap_colon_singleton_eq]

/-- Helper for Chap10 Lemma 10 66 13: multiplying a cyclic generator by a unit does not change
the radical of its annihilator. -/
private theorem radical_colon_unit_smul_eq
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    {u : A} (hu : IsUnit u) (x : N) :
    ((⊥ : Submodule A N).colon ({u • x} : Set N)).radical =
      ((⊥ : Submodule A N).colon ({x} : Set N)).radical := by
  -- Compare radical membership by raising a scalar to a power and cancelling the unit action.
  apply le_antisymm
  · intro a ha
    rw [Ideal.mem_radical_iff] at ha ⊢
    rcases ha with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [Submodule.mem_colon] at hn ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hmem : u • x ∈ ({u • x} : Set N) := by
      simp
    have hzero : a ^ n • (u • x) = 0 := by
      simpa [Submodule.mem_bot] using hn (u • x) hmem
    have hzero' : u • (a ^ n • x) = 0 := by
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hzero
    exact hu.smul_eq_zero.mp hzero'
  · intro a ha
    rw [Ideal.mem_radical_iff] at ha ⊢
    rcases ha with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [Submodule.mem_colon] at hn ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hmem : x ∈ ({x} : Set N) := by
      simp
    have hzero : a ^ n • x = 0 := by
      simpa [Submodule.mem_bot] using hn x hmem
    have hzero' : u • (a ^ n • x) = 0 := hu.smul_eq_zero.mpr hzero
    simpa [Submodule.mem_bot, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hzero'

/-- Helper for Chap10 Lemma 10 66 13: an associated maximal ideal after localization has a
radical-annihilator witness with denominator `1`. -/
private theorem associatedPrime_maximalIdeal_atPrime_has_mk_one_witness
    {𝔮 : Ideal S} [𝔮.IsPrime]
    (hassoc :
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))
        (LocalizedModule.AtPrime 𝔮 M)) :
    ∃ m : M,
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) =
        ((⊥ : Submodule (Localization.AtPrime 𝔮) (LocalizedModule.AtPrime 𝔮 M)).colon
          ({LocalizedModule.mk m (1 : 𝔮.primeCompl)} :
            Set (LocalizedModule.AtPrime 𝔮 M))).radical := by
  -- Choose a localization representative and then remove its denominator by unit scaling.
  rcases hassoc with ⟨_, x, hx⟩
  obtain ⟨⟨m, s⟩, hxmk⟩ :=
    IsLocalizedModule.mk'_surjective 𝔮.primeCompl
      (LocalizedModule.mkLinearMap 𝔮.primeCompl M) x
  refine ⟨m, ?_⟩
  have hunit : IsUnit (Localization.mk (1 : S) s : Localization.AtPrime 𝔮) := by
    have hmkUnit : IsUnit (IsLocalization.mk' (Localization.AtPrime 𝔮) (1 : S) s) :=
      isUnit_of_invertible _
    simpa [Localization.mk_eq_mk'] using hmkUnit
  have hmk :
      LocalizedModule.mk m s =
        (Localization.mk (1 : S) s : Localization.AtPrime 𝔮) •
          LocalizedModule.mk m (1 : 𝔮.primeCompl) := by
    simpa using (LocalizedModule.mk_smul_mk (1 : S) m s (1 : 𝔮.primeCompl)).symm
  have hx' :
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) =
        ((⊥ : Submodule (Localization.AtPrime 𝔮) (LocalizedModule.AtPrime 𝔮 M)).colon
          ({LocalizedModule.mk m s} : Set (LocalizedModule.AtPrime 𝔮 M))).radical := by
    rw [← hxmk] at hx
    simpa [IsLocalizedModule.mk_eq_mk'] using hx
  calc
    IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) =
        ((⊥ : Submodule (Localization.AtPrime 𝔮) (LocalizedModule.AtPrime 𝔮 M)).colon
          ({LocalizedModule.mk m s} : Set (LocalizedModule.AtPrime 𝔮 M))).radical := hx'
    _ = ((⊥ : Submodule (Localization.AtPrime 𝔮) (LocalizedModule.AtPrime 𝔮 M)).colon
          ({(Localization.mk (1 : S) s : Localization.AtPrime 𝔮) •
            LocalizedModule.mk m (1 : 𝔮.primeCompl)} :
            Set (LocalizedModule.AtPrime 𝔮 M))).radical := by
          rw [hmk]
    _ = ((⊥ : Submodule (Localization.AtPrime 𝔮) (LocalizedModule.AtPrime 𝔮 M)).colon
          ({LocalizedModule.mk m (1 : 𝔮.primeCompl)} :
            Set (LocalizedModule.AtPrime 𝔮 M))).radical := by
          exact radical_colon_unit_smul_eq hunit (LocalizedModule.mk m (1 : 𝔮.primeCompl))

/-- Helper for Chap10 Lemma 10 66 13: if a scalar lies in a minimal prime over a cyclic
annihilator, then a power of it kills the generator after multiplying by a denominator outside
that prime. -/
private theorem exists_not_mem_mul_pow_smul_eq_zero_of_mem_minimalPrimes
    {𝔮 : Ideal S} [𝔮.IsPrime] {m : M} {x : S}
    (hmin : 𝔮 ∈ (Ideal.torsionOf S M m).minimalPrimes) (hx : x ∈ 𝔮) :
    ∃ y : S, y ∉ 𝔮 ∧ ∃ n : ℕ, (y * x ^ n) • m = 0 := by
  let S𝔮 := Localization.AtPrime 𝔮
  -- Localizing the minimal-prime witness identifies the radical of the localized annihilator with
  -- the maximal ideal of `S_q`.
  have hrad :
      (Ideal.map (algebraMap S S𝔮) (Ideal.torsionOf S M m)).radical =
        IsLocalRing.maximalIdeal S𝔮 := by
    simpa [S𝔮, Localization.AtPrime.map_eq_maximalIdeal] using
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes S𝔮 𝔮
        (Ideal.torsionOf S M m) hmin
  have hxloc :
      algebraMap S S𝔮 x ∈
        (Ideal.map (algebraMap S S𝔮) (Ideal.torsionOf S M m)).radical := by
    rw [hrad, ← Localization.AtPrime.map_eq_maximalIdeal (R := S) (I := 𝔮)]
    exact Ideal.mem_map_of_mem (algebraMap S S𝔮) hx
  -- Unpack radical membership in the localization and clear the localization denominator.
  rw [Ideal.mem_radical_iff] at hxloc
  rcases hxloc with ⟨n, hn⟩
  rw [← map_pow] at hn
  rcases (IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔮.primeCompl
      (Localization.AtPrime 𝔮) (Ideal.torsionOf S M m) (x ^ n)).mp hn with
    ⟨y, hyq, hy⟩
  refine ⟨y, hyq, n, ?_⟩
  rw [Ideal.mem_torsionOf_iff] at hy
  simpa [mul_comm, mul_left_comm, mul_assoc] using hy

omit [Module.Finite R S] in
/-- Helper for Chap10 Lemma 10 66 13: the local map between prime localizations contracts the
maximal ideal upstairs to the maximal ideal downstairs. -/
private theorem comap_maximalIdeal_localRingHom_atPrime
    {𝔭 : Ideal R} {𝔮 : Ideal S} [𝔭.IsPrime] [𝔮.IsPrime] [𝔮.LiesOver 𝔭] :
    Ideal.comap (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮))
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by
  -- The algebra map between the two localizations is the canonical local ring hom, so its
  -- maximal-ideal comap is exactly the local-hom criterion.
  let f : Localization.AtPrime 𝔭 →+* Localization.AtPrime 𝔮 :=
    Localization.localRingHom 𝔭 𝔮 (algebraMap R S) Ideal.LiesOver.over
  have hf : IsLocalHom f :=
    Localization.isLocalHom_localRingHom 𝔭 𝔮 (algebraMap R S) Ideal.LiesOver.over
  have hmax :
      Ideal.comap f (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by
    exact IsLocalRing.maximalIdeal_comap f
  simpa [f, RingHom.algebraMap_toAlgebra] using hmax

/-- Helper for Chap10 Lemma 10 66 13: in the finite fiber over a prime, one can choose an element
of a given prime avoiding all other primes in the same fiber. -/
private theorem exists_mem_prime_avoid_primesOver_ne
    {𝔭 : Ideal R} {𝔮 : Ideal S} [𝔭.IsPrime] [𝔮.IsPrime] [𝔮.LiesOver 𝔭] :
    ∃ x : S, x ∈ 𝔮 ∧
      ∀ 𝔮' : Ideal S, 𝔮'.IsPrime → 𝔮'.LiesOver 𝔭 → 𝔮' ≠ 𝔮 → x ∉ 𝔮' := by
  classical
  let t : Set (Ideal S) := {𝔮' | 𝔮'.IsPrime ∧ 𝔮'.LiesOver 𝔭 ∧ 𝔮' ≠ 𝔮}
  have ht : t.Finite := by
    -- The finite-algebra hypothesis gives a finite set of primes over `𝔭`; `t` is the subfamily
    -- obtained by removing the distinguished prime.
    exact (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) 𝔭).subset
      (by
        intro 𝔮' h𝔮'
        exact ⟨h𝔮'.1, h𝔮'.2.1⟩)
  have hnot_le_of_mem_t : ∀ ⦃𝔮' : Ideal S⦄, 𝔮' ∈ t → ¬ 𝔮 ≤ 𝔮' := by
    intro 𝔮' h𝔮' hle
    letI : 𝔮'.IsPrime := h𝔮'.1
    letI : 𝔮'.LiesOver 𝔭 := h𝔮'.2.1
    have hlt : 𝔮 < 𝔮' := lt_of_le_of_ne hle (fun h ↦ h𝔮'.2.2 h.symm)
    obtain ⟨x, hx𝔮', hx𝔮⟩ := SetLike.exists_of_lt hlt
    -- Integral incomparability makes a strict containment of primes in one fiber impossible.
    have hcomap_lt :
        Ideal.comap (algebraMap R S) 𝔮 < Ideal.comap (algebraMap R S) 𝔮' :=
      Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) (S := S)
        (I := 𝔮) (J := 𝔮') hle ⟨hx𝔮', hx𝔮⟩
        (Algebra.IsIntegral.isIntegral x)
    have h𝔮_comap : Ideal.comap (algebraMap R S) 𝔮 = 𝔭 :=
      (Ideal.LiesOver.over (P := 𝔮) (p := 𝔭)).symm
    have h𝔮'_comap : Ideal.comap (algebraMap R S) 𝔮' = 𝔭 :=
      (Ideal.LiesOver.over (P := 𝔮') (p := 𝔭)).symm
    rw [h𝔮_comap, h𝔮'_comap] at hcomap_lt
    exact (lt_irrefl 𝔭) hcomap_lt
  have hnot_subset : ¬ (𝔮 : Set S) ⊆ ⋃ 𝔮' ∈ t, (𝔮' : Set S) := by
    intro hsubset
    have hcovered :
        ∃ 𝔮' ∈ t, 𝔮 ≤ 𝔮' := by
      exact (Ideal.subset_union_prime_finite (s := t) (f := fun 𝔮' : Ideal S ↦ 𝔮')
        (a := 𝔮) (b := 𝔮) ht
        (by
          intro 𝔮' h𝔮' _ _
          exact h𝔮'.1)
        (I := 𝔮)).mp hsubset
    rcases hcovered with ⟨𝔮', h𝔮', hle⟩
    exact hnot_le_of_mem_t h𝔮' hle
  obtain ⟨x, hx𝔮, hxnot⟩ := Set.not_subset.mp hnot_subset
  refine ⟨x, hx𝔮, ?_⟩
  intro 𝔮' h𝔮'_prime h𝔮'_lie h𝔮'_ne hx𝔮'
  exact hxnot <| Set.mem_iUnion₂.mpr
    ⟨𝔮', ⟨h𝔮'_prime, h𝔮'_lie, h𝔮'_ne⟩, hx𝔮'⟩

/-- Helper for Chap10 Lemma 10 66 13: multiplying a cyclic witness by a scalar outside a
minimal annihilator prime preserves that minimal annihilator prime. -/
private theorem mem_minimalPrimes_torsionOf_smul_of_not_mem
    {𝔮 : Ideal S} [𝔮.IsPrime] {m : M} {y : S}
    (hmin : 𝔮 ∈ (Ideal.torsionOf S M m).minimalPrimes) (hy : y ∉ 𝔮) :
    𝔮 ∈ (Ideal.torsionOf S M (y • m)).minimalPrimes := by
  -- First show that the new annihilator is still contained in `𝔮`, using primality and `y ∉ 𝔮`.
  have hqprime : 𝔮.IsPrime := inferInstance
  refine ⟨⟨hqprime, ?_⟩, ?_⟩
  · intro a ha
    rw [Ideal.mem_torsionOf_iff] at ha
    have hay : a * y ∈ Ideal.torsionOf S M m := by
      rw [Ideal.mem_torsionOf_iff]
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using ha
    have hayq : a * y ∈ 𝔮 := hmin.1.2 hay
    exact hqprime.mem_or_mem hayq |>.resolve_right hy
  · intro 𝔮' h𝔮' hle
    -- Any prime below `𝔮` containing the new annihilator also contains the old annihilator.
    apply hmin.2
    · refine ⟨h𝔮'.1, ?_⟩
      intro a ha
      apply h𝔮'.2
      rw [Ideal.mem_torsionOf_iff] at ha ⊢
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using congrArg (fun z : M ↦ y • z) ha
    · exact hle

/-- Helper for Chap10 Lemma 10 66 13: a clearing equation puts the separator into the radical of
the annihilator of the multiplied witness. -/
private theorem mem_radical_torsionOf_smul_of_mul_pow_smul_eq_zero
    {m : M} {x y : S} {n : ℕ} (hkill : (y * x ^ n) • m = 0) :
    x ∈ (Ideal.torsionOf S M (y • m)).radical := by
  -- The same exponent witnesses radical membership after commuting the two scalar factors.
  rw [Ideal.mem_radical_iff]
  refine ⟨n, ?_⟩
  rw [Ideal.mem_torsionOf_iff]
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hkill

/-- Helper for Chap10 Lemma 10 66 13: a minimal prime upstairs contracts to a minimal prime
downstairs when a separator in its radical excludes the other primes in the fiber. -/
private theorem comap_mem_minimalPrimes_of_fiber_separator
    {𝔭 : Ideal R} {𝔮 : Ideal S} [𝔭.IsPrime] [𝔮.IsPrime] [𝔮.LiesOver 𝔭]
    {J : Ideal S} {x : S} (hqmin : 𝔮 ∈ J.minimalPrimes) (hxrad : x ∈ J.radical)
    (havoid :
      ∀ 𝔮' : Ideal S, 𝔮'.IsPrime → 𝔮'.LiesOver 𝔭 → 𝔮' ≠ 𝔮 → x ∉ 𝔮') :
    𝔭 ∈ (Ideal.comap (algebraMap R S) J).minimalPrimes := by
  -- The contraction contains the contracted ideal because `J ≤ 𝔮` and `𝔮` lies over `𝔭`.
  have hpprime : 𝔭.IsPrime := inferInstance
  refine ⟨⟨hpprime, ?_⟩, ?_⟩
  · calc
      Ideal.comap (algebraMap R S) J ≤ Ideal.comap (algebraMap R S) 𝔮 :=
        Ideal.comap_mono hqmin.1.2
      _ = 𝔭 := by
        simpa [Ideal.under_def] using (Ideal.LiesOver.over (P := 𝔮) (p := 𝔭)).symm
  · intro 𝔭' h𝔭' h𝔭'p
    letI : 𝔭'.IsPrime := h𝔭'.1
    -- Reduce an arbitrary prime below `𝔭` to a minimal prime over the contracted ideal.
    obtain ⟨𝔭₀, h𝔭₀min, h𝔭₀𝔭'⟩ :=
      Ideal.exists_minimalPrimes_le (I := Ideal.comap (algebraMap R S) J) (J := 𝔭') h𝔭'.2
    obtain ⟨𝔮₀, h𝔮₀min, h𝔮₀comap⟩ :=
      Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) 𝔭₀ h𝔭₀min
    letI : 𝔮₀.IsPrime := Ideal.minimalPrimes_isPrime h𝔮₀min
    have h𝔭₀𝔭 : 𝔭₀ ≤ 𝔭 := h𝔭₀𝔭'.trans h𝔭'p
    have h𝔮₀𝔭 : Ideal.comap (algebraMap R S) 𝔮₀ ≤ 𝔭 := by
      rw [h𝔮₀comap]
      exact h𝔭₀𝔭
    -- Going-up lifts the inclusion `𝔭₀ ≤ 𝔭` to a prime over `𝔭` above `𝔮₀`.
    obtain ⟨𝔮₁, h𝔮₀𝔮₁, h𝔮₁prime, h𝔮₁comap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
        (R := R) (S := S) (I := 𝔮₀) (P := 𝔭) h𝔮₀𝔭
    have h𝔮₁over : 𝔭 = Ideal.under R 𝔮₁ := by
      simpa [Ideal.under_def] using h𝔮₁comap.symm
    have h𝔮₁lie : 𝔮₁.LiesOver 𝔭 := ⟨h𝔮₁over⟩
    have hx𝔮₁ : x ∈ 𝔮₁ := by
      exact (h𝔮₁prime.radical_le_iff.mpr (h𝔮₀min.1.2.trans h𝔮₀𝔮₁)) hxrad
    have h𝔮₁eq : 𝔮₁ = 𝔮 := by
      by_contra hne
      exact havoid 𝔮₁ h𝔮₁prime h𝔮₁lie hne hx𝔮₁
    have h𝔮₀eq : 𝔮₀ = 𝔮 := by
      -- Minimality of `𝔮` over `J` identifies the lower minimal prime with `𝔮`.
      exact le_antisymm (h𝔮₀𝔮₁.trans_eq h𝔮₁eq) (hqmin.2 h𝔮₀min.1 (h𝔮₀𝔮₁.trans_eq h𝔮₁eq))
    have h𝔭₀eq : 𝔭₀ = 𝔭 := by
      calc
        𝔭₀ = Ideal.comap (algebraMap R S) 𝔮₀ := h𝔮₀comap.symm
        _ = Ideal.comap (algebraMap R S) 𝔮 := by rw [h𝔮₀eq]
        _ = 𝔭 := by
          simpa [Ideal.under_def] using (Ideal.LiesOver.over (P := 𝔮) (p := 𝔭)).symm
    simpa [h𝔭₀eq] using h𝔭₀𝔭'

/-- Helper for Chap10 Lemma 10 66 13: a minimal annihilator prime upstairs descends across a
finite map to association at the localized contracted prime. -/
private theorem isAssociatedPrime_maximalIdeal_atPrime_of_mem_minimalPrimes_finite
    {𝔭 : Ideal R} {𝔮 : Ideal S} [𝔭.IsPrime] [𝔮.IsPrime]
    (h𝔭𝔮 : 𝔭 = Ideal.comap (algebraMap R S) 𝔮) {m : M}
    (hmin : 𝔮 ∈ (Ideal.torsionOf S M m).minimalPrimes) :
    IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭))
      (LocalizedModule.AtPrime 𝔭 M) := by
  -- Route correction: avoid the earlier semilocal zero-detection blocker by proving weak
  -- association downstairs as a contracted minimal-prime statement before applying Lemma 10.66.2.
  have h𝔮over : 𝔭 = Ideal.under R 𝔮 := by
    simpa [Ideal.under_def] using h𝔭𝔮
  have hlie : 𝔮.LiesOver 𝔭 := ⟨h𝔮over⟩
  letI : 𝔮.LiesOver 𝔭 := hlie
  obtain ⟨x, hx𝔮, havoid⟩ :=
    exists_mem_prime_avoid_primesOver_ne (R := R) (S := S) (𝔭 := 𝔭) (𝔮 := 𝔮)
  obtain ⟨y, hy𝔮, n, hkill⟩ :=
    exists_not_mem_mul_pow_smul_eq_zero_of_mem_minimalPrimes hmin hx𝔮
  have hqmin_y :
      𝔮 ∈ (Ideal.torsionOf S M (y • m)).minimalPrimes :=
    mem_minimalPrimes_torsionOf_smul_of_not_mem hmin hy𝔮
  have hxrad :
      x ∈ (Ideal.torsionOf S M (y • m)).radical :=
    mem_radical_torsionOf_smul_of_mul_pow_smul_eq_zero hkill
  have hpmin_comap :
      𝔭 ∈
        (Ideal.comap (algebraMap R S) (Ideal.torsionOf S M (y • m))).minimalPrimes :=
    comap_mem_minimalPrimes_of_fiber_separator
      (R := R) (S := S) (𝔭 := 𝔭) (𝔮 := 𝔮) hqmin_y hxrad havoid
  have hpweak : Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
    refine ⟨y • m, ?_⟩
    simpa [comap_torsionOf_eq (R := R) (S := S) (M := M) (y • m)] using hpmin_comap
  exact
    (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
      (R := R) (M := M) 𝔭).mp hpweak

/-- Helper for Chap10 Lemma 10 66 13: for a finite ring map, association of the maximal ideal
after localizing at a prime of `S` descends to association at its contracted prime of `R`. -/
private theorem isAssociatedPrime_maximalIdeal_of_finite_localizationAtPrime
    {𝔭 : Ideal R} {𝔮 : Ideal S} [𝔭.IsPrime] [𝔮.IsPrime]
    (h𝔭𝔮 : 𝔭 = Ideal.comap (algebraMap R S) 𝔮)
    (hassoc :
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))
        (LocalizedModule.AtPrime 𝔮 M)) :
    IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭))
      (LocalizedModule.AtPrime 𝔭 M) := by
  -- Route correction: the fixed `mk m 1` descent only gives a witness in `M_𝔮` and repeatedly
  -- leaves a denominator-clearing comparison with `M_𝔭`. Instead recover the global minimal-prime
  -- witness over `S` and defer exactly the finite semilocal descent used in the source proof.
  have hweak : Ideal.IsWeaklyAssociatedToModule S M 𝔮 :=
    (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
      (R := S) (M := M) 𝔮).mpr hassoc
  rcases hweak with ⟨m, hmin⟩
  exact isAssociatedPrime_maximalIdeal_atPrime_of_mem_minimalPrimes_finite
    (R := R) (S := S) (M := M) (𝔭 := 𝔭) (𝔮 := 𝔮) h𝔭𝔮 hmin

/-- Helper for Chap10 Lemma 10 66 13: a weakly associated prime of `M` over `S` contracts to a
weakly associated prime over `R` for a finite ring map. -/
private theorem comap_mem_weaklyAssociatedPrimes_of_mem
    {𝔮 : Ideal S} (h𝔮 : 𝔮 ∈ weaklyAssociatedPrimes S M) :
    Ideal.comap (algebraMap R S) 𝔮 ∈ weaklyAssociatedPrimes R M := by
  -- Route correction: the earlier minimal-prime contraction route is false even for finite
  -- injective maps (for example `A → A × A ⧸ (x)`). The correct route localizes at the
  -- contraction, turns weak association into association by Lemma 10.66.2, contracts the
  -- associated prime along the local map, and then clears the finite-algebra localization.
  -- First turn weak association at `𝔮` into ordinary association after localizing at `𝔮`.
  let 𝔭 : Ideal R := Ideal.comap (algebraMap R S) 𝔮
  have h𝔮prime : 𝔮.IsPrime :=
    h𝔮.isPrime
  have h𝔭prime : 𝔭.IsPrime := h𝔮prime.comap (algebraMap R S)
  letI : 𝔮.IsPrime := h𝔮prime
  letI : 𝔭.IsPrime := h𝔭prime
  have h𝔮assoc :
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))
        (LocalizedModule.AtPrime 𝔮 M) :=
    (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
      (R := S) (M := M) 𝔮).mp h𝔮
  -- Descend association across the finite local map and return through the localization criterion.
  have h𝔭assoc :
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭))
        (LocalizedModule.AtPrime 𝔭 M) :=
    isAssociatedPrime_maximalIdeal_of_finite_localizationAtPrime
      (R := R) (S := S) (M := M) (𝔭 := 𝔭) (𝔮 := 𝔮) rfl h𝔮assoc
  have h𝔭weak : 𝔭 ∈ weaklyAssociatedPrimes R M :=
    (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
      (R := R) (M := M) 𝔭).mpr h𝔭assoc
  simpa [𝔭] using h𝔭weak

/-- Chap10 Lemma 10 66 13: let `f : Spec S → Spec R` be induced by `algebraMap R S`. If `R → S` is a
finite ring map, then the image of the weakly associated primes of `M` over `S` under `f` is
exactly the weakly associated primes of `M` over `R`. -/
-- Proof sketch: the inclusion `weaklyAssociatedPrimes R M ⊆ Ideal.comap (algebraMap R S) ''
-- weaklyAssociatedPrimes S M` is the restriction-of-scalars inclusion proved earlier. For the
-- reverse inclusion, start with `𝔮 ∈ weaklyAssociatedPrimes S M`, choose an element of `M` whose
-- annihilator has `𝔮` as a minimal prime, and use finiteness of `R → S`, prime avoidance, and the
-- semilocal structure of `S` over the contraction `𝔭` to produce an element whose annihilator over
-- `R` has `𝔭` as a minimal prime.
@[stacks 05E1]
theorem restrictScalars_eq_image_comap_of_finite :
    Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M =
      weaklyAssociatedPrimes R M := by
  -- The earlier item already proves the inclusion from `R` to the image from `S`.
  refine Set.Subset.antisymm ?_ subset_comap_image
  rintro 𝔭 ⟨𝔮, h𝔮, rfl⟩
  -- For the reverse inclusion, contract a weakly associated prime witness along the finite map.
  exact comap_mem_weaklyAssociatedPrimes_of_mem (R := R) (S := S) (M := M) h𝔮

end weaklyAssociatedPrimes

end
