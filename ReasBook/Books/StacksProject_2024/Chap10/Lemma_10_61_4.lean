import Mathlib
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_35_5
import StacksProject_2024.Chap10.Lemma_10_35_6
import StacksProject_2024.Chap10.Lemma_10_61_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Classical

universe u

/-
Domain sampling:
* primary domain: commutative algebra of `Spec R`, `MaxSpec R`, Jacobson rings, and Krull
  dimension in the Noetherian setting;
* owner declarations inspected in this domain:
  - `isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum`
  - `exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing`
  - `infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim`
  - `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`;
* best owner abstraction: `IsJacobsonRing R`, with `Ring.DimensionLEOne` as the canonical
  dimension-one owner and quotient/localization spectrum identifications as bridge/view API;
* primitive vs. derived: the source-facing inputs are infinitude of prime ideals and the primewise
  maximal-or-infinite-over condition, while the comparison between `PrimeSpectrum R` and
  `MaximalSpectrum R` in dimension one is derived API and stays private.
-/

section

variable {R : Type u} [CommRing R] [Ring.DimensionLEOne R]

private theorem finite_primeSpectrum_of_finite_maximalSpectrum
    [Finite (MaximalSpectrum R)] :
    Finite (PrimeSpectrum R) := by
  classical
  let s : Set (Ideal R) := {(⊥ : Ideal R)} ∪ Set.range MaximalSpectrum.asIdeal
  have hs : s.Finite :=
    (Set.finite_singleton (⊥ : Ideal R)).union (Set.finite_range MaximalSpectrum.asIdeal)
  letI : Fintype s := hs.fintype
  let f : PrimeSpectrum R → s := fun x ↦ by
    refine ⟨x.asIdeal, ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · exact Or.inl hx
    · exact Or.inr
        ⟨⟨x.asIdeal, x.isPrime.isMaximal hx⟩, rfl⟩
  exact Finite.of_injective f fun x y hxy ↦
    PrimeSpectrum.ext <| by simpa using congrArg Subtype.val hxy

private theorem infinite_maximalSpectrum_of_infinite_primeSpectrum
    [Infinite (PrimeSpectrum R)] : Infinite (MaximalSpectrum R) := by
  by_contra h
  haveI : Finite (MaximalSpectrum R) := not_infinite_iff_finite.mp h
  haveI : Finite (PrimeSpectrum R) := finite_primeSpectrum_of_finite_maximalSpectrum
  exact Finite.false (inferInstance : Finite (PrimeSpectrum R))

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Helper for Lemma 10.61.4: quotienting by a prime ideal transports the Stacks obstruction
`V(p) ∩ D(f) = {p}` to the singleton generic basic open on `Spec (R / p)`. -/
lemma basicOpen_quotient_eq_singleton_bot_of_zeroLocus_inter_basicOpen_eq_singleton
    (p : PrimeSpectrum R) (f : R)
    (hp :
      PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) ∩
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) = {p}) :
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk p.asIdeal f) :
        Set (PrimeSpectrum (R ⧸ p.asIdeal))) =
      ({(⊥ : PrimeSpectrum (R ⧸ p.asIdeal))} : Set (PrimeSpectrum (R ⧸ p.asIdeal))) := by
  let e := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal
  have hpV : p ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) := by
    exact (PrimeSpectrum.mem_zeroLocus p (p.asIdeal : Set R)).2 le_rfl
  have hbot_image : e (⊥ : PrimeSpectrum (R ⧸ p.asIdeal)) = ⟨p, hpV⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    -- The generic point of `Spec (R / p)` contracts to `p`.
    change Ideal.comap (Ideal.Quotient.mk p.asIdeal) (⊥ : Ideal (R ⧸ p.asIdeal)) = p.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  ext x
  constructor
  · intro hx
    have hxVD :
        (e x).1 ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) ∩
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      refine ⟨(e x).2, ?_⟩
      exact (PrimeSpectrum.mem_basicOpen f (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) x)).2
        (by
          simpa [Ideal.mem_comap] using
            (PrimeSpectrum.mem_basicOpen (Ideal.Quotient.mk p.asIdeal f) x).1 hx)
    have hx_singleton : (e x).1 ∈ ({p} : Set (PrimeSpectrum R)) := by
      rw [← hp]
      exact hxVD
    have hx_image : e x = ⟨p, hpV⟩ := by
      apply Subtype.ext
      simpa using hx_singleton
    refine Set.mem_singleton_iff.mpr ?_
    exact e.injective (hx_image.trans hbot_image.symm)
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hp_basic : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      have hp_mem :
          p ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) ∩
            (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
        rw [hp]
        simp
      exact hp_mem.2
    -- The generic point of `Spec (R / p)` still avoids the image of `f`.
    refine (PrimeSpectrum.mem_basicOpen (Ideal.Quotient.mk p.asIdeal f)
      (⊥ : PrimeSpectrum (R ⧸ p.asIdeal))).2 ?_
    simpa [Ideal.Quotient.eq_zero_iff_mem] using
      (PrimeSpectrum.mem_basicOpen f p).1 hp_basic

/-- Helper for Lemma 10.61.4: once a basic open is the singleton generic point in a domain, the
same remains true after localizing at any prime. -/
lemma basicOpen_localizationAtPrime_eq_singleton_bot_of_basicOpen_eq_singleton_bot
    {A : Type u} [CommRing A] [IsDomain A] {x : A}
    (hbasic :
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)))
    (q : PrimeSpectrum A) :
    (PrimeSpectrum.basicOpen (algebraMap A (Localization.AtPrime q.asIdeal) x) :
        Set (PrimeSpectrum (Localization.AtPrime q.asIdeal))) =
      ({(⊥ : PrimeSpectrum (Localization.AtPrime q.asIdeal))} :
        Set (PrimeSpectrum (Localization.AtPrime q.asIdeal))) := by
  let S := Localization.AtPrime q.asIdeal
  letI : IsDomain S := IsLocalization.isDomain_of_atPrime S q.asIdeal
  have hinj :
      Function.Injective (PrimeSpectrum.comap (algebraMap A S)) :=
    (PrimeSpectrum.localization_comap_isEmbedding S q.asIdeal.primeCompl).injective
  have halg_inj : Function.Injective (algebraMap A S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors q.asIdeal)
  have hx0 : x ≠ 0 := by
    -- The generic point belongs to `D(x)`, so `x` is nonzero.
    have hbot_mem : (⊥ : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
      simpa [hbasic]
    exact (PrimeSpectrum.mem_basicOpen x (⊥ : PrimeSpectrum A)).1 hbot_mem
  have hbot_comap :
      PrimeSpectrum.comap (algebraMap A S) (⊥ : PrimeSpectrum S) = (⊥ : PrimeSpectrum A) := by
    apply PrimeSpectrum.ext
    -- Injectivity of the localization map identifies the contracted zero ideal with `(0)`.
    change Ideal.comap (algebraMap A S) (⊥ : Ideal S) = (⊥ : Ideal A)
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp halg_inj
  ext y
  constructor
  · intro hy
    have hy_comap_mem :
        PrimeSpectrum.comap (algebraMap A S) y ∈
          (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
      exact (PrimeSpectrum.mem_basicOpen x (PrimeSpectrum.comap (algebraMap A S) y)).2 <|
        by
          simpa [Ideal.mem_comap] using
            (PrimeSpectrum.mem_basicOpen (algebraMap A S x) y).1 hy
    have hy_comap_eq_bot : PrimeSpectrum.comap (algebraMap A S) y = (⊥ : PrimeSpectrum A) := by
      simpa [hbasic] using hy_comap_mem
    refine Set.mem_singleton_iff.mpr ?_
    exact hinj (hy_comap_eq_bot.trans hbot_comap.symm)
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    -- Injectivity of `A → A_q` keeps the nonzero element `x` nonzero after localization.
    refine (PrimeSpectrum.mem_basicOpen (algebraMap A S x) (⊥ : PrimeSpectrum S)).2 ?_
    intro hxS
    exact hx0 (halg_inj (by simpa using hxS))

/-- Helper for Lemma 10.61.4: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
lemma exists_nat_ringKrullDim_of_local_noetherian_ring
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim A = (ringKrullDim A).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim A) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.61.4: in a Noetherian domain, a nonzero prime under an open generic
singleton has prime height exactly `1`. -/
lemma primeHeight_eq_one_of_ne_bot_of_basicOpen_eq_singleton_bot
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] {x : A}
    (hbasic :
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)))
    (q : PrimeSpectrum A) (hq : q ≠ ⊥) :
    q.asIdeal.primeHeight = 1 := by
  let S := Localization.AtPrime q.asIdeal
  letI : IsDomain S := IsLocalization.isDomain_of_atPrime S q.asIdeal
  have hlocal_basic :
      (PrimeSpectrum.basicOpen (algebraMap A S x) : Set (PrimeSpectrum S)) =
        ({(⊥ : PrimeSpectrum S)} : Set (PrimeSpectrum S)) :=
    basicOpen_localizationAtPrime_eq_singleton_bot_of_basicOpen_eq_singleton_bot
      (A := A) hbasic q
  let U := PrimeSpectrum.basicOpen (algebraMap A S x)
  have hU_ne : U ≠ ⊥ := by
    rw [U.ne_bot_iff_nonempty]
    refine ⟨⊥, ?_⟩
    rw [hlocal_basic]
    simp
  have hnot_two : ¬ 2 ≤ ringKrullDim S := by
    intro hdim
    have hfinite : Set.Finite (U : Set (PrimeSpectrum S)) := by
      rw [hlocal_basic]
      exact Set.finite_singleton (⊥ : PrimeSpectrum S)
    exact hfinite.not_infinite <|
      infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim
        (R := S) U hU_ne hdim
  obtain ⟨n, hdimS⟩ := exists_nat_ringKrullDim_of_local_noetherian_ring (A := S)
  have hnle : n ≤ 1 := by
    by_contra hnle'
    have htwo : 2 ≤ n := by omega
    exact hnot_two <| by
      simpa [hdimS] using (show (2 : WithBot ℕ∞) ≤ n by exact_mod_cast htwo)
  have hupper : q.asIdeal.primeHeight ≤ 1 := by
    have hheight_le : (q.asIdeal.height : WithBot ℕ∞) ≤ 1 := by
      calc
        (q.asIdeal.height : WithBot ℕ∞) = ringKrullDim S := by
          simpa [S] using (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal S).symm
        _ = n := hdimS
        _ ≤ 1 := by exact_mod_cast hnle
    simpa [Ideal.height_eq_primeHeight] using hheight_le
  have hbot_primeHeight : (⊥ : Ideal A).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff]
    simpa [IsDomain.minimalPrimes_eq_singleton_bot A]
  have hbot_lt_q : (⊥ : Ideal A) < q.asIdeal := by
    refine lt_of_le_of_ne bot_le ?_
    intro hEq
    exact hq (PrimeSpectrum.ext hEq.symm)
  have hlower : (1 : ℕ∞) ≤ q.asIdeal.primeHeight := by
    simpa [hbot_primeHeight] using
      (Ideal.primeHeight_add_one_le_of_lt hbot_lt_q)
  exact le_antisymm hupper hlower

/-- Helper for Lemma 10.61.4: infinitely many primes above `p` give infinitely many primes of the
quotient `R / p`. -/
lemma infinite_primeSpectrum_quotient_of_infinite_primesOver
    (p : PrimeSpectrum R) [Infinite { q : PrimeSpectrum R // p ≤ q }] :
    Infinite (PrimeSpectrum (R ⧸ p.asIdeal)) := by
  let f : { q : PrimeSpectrum R // p ≤ q } → PrimeSpectrum (R ⧸ p.asIdeal) := fun q ↦
    (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal).symm
      ⟨q.1, (PrimeSpectrum.mem_zeroLocus q.1 (p.asIdeal : Set R)).2 q.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' := congrArg
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal) hab
    have hab'' : a.1 = b.1 := by
      simpa [f] using congrArg Subtype.val hab'
    exact Subtype.ext hab''
  exact Infinite.of_injective f hf

-- Proof sketch: this is a reformulation of Lemma `10.35.6`. In a domain of Krull dimension `1`,
-- every nonzero prime ideal is maximal, so only `⊥` can fail to be maximal. Hence infinitely many
-- prime ideals force infinitely many maximal ideals, and the dimension-one Jacobson criterion
-- applies.
/-- Lemma 10.61.4 (1): any Noetherian domain of Krull dimension `1` with infinitely many prime
ideals is a Jacobson ring. In Lean, “infinitely many prime ideals” is expressed canonically by
`[Infinite (PrimeSpectrum R)]`. -/
theorem isJacobsonRing_of_isNoetherianRing_of_ringKrullDim_eq_one_of_infinite_primeIdeals
    [IsDomain R] [Infinite (PrimeSpectrum R)] (hdim : ringKrullDim R = 1) :
    IsJacobsonRing R := by
  have hdim' : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  letI : Ring.DimensionLEOne R :=
    ⟨fun {p} hp hprime ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim' p hp hprime⟩
  letI : Infinite (MaximalSpectrum R) := infinite_maximalSpectrum_of_infinite_primeSpectrum
  exact isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum R

-- Proof sketch: argue by contradiction. If `R` were not Jacobson, Lemma `10.35.5` gives a
-- nonmaximal prime `P` whose singleton is locally closed in `Spec R`. For each prime `Q ⊇ P`,
-- the corresponding localization of `R ⧸ P` has locally closed generic point, so Lemma `10.61.1`
-- forces it to have Krull dimension `1`; thus `R ⧸ P` is a one-dimensional Noetherian domain.
-- The hypothesis gives infinitely many primes above `P`, hence infinitely many primes of `R ⧸ P`,
-- so clause `(1)` makes `R ⧸ P` Jacobson, contradicting that `{P}` is open in `V(P)`.
/-- Lemma 10.61.4 (2): any Noetherian ring such that every prime ideal is either maximal or
contained in infinitely many prime ideals is a Jacobson ring. -/
theorem isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver
    (hprime :
      ∀ p : PrimeSpectrum R,
        p.asIdeal.IsMaximal ∨ Infinite { q : PrimeSpectrum R // p ≤ q }) :
    IsJacobsonRing R := by
  by_contra hR
  obtain ⟨p, f, hp_nonmax, hp⟩ :=
    exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing
      (R := R) hR
  let A := R ⧸ p.asIdeal
  let xbar : A := Ideal.Quotient.mk p.asIdeal f
  have hbasicA :
      (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)) := by
    -- Pass to the quotient ring, where the obstruction becomes an open generic singleton.
    simpa [A, xbar] using
      basicOpen_quotient_eq_singleton_bot_of_zeroLocus_inter_basicOpen_eq_singleton
        (R := R) p f hp
  have hp_inf : Infinite { q : PrimeSpectrum R // p ≤ q } := by
    rcases hprime p with hp_max | hp_inf
    · exact False.elim (hp_nonmax hp_max)
    · exact hp_inf
  letI : Infinite (PrimeSpectrum A) :=
    infinite_primeSpectrum_quotient_of_infinite_primesOver (R := R) p
  have hdimA_le : ringKrullDim A ≤ 1 := by
    refine (ringKrullDim_le_iff_isMaximal_height_le (R := A) 1).2 ?_
    intro m hm
    by_cases hm0 : m = ⊥
    · simpa [hm0]
    · let q : PrimeSpectrum A := ⟨m, hm.isPrime⟩
      have hq : q ≠ ⊥ := by
        intro hq
        exact hm0 (congrArg PrimeSpectrum.asIdeal hq)
      have hq_height :
          q.asIdeal.primeHeight = 1 :=
        primeHeight_eq_one_of_ne_bot_of_basicOpen_eq_singleton_bot
          (A := A) hbasicA q hq
      -- Every maximal ideal of `A` has height at most `1`.
      simpa [q, Ideal.height_eq_primeHeight, hq_height]
  have hp_ne_top : p.asIdeal ≠ ⊤ := p.isPrime.ne_top
  obtain ⟨M, hMmax, hpMle⟩ := Ideal.exists_le_maximal p.asIdeal hp_ne_top
  have hMp : p.asIdeal < M := by
    refine lt_of_le_of_ne hpMle ?_
    intro hEq
    exact hp_nonmax (hEq ▸ hMmax)
  let mSpec : PrimeSpectrum R := ⟨M, hMmax.isPrime⟩
  have hm_zeroLocus :
      mSpec ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact hpMle
  let qbar : PrimeSpectrum A :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal).symm
      ⟨mSpec, hm_zeroLocus⟩
  have hqbar_ne : qbar ≠ (⊥ : PrimeSpectrum A) := by
    intro hqbar
    have hqbar_asIdeal : qbar.asIdeal = (⊥ : Ideal A) := congrArg PrimeSpectrum.asIdeal hqbar
    have hmap_eq_bot : Ideal.map (Ideal.Quotient.mk p.asIdeal) M = (⊥ : Ideal A) := by
      calc
        Ideal.map (Ideal.Quotient.mk p.asIdeal) M = qbar.asIdeal := by
          symm
          simpa [A, qbar] using
            (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_symm_asIdeal
              (I := p.asIdeal) ⟨mSpec, hm_zeroLocus⟩)
        _ = (⊥ : Ideal A) := hqbar_asIdeal
    have hM_eq_p : M = p.asIdeal := by
      have hcomap_map :
          Ideal.comap (Ideal.Quotient.mk p.asIdeal)
            (Ideal.map (Ideal.Quotient.mk p.asIdeal) M) = M := by
        calc
          Ideal.comap (Ideal.Quotient.mk p.asIdeal)
              (Ideal.map (Ideal.Quotient.mk p.asIdeal) M) =
                M ⊔ Ideal.comap (Ideal.Quotient.mk p.asIdeal) (⊥ : Ideal A) := by
                  simpa using
                    (Ideal.comap_map_of_surjective (Ideal.Quotient.mk p.asIdeal)
                      Ideal.Quotient.mk_surjective M)
          _ = M ⊔ p.asIdeal := by
                rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          _ = M := sup_eq_left.mpr hpMle
      calc
        M = Ideal.comap (Ideal.Quotient.mk p.asIdeal)
            (Ideal.map (Ideal.Quotient.mk p.asIdeal) M) := by
              symm
              exact hcomap_map
        _ = Ideal.comap (Ideal.Quotient.mk p.asIdeal) (⊥ : Ideal A) := by rw [hmap_eq_bot]
        _ = p.asIdeal := by
              rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hMp.ne hM_eq_p.symm
  have hdimA_ge : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
    have hqbar_height :
        qbar.asIdeal.primeHeight = 1 :=
      primeHeight_eq_one_of_ne_bot_of_basicOpen_eq_singleton_bot
        (A := A) hbasicA qbar hqbar_ne
    calc
      (1 : WithBot ℕ∞) = (qbar.asIdeal.height : WithBot ℕ∞) := by
        simpa [Ideal.height_eq_primeHeight, hqbar_height]
      _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_ne_top qbar.isPrime.ne_top
  have hdimA : ringKrullDim A = 1 := le_antisymm hdimA_le hdimA_ge
  have hJacobsonA : IsJacobsonRing A :=
    isJacobsonRing_of_isNoetherianRing_of_ringKrullDim_eq_one_of_infinite_primeIdeals
      (R := A) hdimA
  have hbot_nonmax : ¬ (⊥ : Ideal A).IsMaximal := by
    intro hbot_max
    have hsub : Subsingleton (PrimeSpectrum A) := by
      refine ⟨fun q₁ q₂ ↦ ?_⟩
      apply PrimeSpectrum.ext
      have hq₁ : (⊥ : Ideal A) = q₁.asIdeal := hbot_max.eq_of_le q₁.isPrime.ne_top bot_le
      have hq₂ : (⊥ : Ideal A) = q₂.asIdeal := hbot_max.eq_of_le q₂.isPrime.ne_top bot_le
      exact hq₁.symm.trans hq₂
    letI : Finite (PrimeSpectrum A) := Finite.of_subsingleton
    exact Finite.false (inferInstance : Finite (PrimeSpectrum A))
  have hxbar_not_mem_bot : xbar ∉ (⊥ : Ideal A) := by
    -- The singleton basic open is nonempty, so its defining element is nonzero.
    simpa [hbasicA] using
      (PrimeSpectrum.mem_basicOpen xbar (⊥ : PrimeSpectrum A)).1
        (by simpa [hbasicA] : (⊥ : PrimeSpectrum A) ∈
          (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A)))
  have hinfinite_basic :
      Set.Infinite
        (PrimeSpectrum.zeroLocus (R := A) ((⊥ : Ideal A) : Set A) ∩
          (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A))) :=
    infinite_zeroLocus_inter_basicOpen_of_isJacobsonRing
      (R := A) (p := (⊥ : PrimeSpectrum A)) xbar hbot_nonmax hxbar_not_mem_bot
  have hfinite_basic :
      ¬ Set.Infinite
        (PrimeSpectrum.zeroLocus (R := A) ((⊥ : Ideal A) : Set A) ∩
          (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A))) := by
    simpa [PrimeSpectrum.zeroLocus_bot, hbasicA] using
      (Set.not_infinite.mpr (Set.finite_singleton (⊥ : PrimeSpectrum A)))
  exact hfinite_basic hinfinite_basic

end
