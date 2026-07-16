import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_61_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_61_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: Jacobson rings, Jacobson-radical membership, and away-localization in
  commutative algebra;
- sampled owner declarations of the same kind:
  `Ring.jacobson`,
  `Definition_15_10_1`'s canonical Zariski-pair surface `I ≤ Ring.jacobson A`,
  `isJacobsonRing_localization`,
  `isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver`;
- best owner abstraction: an arbitrary away-localization target `S` with `[Algebra A S]` and
  `[IsLocalization.Away f S]`, of which `Localization.Away f` is the canonical model;
- primitive data: `f : A`, the Jacobson-radical membership `hf : f ∈ Ring.jacobson A`, and the
  ambient away-localization owner structure on `S`;
- derived API: the Zariski-pair formulation obtained from `I ≤ Ring.jacobson A` and `f ∈ I`; the
  concrete ring `Localization.Away f` is only a specialization of the owner-level statement.

Layer triage:
- `source-facing`: `isJacobsonRing_of_isLocalizationAway_of_mem_of_le_jacobson`;
- `core/canonical`: `isJacobsonRing_of_isLocalizationAway_of_mem_jacobson`, proved from the
  chapter Jacobson criterion
  `isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver` together
  with mathlib's away-localization infrastructure;
- `bridge/view`: the specialization `S = Localization.Away f`, supplied automatically by the
  canonical `IsLocalization.Away` instance.
-/

-- Proof sketch: apply the Noetherian Jacobson criterion to an arbitrary away-localization target
-- `S`. For a nonmaximal prime of `S`, contract to a prime of `A` and use `f ∈ Ring.jacobson A`
-- to show the corresponding quotient has dimension at least `1`; the local domain criterion from
-- Chapter 10 then gives infinitely many primes above it, so Lemma `10.61.4` makes `S` Jacobson.
variable [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: a prime of an away-localization contracts to a prime ideal avoiding
the localized element. -/
lemma comap_away_not_mem {S : Type v} [CommRing S] [Algebra A S] (f : A)
    [IsLocalization.Away f S] (p : PrimeSpectrum S) :
    f ∉ (PrimeSpectrum.comap (algebraMap A S) p).asIdeal := by
  -- The image of `f` is a unit after localizing away from `f`, so it cannot lie in a prime ideal.
  change f ∉ Ideal.comap (algebraMap A S) p.asIdeal
  rw [Ideal.mem_comap]
  intro hf
  exact p.2.ne_top <| Ideal.eq_top_of_isUnit_mem _ hf (IsLocalization.Away.algebraMap_isUnit f)

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: a prime ideal avoiding a Jacobson-radical element is not maximal. -/
lemma not_isMaximal_of_mem_jacobson_of_not_mem {f : A} (hf : f ∈ Ring.jacobson A)
    (P : PrimeSpectrum A) (hfP : f ∉ P.asIdeal) :
    ¬ P.asIdeal.IsMaximal := by
  -- Every maximal ideal contains the Jacobson radical.
  intro hP
  exact hfP ((Ring.jacobson_le_of_isMaximal P.asIdeal) hf)

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: extending a prime ideal of `A` that avoids `f` to an
away-localization again gives a prime ideal. -/
lemma away_extension_isPrime {S : Type v} [CommRing S] [Algebra A S] (f : A)
    [IsLocalization.Away f S] (Q : PrimeSpectrum A) (hQf : f ∉ Q.asIdeal) :
    (Ideal.map (algebraMap A S) Q.asIdeal).IsPrime := by
  -- The prime avoids the powers of `f`, so standard localization extension preserves primality.
  have hdisj : Disjoint (Submonoid.powers f : Set A) Q.asIdeal := by
    rw [Ideal.disjoint_powers_iff_notMem f Q.2.isRadical]
    exact hQf
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) S _ Q.2 hdisj

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: contracting the extension of a prime ideal avoiding `f` recovers the
original prime. -/
lemma comap_away_extension_eq {S : Type v} [CommRing S] [Algebra A S] (f : A)
    [IsLocalization.Away f S] (Q : PrimeSpectrum A) (hQf : f ∉ Q.asIdeal) :
    PrimeSpectrum.comap (algebraMap A S)
        ⟨Ideal.map (algebraMap A S) Q.asIdeal, away_extension_isPrime f Q hQf⟩ = Q := by
  -- Contraction of the extended prime is the standard localization identity.
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap A S) (Ideal.map (algebraMap A S) Q.asIdeal) = Q.asIdeal
  have hdisj : Disjoint (Submonoid.powers f : Set A) Q.asIdeal := by
    rw [Ideal.disjoint_powers_iff_notMem f Q.2.isRadical]
    exact hQf
  simpa using
    (IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f) S Q.2 hdisj)

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: a nonmaximal prime of an away-localization sits in a strict chain
`P < Q < M` after contraction to `A`, with `M` maximal and containing `f`. -/
lemma exists_chain_of_nonmaximal_away_prime {S : Type v} [CommRing S] [Algebra A S]
    (f : A) [IsLocalization.Away f S] (hf : f ∈ Ring.jacobson A)
    (p : PrimeSpectrum S) (hp : ¬ p.asIdeal.IsMaximal) :
    ∃ qmax : PrimeSpectrum S, ∃ M : PrimeSpectrum A,
      p < qmax ∧
        let P := PrimeSpectrum.comap (algebraMap A S) p
        let Q := PrimeSpectrum.comap (algebraMap A S) qmax
        P < Q ∧ Q < M ∧ M.asIdeal.IsMaximal ∧
          f ∉ P.asIdeal ∧ f ∉ Q.asIdeal ∧ f ∈ M.asIdeal := by
  classical
  -- Choose a maximal prime strictly above `p` in the localization.
  obtain ⟨mS, hmS, hpmS⟩ := p.asIdeal.exists_le_maximal p.2.1
  let qmax : PrimeSpectrum S := ⟨mS, hmS.isPrime⟩
  have hp_lt_qmax : p < qmax := by
    refine lt_of_le_of_ne hpmS ?_
    intro hpq
    exact hp (hpq ▸ hmS)
  let P : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A S) p
  let Q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A S) qmax
  have hfP : f ∉ P.asIdeal := comap_away_not_mem f p
  have hfQ : f ∉ Q.asIdeal := comap_away_not_mem f qmax
  have hQ_not_max : ¬ Q.asIdeal.IsMaximal :=
    not_isMaximal_of_mem_jacobson_of_not_mem hf Q hfQ
  -- Lift `Q` to a maximal ideal of `A`; Jacobson-radical membership then forces `f` into it.
  obtain ⟨mA, hmA, hQmA⟩ := Q.asIdeal.exists_le_maximal Q.2.1
  let M : PrimeSpectrum A := ⟨mA, hmA.isPrime⟩
  have hP_lt_Q : P < Q := by
    refine lt_of_le_of_ne (Ideal.comap_mono hpmS) ?_
    intro hPQ
    have hmap :
        Ideal.map (algebraMap A S) P.asIdeal =
          Ideal.map (algebraMap A S) Q.asIdeal := by
      simpa using congrArg (Ideal.map (algebraMap A S)) (congrArg PrimeSpectrum.asIdeal hPQ)
    have hp_eq_qmax : p = qmax := by
      apply PrimeSpectrum.ext
      calc
        p.asIdeal = Ideal.map (algebraMap A S) P.asIdeal := by
          simpa [P, PrimeSpectrum.comap_asIdeal] using
            (IsLocalization.map_comap (Submonoid.powers f) S p.asIdeal).symm
        _ = Ideal.map (algebraMap A S) Q.asIdeal := hmap
        _ = qmax.asIdeal := by
          simpa [Q, PrimeSpectrum.comap_asIdeal] using
            (IsLocalization.map_comap (Submonoid.powers f) S qmax.asIdeal)
    exact hp_lt_qmax.ne hp_eq_qmax
  have hQ_lt_M : Q < M := by
    refine lt_of_le_of_ne hQmA ?_
    intro hQM
    exact hQ_not_max (hQM ▸ hmA)
  have hfM : f ∈ M.asIdeal := by
    exact Ring.jacobson_le_of_isMaximal M.asIdeal hf
  refine ⟨qmax, M, hp_lt_qmax, ?_⟩
  -- This packages the exact strict chain used later in the quotient-local proof.
  simpa [P, Q, M] using ⟨hP_lt_Q, hQ_lt_M, hmA, hfP, hfQ, hfM⟩

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: a prime of the localization of a quotient that lies in the basic
open defined by the image of `f` lifts to a prime of `A` that still avoids `f`. -/
lemma quotient_localization_basicOpen_lift_avoids_f
    (I : Ideal A) (mbar : PrimeSpectrum (A ⧸ I)) (f : A)
    (r : PrimeSpectrum (Localization.AtPrime mbar.asIdeal))
    (hr : r ∈ PrimeSpectrum.basicOpen
      (algebraMap (A ⧸ I) (Localization.AtPrime mbar.asIdeal) (Ideal.Quotient.mk I f))) :
    f ∉ (PrimeSpectrum.comap (Ideal.Quotient.mk I)
      (PrimeSpectrum.comap (algebraMap (A ⧸ I) (Localization.AtPrime mbar.asIdeal)) r)).asIdeal := by
  -- Contract first from the local ring to the quotient, then from the quotient to `A`.
  change f ∉ Ideal.comap (Ideal.Quotient.mk I)
    (Ideal.comap (algebraMap (A ⧸ I) (Localization.AtPrime mbar.asIdeal)) r.asIdeal)
  rw [Ideal.mem_comap, Ideal.mem_comap]
  intro hf
  exact (PrimeSpectrum.mem_basicOpen _ r).1 hr hf

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: extending a prime of `A` that lies over the contraction of `p`
produces a prime of the away-localization lying above `p`. -/
lemma away_extension_lands_above_of_comap_le {S : Type v} [CommRing S] [Algebra A S]
    (f : A) [IsLocalization.Away f S] {p : PrimeSpectrum S} {N : PrimeSpectrum A}
    (hPN : PrimeSpectrum.comap (algebraMap A S) p ≤ N) (hNf : f ∉ N.asIdeal) :
    p ≤ ⟨Ideal.map (algebraMap A S) N.asIdeal, away_extension_isPrime f N hNf⟩ := by
  -- Rewrite both primes as extensions from `A` and use monotonicity of ideal maps.
  change p.asIdeal ≤ Ideal.map (algebraMap A S) N.asIdeal
  calc
    p.asIdeal = Ideal.map (algebraMap A S)
        (PrimeSpectrum.comap (algebraMap A S) p).asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using
        (IsLocalization.map_comap (Submonoid.powers f) S p.asIdeal).symm
    _ ≤ Ideal.map (algebraMap A S) N.asIdeal :=
      Ideal.map_mono hPN

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: the inverse quotient-spectrum order isomorphism contracts back to the
original prime in the zero locus. -/
lemma primeSpectrumQuotientOrderIsoZeroLocus_symm_apply_comap
    (I : Ideal A) (x : PrimeSpectrum.zeroLocus (I : Set A)) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I)
      (I.primeSpectrumQuotientOrderIsoZeroLocus.symm x) = x.1 := by
  -- Read off the underlying prime after moving back through the quotient-spectrum order isomorphism.
  exact congrArg Subtype.val (I.primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply x)

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: the inverse at-prime order isomorphism contracts back to the chosen
prime below the localization point. -/
lemma atPrime_primeSpectrumOrderIso_symm_apply_comap
    (I : Ideal A) [I.IsPrime] (x : Set.Iic ({ asIdeal := I, isPrime := ‹I.IsPrime› } :
      PrimeSpectrum A)) :
    PrimeSpectrum.comap (algebraMap A (Localization.AtPrime I))
      ((IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime I) I).symm x) = x.1 := by
  -- This turns the bundled `Set.Iic` transport into a direct contraction formula.
  exact congrArg Subtype.val
    ((IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime I) I).apply_symm_apply x)

/-- Helper for Lemma 15.10.5: a local Noetherian domain with a prime strictly between the generic
point and the maximal ideal has Krull dimension at least `2`. -/
lemma two_le_ringKrullDim_of_zero_lt_lt_maximalIdeal
    {B : Type u} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    (q : PrimeSpectrum B) (hbot : (⊥ : PrimeSpectrum B) < q)
    (hqmax : q.asIdeal < IsLocalRing.maximalIdeal B) :
    2 ≤ ringKrullDim B := by
  -- The bottom prime has height `0` in a domain.
  have hbot_height : (⊥ : Ideal B).height = 0 := by
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff,
      IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hbot_primeHeight : (⊥ : Ideal B).primeHeight = 0 := by
    simpa [Ideal.height_eq_primeHeight] using hbot_height
  -- One strict inclusion gives height at least `1`, and a second gives height at least `2`.
  have hq_height_ge : (1 : WithBot ℕ∞) ≤ q.asIdeal.height := by
    have hbot' : (⊥ : Ideal B) < q.asIdeal := by
      simpa using hbot
    have := Ideal.primeHeight_add_one_le_of_lt hbot'
    simpa [hbot_primeHeight, Ideal.height_eq_primeHeight] using this
  have hmax_height_ge : (q.asIdeal.height : WithBot ℕ∞) + 1 ≤ ringKrullDim B := by
    have hmax_height :
        (q.asIdeal.height : WithBot ℕ∞) + 1 ≤ ((IsLocalRing.maximalIdeal B).height : WithBot ℕ∞) := by
      have hmax_primeHeight :
          q.asIdeal.primeHeight + 1 ≤ (IsLocalRing.maximalIdeal B).primeHeight :=
        Ideal.primeHeight_add_one_le_of_lt hqmax
      rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
      exact_mod_cast hmax_primeHeight
    simpa [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using hmax_height
  have htwo_le_qheight : (2 : WithBot ℕ∞) ≤ q.asIdeal.height + 1 := by
    have hq_height_ge' := add_le_add_right hq_height_ge 1
    simpa [add_assoc, add_comm, add_left_comm] using hq_height_ge'
  have htwo_le_height : (2 : WithBot ℕ∞) ≤ ringKrullDim B := by
    exact htwo_le_qheight.trans hmax_height_ge
  -- A local ring identifies the height of its maximal ideal with its Krull dimension.
  exact htwo_le_height

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: after quotienting by the contracted prime `P`, the intermediate
prime `Q` still sits strictly between the generic point and the image of the maximal prime `M`. -/
lemma quotient_intermediate_prime_strict_chain
    (P Q M : PrimeSpectrum A) (hP_lt_Q : P < Q) (hQ_lt_M : Q < M) :
    let B := A ⧸ P.asIdeal
    let qbar : PrimeSpectrum B :=
      P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨Q, hP_lt_Q.le⟩
    let mbar : PrimeSpectrum B :=
      P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm
        ⟨M, le_trans hP_lt_Q.le hQ_lt_M.le⟩
    (⊥ : PrimeSpectrum B) < qbar ∧ qbar < mbar := by
  let B := A ⧸ P.asIdeal
  let e : PrimeSpectrum B ≃o PrimeSpectrum.zeroLocus (P.asIdeal : Set A) :=
    P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  let qbar : PrimeSpectrum B := e.symm ⟨Q, hP_lt_Q.le⟩
  let mbar : PrimeSpectrum B := e.symm ⟨M, le_trans hP_lt_Q.le hQ_lt_M.le⟩
  have hcomap_qbar :
      PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal) qbar = Q := by
    -- Contracting `qbar` through the quotient map recovers the original prime `Q`.
    simpa [qbar] using
      primeSpectrumQuotientOrderIsoZeroLocus_symm_apply_comap P.asIdeal ⟨Q, hP_lt_Q.le⟩
  have hcomap_mbar :
      PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal) mbar = M := by
    -- The same explicit contraction formula identifies `mbar` with `M`.
    simpa [mbar] using
      primeSpectrumQuotientOrderIsoZeroLocus_symm_apply_comap P.asIdeal
        ⟨M, le_trans hP_lt_Q.le hQ_lt_M.le⟩
  have hbot_lt_qbar : (⊥ : PrimeSpectrum B) < qbar := by
    -- If `qbar` were the generic point of the quotient, contracting would force `Q = P`.
    refine lt_of_le_of_ne bot_le ?_
    intro hqbar_bot
    have hQ_eq_P : Q = P := by
      apply PrimeSpectrum.ext
      have hqbar_bot_asIdeal : qbar.asIdeal = (⊥ : Ideal B) := by
        simpa using congrArg PrimeSpectrum.asIdeal hqbar_bot.symm
      calc
        Q.asIdeal = Ideal.comap (Ideal.Quotient.mk P.asIdeal) qbar.asIdeal := by
          simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap_qbar.symm
        _ = Ideal.comap (Ideal.Quotient.mk P.asIdeal) (⊥ : Ideal B) := by
          simpa [hqbar_bot_asIdeal]
        _ = P.asIdeal := by
          ext x
          rw [Ideal.mem_comap]
          exact Ideal.Quotient.eq_zero_iff_mem
    exact hP_lt_Q.ne hQ_eq_P.symm
  have hqbar_lt_mbar : qbar < mbar := by
    -- Equality of `qbar` and `mbar` would contract to equality of `Q` and `M`.
    refine lt_of_le_of_ne ?_ ?_
    · exact
        e.symm.monotone
          (show (⟨Q, hP_lt_Q.le⟩ : PrimeSpectrum.zeroLocus (P.asIdeal : Set A)) ≤
              ⟨M, le_trans hP_lt_Q.le hQ_lt_M.le⟩ from hQ_lt_M.le)
    · intro hqbar_eq_mbar
      have hQ_eq_M : Q = M := by
        apply PrimeSpectrum.ext
        calc
          Q.asIdeal = Ideal.comap (Ideal.Quotient.mk P.asIdeal) qbar.asIdeal := by
            simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap_qbar.symm
          _ = Ideal.comap (Ideal.Quotient.mk P.asIdeal) mbar.asIdeal := by
            simpa [hqbar_eq_mbar]
          _ = M.asIdeal := by
            simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap_mbar
      exact hQ_lt_M.ne hQ_eq_M
  exact ⟨hbot_lt_qbar, hqbar_lt_mbar⟩

/-- Helper for Lemma 15.10.5: localizing the quotient at `mbar` lifts the intermediate quotient
prime to a prime strictly between the generic point and the maximal ideal. -/
lemma localized_prime_over_intermediate_strict_chain
    {B : Type u} [CommRing B] [IsDomain B] (mbar qbar : PrimeSpectrum B)
    (hqbar_bot : (⊥ : PrimeSpectrum B) < qbar) (hqbar_lt_mbar : qbar < mbar) :
    let Bm := Localization.AtPrime mbar.asIdeal
    let qloc : PrimeSpectrum Bm :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso Bm mbar.asIdeal).symm
        ⟨qbar, hqbar_lt_mbar.le⟩
    PrimeSpectrum.comap (algebraMap B Bm) qloc = qbar ∧
      (⊥ : PrimeSpectrum Bm) < qloc ∧
      qloc.asIdeal < IsLocalRing.maximalIdeal Bm := by
  let Bm := Localization.AtPrime mbar.asIdeal
  let eLoc : PrimeSpectrum Bm ≃o Set.Iic mbar :=
    IsLocalization.AtPrime.primeSpectrumOrderIso Bm mbar.asIdeal
  let qloc : PrimeSpectrum Bm := eLoc.symm ⟨qbar, hqbar_lt_mbar.le⟩
  have hcomap :
      PrimeSpectrum.comap (algebraMap B Bm) qloc = qbar := by
    -- The explicit `symm`-comap formula removes the remaining `Set.Iic` transport.
    simpa [Bm, eLoc, qloc] using
      atPrime_primeSpectrumOrderIso_symm_apply_comap mbar.asIdeal ⟨qbar, hqbar_lt_mbar.le⟩
  have hinj : Function.Injective (algebraMap B Bm) :=
    IsLocalization.injective Bm mbar.asIdeal.primeCompl_le_nonZeroDivisors
  have hcomap_bot :
      PrimeSpectrum.comap (algebraMap B Bm) (⊥ : PrimeSpectrum Bm) = (⊥ : PrimeSpectrum B) := by
    -- Because `B` is a domain, localizing at `mbar` is injective, so the contracted generic point
    -- is still the generic point.
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap B Bm) (⊥ : Ideal Bm) = (⊥ : Ideal B)
    simpa [RingHom.ker_eq_comap_bot] using (RingHom.ker_eq_bot_iff.2 hinj)
  have hbot_lt_qloc : (⊥ : PrimeSpectrum Bm) < qloc := by
    -- Contracting an equality `qloc = ⊥` would force `qbar = ⊥`, contradicting the quotient chain.
    refine lt_of_le_of_ne bot_le ?_
    intro hqloc_bot
    have hqbar_eq_bot : qbar = (⊥ : PrimeSpectrum B) := by
      calc
        qbar = PrimeSpectrum.comap (algebraMap B Bm) qloc := hcomap.symm
        _ = PrimeSpectrum.comap (algebraMap B Bm) (⊥ : PrimeSpectrum Bm) := by
          simpa [hqloc_bot]
        _ = (⊥ : PrimeSpectrum B) := hcomap_bot
    exact hqbar_bot.ne hqbar_eq_bot.symm
  have hqloc_ne_max :
      qloc.asIdeal ≠ IsLocalRing.maximalIdeal Bm := by
    -- If `qloc` were maximal in the localization, its contraction would be exactly `mbar`.
    intro hqloc_max
    have hcomap_eq :
        Ideal.comap (algebraMap B Bm) qloc.asIdeal = mbar.asIdeal :=
      by rw [hqloc_max, Localization.AtPrime.comap_maximalIdeal]
    have hcomap_asIdeal :
        Ideal.comap (algebraMap B Bm) qloc.asIdeal = qbar.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap
    have hqbar_eq_mbar : qbar = mbar := by
      apply PrimeSpectrum.ext
      exact hcomap_asIdeal.symm.trans hcomap_eq
    exact hqbar_lt_mbar.ne hqbar_eq_mbar
  have hqloc_lt_max : qloc.asIdeal < IsLocalRing.maximalIdeal Bm := by
    -- In a local ring every proper prime ideal lies under the maximal ideal, and `qloc` is not
    -- itself maximal by the previous contradiction.
    refine lt_of_le_of_ne ?_ hqloc_ne_max
    exact IsLocalRing.le_maximalIdeal qloc.2.1
  simpa [Bm, qloc] using ⟨hcomap, hbot_lt_qloc, hqloc_lt_max⟩

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.10.5: the localized lift of the intermediate quotient prime lies in the
basic open cut out by the image of `f`. -/
lemma localized_prime_over_intermediate_mem_basicOpen
    (P Q M : PrimeSpectrum A) (hP_lt_Q : P < Q) (hQ_lt_M : Q < M)
    {f : A} (hfQ : f ∉ Q.asIdeal) :
    let B := A ⧸ P.asIdeal
    let qbar : PrimeSpectrum B :=
      P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨Q, hP_lt_Q.le⟩
    let mbar : PrimeSpectrum B :=
      P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm
        ⟨M, le_trans hP_lt_Q.le hQ_lt_M.le⟩
    let Bm := Localization.AtPrime mbar.asIdeal
    let qloc : PrimeSpectrum Bm :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso Bm mbar.asIdeal).symm
        ⟨qbar, (quotient_intermediate_prime_strict_chain P Q M hP_lt_Q hQ_lt_M).2.le⟩
    let fbar : Bm := algebraMap B Bm (Ideal.Quotient.mk P.asIdeal f)
    qloc ∈ PrimeSpectrum.basicOpen fbar := by
  let B := A ⧸ P.asIdeal
  let qbar : PrimeSpectrum B :=
    P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨Q, hP_lt_Q.le⟩
  let mbar : PrimeSpectrum B :=
    P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm
      ⟨M, le_trans hP_lt_Q.le hQ_lt_M.le⟩
  let Bm := Localization.AtPrime mbar.asIdeal
  let qloc : PrimeSpectrum Bm :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso Bm mbar.asIdeal).symm
      ⟨qbar, (quotient_intermediate_prime_strict_chain P Q M hP_lt_Q hQ_lt_M).2.le⟩
  let fbar : Bm := algebraMap B Bm (Ideal.Quotient.mk P.asIdeal f)
  have hcomap_qloc :
      PrimeSpectrum.comap (algebraMap B Bm) qloc = qbar := by
    -- The local lift contracts back to the quotient prime `qbar`.
    simpa [Bm, qloc, qbar] using
      atPrime_primeSpectrumOrderIso_symm_apply_comap mbar.asIdeal
        ⟨qbar, (quotient_intermediate_prime_strict_chain P Q M hP_lt_Q hQ_lt_M).2.le⟩
  have hcomap_qbar :
      PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal) qbar = Q := by
    -- Contracting through the quotient identifies `qbar` with the original prime `Q`.
    simpa [qbar] using
      primeSpectrumQuotientOrderIsoZeroLocus_symm_apply_comap P.asIdeal ⟨Q, hP_lt_Q.le⟩
  -- Membership in `D(fbar)` is exactly the avoidance of `f` after contracting first to `B`
  -- and then to `A`.
  refine (PrimeSpectrum.mem_basicOpen _ qloc).2 ?_
  intro hfbar
  have hqbar_mem :
      Ideal.Quotient.mk P.asIdeal f ∈ qbar.asIdeal := by
    have : Ideal.Quotient.mk P.asIdeal f ∈
        (PrimeSpectrum.comap (algebraMap B Bm) qloc).asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hfbar
    simpa [hcomap_qloc] using this
  have hQ_mem : f ∈ Q.asIdeal := by
    have : f ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal) qbar).asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hqbar_mem
    simpa [hcomap_qbar] using this
  exact hfQ hQ_mem

/-- Helper for Lemma 15.10.5: a nonmaximal prime of an away-localization lies below infinitely
many primes. -/
lemma infinite_primes_over_of_nonmaximal_away_prime {S : Type v} [CommRing S] [Algebra A S]
    (f : A) [IsLocalization.Away f S] (hf : f ∈ Ring.jacobson A)
    (p : PrimeSpectrum S) (hp : ¬ p.asIdeal.IsMaximal) :
    Infinite { q : PrimeSpectrum S // p ≤ q } := by
  classical
  obtain ⟨qmax, M, hp_lt_qmax, hchain⟩ :=
    exists_chain_of_nonmaximal_away_prime f hf p hp
  let P : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A S) p
  let Q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A S) qmax
  have hchain' :
      P < Q ∧ Q < M ∧ M.asIdeal.IsMaximal ∧
        f ∉ P.asIdeal ∧ f ∉ Q.asIdeal ∧ f ∈ M.asIdeal := by
    simpa [P, Q] using hchain
  rcases hchain' with ⟨hP_lt_Q, hQ_lt_M, hMmax, hfP, hfQ, hfM⟩
  let B := A ⧸ P.asIdeal
  let qbar : PrimeSpectrum B :=
    P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨Q, hP_lt_Q.le⟩
  let mbar : PrimeSpectrum B :=
    P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm
      ⟨M, le_trans hP_lt_Q.le hQ_lt_M.le⟩
  let Bm := Localization.AtPrime mbar.asIdeal
  let fbar : Bm := algebraMap B Bm (Ideal.Quotient.mk P.asIdeal f)
  have hreturn_lands_above :
      ∀ r : { r : PrimeSpectrum Bm // r ∈ PrimeSpectrum.basicOpen fbar },
        p ≤
          ⟨Ideal.map (algebraMap A S)
              (PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
                (PrimeSpectrum.comap (algebraMap B Bm) r.1)).asIdeal,
            away_extension_isPrime f
              (PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
                (PrimeSpectrum.comap (algebraMap B Bm) r.1))
              (quotient_localization_basicOpen_lift_avoids_f P.asIdeal mbar f r.1 r.2)⟩ := by
    intro r
    -- The already proved adapter lemmas identify the returned away-prime and show it lies above `p`.
    exact away_extension_lands_above_of_comap_le f
      (S := S) (p := p)
      (N := PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
        (PrimeSpectrum.comap (algebraMap B Bm) r.1))
      (by
        change P.asIdeal ≤ Ideal.comap (Ideal.Quotient.mk P.asIdeal)
          (Ideal.comap (algebraMap B Bm) r.1.asIdeal)
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap]
        have hx0 : Ideal.Quotient.mk P.asIdeal x = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hx
        simp [hx0])
      (quotient_localization_basicOpen_lift_avoids_f P.asIdeal mbar f r.1 r.2)
  letI : IsDomain B := Ideal.Quotient.isDomain P.asIdeal
  have hqbar_bot :
      (⊥ : PrimeSpectrum B) < qbar := by
    -- Route correction: first stabilize the quotient chain `⊥ < qbar < mbar`.
    simpa [B, qbar, mbar] using
      (quotient_intermediate_prime_strict_chain P Q M hP_lt_Q hQ_lt_M).1
  have hqbar_lt_mbar : qbar < mbar := by
    -- This isolates the quotient step before introducing the localization transport.
    simpa [B, qbar, mbar] using
      (quotient_intermediate_prime_strict_chain P Q M hP_lt_Q hQ_lt_M).2
  let qloc : PrimeSpectrum Bm :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso Bm mbar.asIdeal).symm
      ⟨qbar, hqbar_lt_mbar.le⟩
  have hqloc_comap :
      PrimeSpectrum.comap (algebraMap B Bm) qloc = qbar := by
    -- The localized lift contracts back to the intermediate quotient prime.
    simpa [B, qbar, mbar, Bm, qloc] using
      (localized_prime_over_intermediate_strict_chain (B := B) mbar qbar
        hqbar_bot hqbar_lt_mbar).1
  have hbot_lt_qloc : (⊥ : PrimeSpectrum Bm) < qloc := by
    -- This is the local-domain input for Lemma `10.61.1`.
    simpa [B, qbar, mbar, Bm, qloc] using
      (localized_prime_over_intermediate_strict_chain (B := B) mbar qbar
        hqbar_bot hqbar_lt_mbar).2.1
  have hqloc_lt_max : qloc.asIdeal < IsLocalRing.maximalIdeal Bm := by
    -- This provides the second strict inclusion needed for dimension at least `2`.
    simpa [B, qbar, mbar, Bm, qloc] using
      (localized_prime_over_intermediate_strict_chain (B := B) mbar qbar
        hqbar_bot hqbar_lt_mbar).2.2
  have hqloc_mem :
      qloc ∈ PrimeSpectrum.basicOpen fbar := by
    -- The image of `f` avoids `qloc` because `f` already avoids the intermediate prime `Q`.
    simpa [B, qbar, mbar, Bm, qloc, fbar] using
      localized_prime_over_intermediate_mem_basicOpen P Q M hP_lt_Q hQ_lt_M hfQ
  letI : IsNoetherianRing Bm :=
    IsLocalization.isNoetherianRing mbar.asIdeal.primeCompl Bm inferInstance
  letI : IsDomain Bm := IsLocalization.isDomain_of_atPrime Bm mbar.asIdeal
  have hbasicOpen_ne_bot :
      (PrimeSpectrum.basicOpen fbar : TopologicalSpace.Opens (PrimeSpectrum Bm)) ≠ ⊥ := by
    -- The witness `qloc ∈ D(fbar)` shows the basic open is nonempty.
    intro hbot
    have : qloc ∈ ((⊥ : TopologicalSpace.Opens (PrimeSpectrum Bm)) :
        Set (PrimeSpectrum Bm)) := by
      simpa [hbot] using hqloc_mem
    simpa using this
  have hbasicOpen_infinite :
      Set.Infinite ((PrimeSpectrum.basicOpen fbar : TopologicalSpace.Opens (PrimeSpectrum Bm)) :
        Set (PrimeSpectrum Bm)) := by
    -- Lemma `10.61.1` applies in the local quotient because `qloc` lies strictly between the
    -- generic point and the maximal ideal.
    refine infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim
      (PrimeSpectrum.basicOpen fbar) hbasicOpen_ne_bot ?_
    exact two_le_ringKrullDim_of_zero_lt_lt_maximalIdeal qloc hbot_lt_qloc hqloc_lt_max
  let returnMap :
      { r : PrimeSpectrum Bm // r ∈ PrimeSpectrum.basicOpen fbar } →
        { q : PrimeSpectrum S // p ≤ q } := fun r ↦
      ⟨⟨Ideal.map (algebraMap A S)
          (PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
            (PrimeSpectrum.comap (algebraMap B Bm) r.1)).asIdeal,
        away_extension_isPrime f
          (PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
            (PrimeSpectrum.comap (algebraMap B Bm) r.1))
          (quotient_localization_basicOpen_lift_avoids_f P.asIdeal mbar f r.1 r.2)⟩,
        hreturn_lands_above r⟩
  have hreturn_injective : Function.Injective returnMap := by
    intro r₁ r₂ hEq
    apply Subtype.ext
    apply (IsLocalization.AtPrime.primeSpectrumOrderIso Bm mbar.asIdeal).injective
    apply Subtype.ext
    -- Contract equal away-extensions back to `A`, then use quotient and localization contraction
    -- to recover equality of the original local primes.
    have hAeq :
        PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
            (PrimeSpectrum.comap (algebraMap B Bm) r₁.1) =
          PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
            (PrimeSpectrum.comap (algebraMap B Bm) r₂.1) := by
      calc
        PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
            (PrimeSpectrum.comap (algebraMap B Bm) r₁.1) =
            PrimeSpectrum.comap (algebraMap A S) (returnMap r₁).1 := by
              exact (comap_away_extension_eq f
                (PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
                  (PrimeSpectrum.comap (algebraMap B Bm) r₁.1))
                (quotient_localization_basicOpen_lift_avoids_f P.asIdeal mbar f r₁.1 r₁.2)).symm
        _ = PrimeSpectrum.comap (algebraMap A S) (returnMap r₂).1 := by
              simpa using congrArg (PrimeSpectrum.comap (algebraMap A S)) (congrArg Subtype.val hEq)
        _ = PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
            (PrimeSpectrum.comap (algebraMap B Bm) r₂.1) := by
              exact comap_away_extension_eq f
                (PrimeSpectrum.comap (Ideal.Quotient.mk P.asIdeal)
                  (PrimeSpectrum.comap (algebraMap B Bm) r₂.1))
                (quotient_localization_basicOpen_lift_avoids_f P.asIdeal mbar f r₂.1 r₂.2)
    have hBeq :
        PrimeSpectrum.comap (algebraMap B Bm) r₁.1 =
          PrimeSpectrum.comap (algebraMap B Bm) r₂.1 := by
      apply PrimeSpectrum.ext
      have hAeq_ideal :
          Ideal.comap (Ideal.Quotient.mk P.asIdeal)
              (PrimeSpectrum.comap (algebraMap B Bm) r₁.1).asIdeal =
            Ideal.comap (Ideal.Quotient.mk P.asIdeal)
              (PrimeSpectrum.comap (algebraMap B Bm) r₂.1).asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hAeq
      calc
        (PrimeSpectrum.comap (algebraMap B Bm) r₁.1).asIdeal =
            Ideal.map (Ideal.Quotient.mk P.asIdeal)
              (Ideal.comap (Ideal.Quotient.mk P.asIdeal)
                (PrimeSpectrum.comap (algebraMap B Bm) r₁.1).asIdeal) := by
              symm
              exact (PrimeSpectrum.comap (algebraMap B Bm) r₁.1).asIdeal.map_comap_of_surjective
                (Ideal.Quotient.mk P.asIdeal) Ideal.Quotient.mk_surjective
        _ = Ideal.map (Ideal.Quotient.mk P.asIdeal)
              (Ideal.comap (Ideal.Quotient.mk P.asIdeal)
                (PrimeSpectrum.comap (algebraMap B Bm) r₂.1).asIdeal) := by
              exact congrArg (Ideal.map (Ideal.Quotient.mk P.asIdeal)) hAeq_ideal
        _ = (PrimeSpectrum.comap (algebraMap B Bm) r₂.1).asIdeal := by
              exact (PrimeSpectrum.comap (algebraMap B Bm) r₂.1).asIdeal.map_comap_of_surjective
                (Ideal.Quotient.mk P.asIdeal) Ideal.Quotient.mk_surjective
    simpa using hBeq
  letI : Infinite { r : PrimeSpectrum Bm // r ∈ PrimeSpectrum.basicOpen fbar } :=
    hbasicOpen_infinite.to_subtype
  exact Infinite.of_injective returnMap hreturn_injective

/-- Lemma 15.10.5 in canonical owner form: if `A` is Noetherian and `f ∈ Ring.jacobson A`, then
any away localization of `A` at `f` is a Jacobson ring. The textbook ring `Localization.Away f`
is the special case `S = Localization.Away f`. -/
theorem isJacobsonRing_of_isLocalizationAway_of_mem_jacobson
    {S : Type v} [CommRing S] [Algebra A S] (f : A) [IsLocalization.Away f S]
    (hf : f ∈ Ring.jacobson A) :
    IsJacobsonRing S := by
  letI : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
  -- Apply the Noetherian Jacobson criterion and split into the maximal and nonmaximal cases.
  refine isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver ?_
  intro p
  by_cases hp : p.asIdeal.IsMaximal
  · exact Or.inl hp
  · exact Or.inr <| infinite_primes_over_of_nonmaximal_away_prime f hf p hp

/-- Lemma 15.10.5 in the textbook Zariski-pair form: if `(A, I)` is a Zariski pair with `A`
Noetherian and `f ∈ I`, then any away localization of `A` at `f` is a Jacobson ring. The
textbook ring `Localization.Away f` is the special case `S = Localization.Away f`. -/
theorem isJacobsonRing_of_isLocalizationAway_of_mem_of_le_jacobson
    {S : Type v} [CommRing S] [Algebra A S] (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (f : A) [IsLocalization.Away f S] (hf : f ∈ I) :
    IsJacobsonRing S :=
  isJacobsonRing_of_isLocalizationAway_of_mem_jacobson f (hI hf)

end
