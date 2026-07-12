import Mathlib
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Lemma_10_35_9
import StacksProject_2024.Chap10.Lemma_10_37_16
import StacksProject_2024.Chap10.Lemma_10_37_12
import StacksProject_2024.Chap10.Lemma_10_119_7
import StacksProject_2024.Chap10.Lemma_10_120_17
import StacksProject_2024.Chap15.Lemma_15_44_2
import StacksProject_2024.Chap15.Lemma_15_44_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Lemma 15.44.4:
- primary domain: étale commutative algebra over Dedekind domains, together with the canonical
  Dedekind-ring and localization owners for one-dimensional normal rings;
- sampled owner declarations of the same kind:
  `IsDedekindRing`,
  `IsDedekindDomain`,
  `normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains`,
  `isDedekindDomainByFactorization_iff_isDedekindDomainDvr`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- owner abstraction: the canonical `IsDedekindRing` owner on `B`, the Dedekind-domain owner on
  each product factor, and the localization-at-a-prime owner for the DVR conclusion;
- primitive data: the rings `A`, `B`, the algebra `A → B`, and the étale structure;
- derived API: the finite-product decomposition, the `IsDedekindRing B` bridge, and the
  discrete-valuation-ring conclusion for a nonzero maximal localization.

Layer triage:
- `source-facing`: `exists_finite_product_dedekindDomain_of_etale`;
- `core/canonical`: `IsDedekindRing`, `IsDedekindDomain`, and
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- `bridge/view`: the local discrete-valuation statement is a source-facing consequence for the
  canonical localization `Localization.AtPrime q.asIdeal`, rather than for an arbitrary chosen
  localization model.

Primitive-vs-derived refinement:
- a Dedekind-domain factor already carries its domain structure, so an extra public witness
  `∀ i, IsDomain (R i)` is redundant;
- the product decomposition is existential source content, so the theorem should keep only the
  Prop-level witness `Nonempty (B ≃+* Π i, R i)` rather than duplicating any extra wrapper API;
- `IsDedekindRing B` is the canonical owner-level conclusion for `B`, so it should be exposed
  directly instead of only through downstream consequences;
- the domain structure on a nonzero maximal localization of `B` is derived local data, so it
  should be internalized as an auxiliary instance rather than exposed in the public statement of
  the DVR theorem.
-/
section

variable {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
variable [CommRing B] [Algebra A B] [Algebra.Etale A B]

/-- Helper for Lemma 15.44.4: localizing a domain at the zero prime gives its fraction field, so
the localized Krull dimension is `0`. -/
private theorem ringKrullDim_localizationAtPrime_bot_eq_zero :
    ringKrullDim (Localization.AtPrime (⊥ : Ideal A)) = 0 := by
  -- Identify the zero-prime localization with the fraction field before reading off the
  -- zero-dimensional field case.
  letI : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance :
        IsLocalization ((⊥ : Ideal A).primeCompl)
          (Localization.AtPrime (⊥ : Ideal A)))
  let e : FractionRing A ≃ₐ[A] Localization.AtPrime (⊥ : Ideal A) :=
    FractionRing.algEquiv A (Localization.AtPrime (⊥ : Ideal A))
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact ringKrullDim_eq_zero_of_field (FractionRing A)

/-- Helper for Lemma 15.44.4: any source localization at a prime ideal equal to `0` has Krull
dimension `0`. -/
private theorem ringKrullDim_localizationAtPrime_eq_zero_of_eq_bot
    (p : Ideal A) [p.IsPrime] (hp : p = ⊥) :
    ringKrullDim (Localization.AtPrime p) = 0 := by
  -- Reduce to the explicit zero-prime computation above.
  subst hp
  simpa using ringKrullDim_localizationAtPrime_bot_eq_zero (A := A)

/-- Helper for Lemma 15.44.4: any source localization at a prime ideal equal to `0` is regular
local because it is the fraction field of `A`. -/
private theorem localizationAtPrime_isRegularLocalRing_of_eq_bot
    (p : Ideal A) [p.IsPrime] (hp : p = ⊥) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  -- After replacing `p` by `0`, the localization is the fraction field, hence a field and
  -- therefore a regular local ring.
  subst hp
  letI : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance :
        IsLocalization ((⊥ : Ideal A).primeCompl)
          (Localization.AtPrime (⊥ : Ideal A)))
  let _ : Field (Localization.AtPrime (⊥ : Ideal A)) :=
    IsFractionRing.toField (A := A) (K := Localization.AtPrime (⊥ : Ideal A))
  infer_instance

/-- Helper for Lemma 15.44.4: when a prime of `B` contracts to `0` in `A`, the corresponding
localization of `B` has Krull dimension `0`. -/
private theorem ringKrullDim_localizationAtPrime_eq_zero_of_zero_contraction
    (q : PrimeSpectrum B) (hq : q.asIdeal.under A = ⊥) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
  -- Compare dimensions along the étale map and then simplify the contracted prime to `0`.
  have hsource :
      ringKrullDim (Localization.AtPrime (q.asIdeal.under A)) = 0 := by
    exact ringKrullDim_localizationAtPrime_eq_zero_of_eq_bot
      (A := A) (p := q.asIdeal.under A) hq
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under A)) := by
      symm
      exact ringKrullDim_localizationAtPrime_eq_of_etale (A := A) (B := B) q.asIdeal
    _ = 0 := hsource

/-- Helper for Lemma 15.44.4: a zero-contraction localization of an étale algebra is regular
local because it is étale over the field case on the source side. -/
private theorem localizationAtPrime_isRegularLocalRing_of_zero_contraction
    (q : PrimeSpectrum B) (hq : q.asIdeal.under A = ⊥) :
    IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  -- The source localization at the zero prime is a field, hence regular local, and Lemma `15.44.3`
  -- transports that regularity across the étale local map.
  have hsource' : IsRegularLocalRing (Localization.AtPrime (q.asIdeal.under A)) := by
    exact localizationAtPrime_isRegularLocalRing_of_eq_bot
      (A := A) (p := q.asIdeal.under A) hq
  have hiff :=
    localizationAtPrime_isRegularLocalRing_iff_of_etale (A := A) (B := B) q
  exact hiff.mp hsource'

/-- Helper for Lemma 15.44.4: when a prime of `B` contracts to `0` in `A`, the corresponding
localization of `B` is a field. -/
private theorem localizationAtPrime_isField_of_zero_contraction
    (q : PrimeSpectrum B) (hq : q.asIdeal.under A = ⊥) :
    IsField (Localization.AtPrime q.asIdeal) := by
  let R := Localization.AtPrime q.asIdeal
  letI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R q.asIdeal
  have hregular : IsRegularLocalRing R :=
    localizationAtPrime_isRegularLocalRing_of_zero_contraction (A := A) (B := B) q hq
  have hdim : ringKrullDim R = 0 :=
    ringKrullDim_localizationAtPrime_eq_zero_of_zero_contraction (A := A) (B := B) q hq
  letI : IsRegularLocalRing R := hregular
  have hspan' : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = 0 := by
    exact ((isRegularLocalRing_iff R).mp inferInstance).trans hdim
  have hspan : (IsLocalRing.maximalIdeal R).spanFinrank = 0 := by
    exact_mod_cast hspan'
  have hfg : (IsLocalRing.maximalIdeal R).FG := by
    exact Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R)
  have hmax : IsLocalRing.maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hspan
  -- A local ring with zero maximal ideal is a field.
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax

/-- Helper for Lemma 15.44.4: when a prime of `B` contracts to a nonzero prime of the Dedekind
domain `A`, the corresponding localization of `B` is a discrete valuation ring. -/
private theorem localizationAtPrime_isDiscreteValuationRing_of_nonzero_contraction
    (q : PrimeSpectrum B) (hq : q.asIdeal.under A ≠ ⊥) :
    ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let Aq := Localization.AtPrime (q.asIdeal.under A)
  let Bq := Localization.AtPrime q.asIdeal
  have hsourceDvr : IsDiscreteValuationRing Aq := by
    simpa [Aq] using
      (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq Aq)
  have hsourceRegDim : IsRegularLocalRing Aq ∧ ringKrullDim Aq = 1 := by
    exact
      (discreteValuationRing_iff_regularLocalRing_dim_one (A := Aq)).mp
        ⟨inferInstance, hsourceDvr⟩
  have htargetRegular : IsRegularLocalRing Bq := by
    exact
      (localizationAtPrime_isRegularLocalRing_iff_of_etale (A := A) (B := B) q).mp
        hsourceRegDim.1
  have htargetDim : ringKrullDim Bq = 1 := by
    calc
      ringKrullDim Bq = ringKrullDim Aq := by
        symm
        simpa [Aq, Bq] using
          ringKrullDim_localizationAtPrime_eq_of_etale (A := A) (B := B) q.asIdeal
      _ = 1 := hsourceRegDim.2
  have htargetDvr : ∃ (_ : IsDomain Bq), IsDiscreteValuationRing Bq := by
    exact
      (discreteValuationRing_iff_regularLocalRing_dim_one (A := Bq)).mpr
        ⟨htargetRegular, htargetDim⟩
  exact htargetDvr

/-- Helper for Lemma 15.44.4: every prime localization of an étale algebra over a Dedekind domain
is either a field or a discrete valuation ring, according to whether the contracted prime is `0`
or nonzero. -/
private theorem localizationAtPrime_field_or_dvr_of_etale
    (q : PrimeSpectrum B) (p : Ideal A) (hp : q.asIdeal.under A = p) :
    IsField (Localization.AtPrime q.asIdeal) ∨
      ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  -- Route correction: split on the contracted prime in `A`; the zero-contraction branch is a
  -- field, while the nonzero branch is a DVR.
  by_cases hq : p = ⊥
  · exact Or.inl <|
      localizationAtPrime_isField_of_zero_contraction q (hp.trans hq)
  · exact Or.inr <|
      localizationAtPrime_isDiscreteValuationRing_of_nonzero_contraction
        q (by
          intro hbot
          exact hq (hp.symm ▸ hbot))

/-- Helper for Lemma 15.44.4: every prime localization of an étale algebra over a Dedekind domain
is a domain. -/
private theorem localizationAtPrime_isDomain_of_etale
    (q : PrimeSpectrum B) (p : Ideal A) (hp : q.asIdeal.under A = p) :
    IsDomain (Localization.AtPrime q.asIdeal) := by
  rcases localizationAtPrime_field_or_dvr_of_etale q p hp with
      hfield | ⟨hdom, hdvr⟩
  · let _ : Field (Localization.AtPrime q.asIdeal) := hfield.toField
    exact inferInstance
  · let _ : IsDomain (Localization.AtPrime q.asIdeal) := hdom
    let _ : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := hdvr
    exact inferInstance

/-- Helper for Lemma 15.44.4: the prime localizations of an étale algebra over a Dedekind domain
are normal domains because each one is either a field or a discrete valuation ring. -/
private theorem isNormalRing_of_etale_local (_ : Ideal A := ⊥) : IsNormalRing B := by
  refine ⟨fun q ↦ ?_⟩
  rcases localizationAtPrime_field_or_dvr_of_etale q (q.asIdeal.under A) rfl with
      hfield | ⟨hdom, hdvr⟩
  · let _ : Field (Localization.AtPrime q.asIdeal) := hfield.toField
    exact ⟨inferInstance, inferInstance⟩
  · let _ : IsDomain (Localization.AtPrime q.asIdeal) := hdom
    let _ : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := hdvr
    exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 15.44.4: for a maximal ideal of `B` with zero contraction to `A`, the
corresponding localization is a field. -/
theorem localizationAtMaximal_isField_of_zero_contraction
    (q : MaximalSpectrum B) (hq : q.asIdeal.under A = ⊥) :
    IsField (Localization.AtPrime q.asIdeal) := by
  let q' : PrimeSpectrum B := ⟨q.asIdeal, inferInstance⟩
  -- The maximal case is a direct specialization of the prime-level zero-contraction branch.
  simpa using
    localizationAtPrime_isField_of_zero_contraction q' hq

/-- Helper for Lemma 15.44.4: for a maximal ideal of `B` with nonzero contraction to `A`, the
corresponding localization is a discrete valuation ring. -/
theorem localizationAtMaximal_isDiscreteValuationRing_of_nonzero_contraction
    (q : MaximalSpectrum B) (hq : q.asIdeal.under A ≠ ⊥) :
    ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let q' : PrimeSpectrum B := ⟨q.asIdeal, inferInstance⟩
  -- The maximal case is a direct specialization of the prime-level nonzero-contraction branch.
  obtain ⟨hdom, hdvr⟩ :=
    localizationAtPrime_isDiscreteValuationRing_of_nonzero_contraction
      q' hq
  exact ⟨by simpa using hdom, hdvr⟩

/-- Helper for Lemma 15.44.4: a prime of `B` with nonzero contraction to the Dedekind base is a
closed point because the residue-field extension over the contracted maximal ideal is algebraic. -/
private theorem prime_isMaximal_of_nonzero_contraction
    (q : PrimeSpectrum B) (hq : q.asIdeal.under A ≠ ⊥) :
    q.asIdeal.IsMaximal := by
  let m : Ideal A := q.asIdeal.under A
  have hm : m.IsMaximal := by
    -- Over a Dedekind domain, every nonzero prime ideal is maximal.
    simpa [m] using
      Ideal.IsPrime.isMaximal (R := A) (p := q.asIdeal.under A)
        (h := inferInstance) (hp := hq)
  letI : m.IsMaximal := hm
  letI : q.asIdeal.LiesOver m := Ideal.over_under q.asIdeal
  have hfinite :
      Module.Finite m.ResidueField q.asIdeal.ResidueField := by
    -- The source-faithful residue-field finiteness comes from the étale-away neighborhood `g = 1`.
    exact
      (residueField_finite_and_separable_of_exists_etale_away
        (R := A) (S := B) q.asIdeal
        ⟨1, by
            simpa [Ideal.ne_top_iff_one] using
              (Ideal.IsPrime.ne_top (inferInstance : q.asIdeal.IsPrime)),
          inferInstance⟩).1
  letI : Module.Finite m.ResidueField q.asIdeal.ResidueField := hfinite
  letI : Algebra.IsAlgebraic m.ResidueField q.asIdeal.ResidueField :=
    Algebra.IsAlgebraic.of_finite m.ResidueField q.asIdeal.ResidueField
  -- Lemma `10.35.9` upgrades algebraicity of the residue-field extension to maximality of `q`.
  simpa [m] using
    isMaximal_of_liesOver_of_isAlgebraic_residueField
      (R := A) (S := B) m q.asIdeal

/-- Helper for Lemma 15.44.4: the local field-or-DVR analysis already proves that an étale
algebra over a Dedekind domain is a finite product of normal domains. -/
private theorem normal_domain_product_of_etale
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] :
    ∃ (ι : Type v) (_ : Finite ι) (R : ι → Type v)
      (_ : ∀ i, CommRing (R i)) (_ : B ≃+* ∀ i, R i),
      (∀ i, IsDomain (R i)) ∧ ∀ i, IsIntegrallyClosed (R i) := by
  -- Route correction: instead of proving `Ring.DimensionLEOne B` globally first, split `B`
  -- using the normal-ring TFAE and defer dimension arguments to the domain factors.
  have hnormal : IsNormalRing B := by
    simpa using (isNormalRing_of_etale_local (A := A) (B := B) (⊥ : Ideal A))
  letI : IsNormalRing B := hnormal
  letI : Algebra.FinitePresentation A B := inferInstance
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let _ : Fintype (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).fintype
  -- The finite-product clause is exactly the third entry in the normal-ring TFAE.
  exact
    ((normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains (R := B)).out 0 2).mp
      hnormal

/-- Helper for Lemma 15.44.4: in a domain, if the localization at a prime is already a field,
then the prime was the zero ideal. -/
private theorem prime_eq_bot_of_isField_localizationAtPrime_of_domain
    {R : Type v} [CommRing R] [IsDomain R] (q : PrimeSpectrum R)
    (hfield : IsField (Localization.AtPrime q.asIdeal)) :
    q.asIdeal = ⊥ := by
  let K := Localization.AtPrime q.asIdeal
  letI : IsField K := hfield
  letI : IsLocalRing K := IsLocalization.AtPrime.isLocalRing K q.asIdeal
  have hmax : IsLocalRing.maximalIdeal K = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  ext x
  constructor
  · intro hx
    -- Elements of `q` map into the maximal ideal of the localization, which vanishes in a field.
    have hxmap : algebraMap R K x ∈ IsLocalRing.maximalIdeal K := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal K]
      exact Ideal.mem_map_of_mem _ hx
    have hxzero : algebraMap R K x = 0 := by
      simpa [hmax] using hxmap
    exact (IsLocalization.to_map_eq_zero_iff K q.asIdeal.primeCompl_le_nonZeroDivisors).mp hxzero
  · intro hx
    -- Conversely the zero ideal is contained in every prime ideal.
    have hx0 : x = 0 := by
      simpa using hx
    simp [hx0]

/-- Helper for Lemma 15.44.4: localizing along a pulled-back prime is compatible with a ring
equivalence. -/
private noncomputable def localizationAtPrime_ringEquiv_of_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : PrimeSpectrum S) :
    Localization.AtPrime (Ideal.comap e.toRingHom q.asIdeal) ≃+*
      Localization.AtPrime q.asIdeal := by
  have hPrimeCompl :
      Submonoid.map e.toMonoidHom (Ideal.comap e.toRingHom q.asIdeal).primeCompl =
        q.asIdeal.primeCompl := by
    -- The complement of the pulled-back prime is transported exactly by the equivalence.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      exact hx hy
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hx
      exact hy (by simpa using hx)
  -- Once the prime complements agree, the universal property of localization gives the comparison.
  exact
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime (Ideal.comap e.toRingHom q.asIdeal))
      (Localization.AtPrime q.asIdeal) e hPrimeCompl

/-- Helper for Lemma 15.44.4: if the pulled-back prime on `B` contracts to `0` in `A`, then the
corresponding localization of a product factor is a field. -/
private theorem factor_localization_isField_of_zero_contraction
    {ι : Type v} [Finite ι] {R : ι → Type v} [∀ i, CommRing (R i)]
    (e : B ≃+* ∀ j, R j) (i : ι) (P : PrimeSpectrum (R i))
    (hqB :
      (PrimeSpectrum.comap e.toRingHom
        (PrimeSpectrum.comap (Pi.evalRingHom R i) P)).asIdeal.under A = ⊥) :
    IsField (Localization.AtPrime P.asIdeal) := by
  let qPi : PrimeSpectrum (∀ j, R j) := PrimeSpectrum.comap (Pi.evalRingHom R i) P
  let qB : PrimeSpectrum B := PrimeSpectrum.comap e.toRingHom qPi
  have hqB' : qB.asIdeal.under A = ⊥ := by
    simpa [qB, qPi] using hqB
  have hfieldB : IsField (Localization.AtPrime qB.asIdeal) :=
    localizationAtPrime_isField_of_zero_contraction (A := A) (B := B) qB hqB'
  let eB :
      Localization.AtPrime qB.asIdeal ≃+* Localization.AtPrime qPi.asIdeal :=
    localizationAtPrime_ringEquiv_of_comap e qPi
  have hfieldPi : IsField (Localization.AtPrime qPi.asIdeal) := by
    -- Move the field structure across the localization equivalence induced by `e`.
    exact eB.symm.toMulEquiv.isField hfieldB
  let ePi :
      Localization.AtPrime qPi.asIdeal ≃+* Localization.AtPrime P.asIdeal := by
    -- The product-side localization reduces to the chosen factor via the evaluation map.
    simpa [qPi, PrimeSpectrum.comap_asIdeal] using
      (RingEquiv.ofBijective
        (Localization.AtPrime.mapPiEvalRingHom P.asIdeal)
        (Localization.AtPrime.mapPiEvalRingHom_bijective P.asIdeal) :
          Localization.AtPrime (Ideal.comap (Pi.evalRingHom R i) P.asIdeal) ≃+*
            Localization.AtPrime P.asIdeal)
  -- Transport the field structure one more time to the factor localization.
  exact ePi.symm.toMulEquiv.isField hfieldPi

/-- Helper for Lemma 15.44.4: a nonzero prime in a domain factor of the product decomposition is
maximal. -/
private theorem factor_prime_isMaximal_of_nonzero
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    {ι : Type v} [Finite ι] {R : ι → Type v} [∀ i, CommRing (R i)]
    (e : B ≃+* ∀ j, R j) (hdom : ∀ j, IsDomain (R j))
    (i : ι) (P : PrimeSpectrum (R i)) (hP : P.asIdeal ≠ ⊥) :
    P.asIdeal.IsMaximal := by
  letI : IsDomain (R i) := hdom i
  let qPi : PrimeSpectrum (∀ j, R j) := PrimeSpectrum.comap (Pi.evalRingHom R i) P
  let qB : PrimeSpectrum B := PrimeSpectrum.comap e.toRingHom qPi
  by_cases hqB : qB.asIdeal.under A = ⊥
  · -- Route correction: in the zero-contraction branch, the factor localization becomes a field,
    -- which forces the prime of the domain factor to be the zero ideal.
    have hfieldP : IsField (Localization.AtPrime P.asIdeal) :=
      factor_localization_isField_of_zero_contraction
        (A := A) (B := B) e i P hqB
    have hbot : P.asIdeal = ⊥ :=
      prime_eq_bot_of_isField_localizationAtPrime_of_domain P hfieldP
    exact False.elim (hP hbot)
  · -- In the nonzero-contraction branch, maximality comes from the pulled-back prime on `B`
    -- and is transported first across `e`, then across the evaluation map to the factor.
    have hqBMax : qB.asIdeal.IsMaximal :=
      prime_isMaximal_of_nonzero_contraction (A := A) (B := B) qB hqB
    have hkerE : RingHom.ker e.toRingHom ≤ qB.asIdeal := by
      simpa [qB, PrimeSpectrum.comap_asIdeal, RingHom.ker_eq_comap_bot] using
        (Ideal.comap_mono (f := e.toRingHom) bot_le :
          Ideal.comap e.toRingHom ⊥ ≤ Ideal.comap e.toRingHom qPi.asIdeal)
    have hqPiMap :
        (Ideal.map e.toRingHom qB.asIdeal).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le
        (f := e.toRingHom) e.surjective hkerE
    have hqPiEq : Ideal.map e.toRingHom qB.asIdeal = qPi.asIdeal := by
      simpa [qB, PrimeSpectrum.comap_asIdeal] using
        (Ideal.map_comap_of_surjective e.toRingHom e.surjective qPi.asIdeal)
    have hqPiMax : qPi.asIdeal.IsMaximal := by
      rw [← hqPiEq]
      exact hqPiMap
    have hkerEval : RingHom.ker (Pi.evalRingHom R i) ≤ qPi.asIdeal := by
      simpa [qPi, PrimeSpectrum.comap_asIdeal, RingHom.ker_eq_comap_bot] using
        (Ideal.comap_mono (f := Pi.evalRingHom R i) bot_le :
          Ideal.comap (Pi.evalRingHom R i) ⊥ ≤
            Ideal.comap (Pi.evalRingHom R i) P.asIdeal)
    have hPMap :
        (Ideal.map (Pi.evalRingHom R i) qPi.asIdeal).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le
        (f := Pi.evalRingHom R i) (Function.surjective_eval i) hkerEval
    have hPEq : Ideal.map (Pi.evalRingHom R i) qPi.asIdeal = P.asIdeal := by
      simpa [qPi, PrimeSpectrum.comap_asIdeal] using
        (Ideal.map_comap_of_surjective
          (Pi.evalRingHom R i) (Function.surjective_eval i) P.asIdeal)
    simpa [hPEq] using hPMap

/-- Helper for Lemma 15.44.4: once `B` is split into normal domain factors, it remains to prove
that every nonzero prime of each factor is maximal. -/
private theorem factor_isDedekindDomain_of_normal_product_equiv
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    {ι : Type v} [Finite ι] {R : ι → Type v} [∀ i, CommRing (R i)]
    (e : B ≃+* ∀ i, R i) (hdom : ∀ i, IsDomain (R i))
    (hintegrallyClosed : ∀ i, IsIntegrallyClosed (R i)) :
    ∀ i, IsDedekindDomain (R i) := by
  intro i
  letI : Algebra.FinitePresentation A B := inferInstance
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  letI : IsDomain (R i) := hdom i
  have hNoetherianProd : IsNoetherianRing (∀ j, R j) := by
    -- Transport Noetherianity from `B` across the product equivalence.
    exact isNoetherianRing_of_ringEquiv B e
  have hNoetherian : IsNoetherianRing (R i) := by
    let _ : IsNoetherianRing (∀ j, R j) := hNoetherianProd
    -- Each factor is a quotient of the finite product via the evaluation map.
    exact isNoetherianRing_of_surjective (∀ j, R j) (R i) (Pi.evalRingHom R i)
      (Function.surjective_eval i)
  have hDimensionLEOne : Ring.DimensionLEOne (R i) := by
    refine ⟨fun {P} hP hprime ↦ ?_⟩
    let P' : PrimeSpectrum (R i) := ⟨P, hprime⟩
    -- Route correction: the factor-local helper now packages the source split on the pulled-back
    -- prime of `B`, so the dimension bound is exactly the maximality statement we just proved.
    simpa using
      factor_prime_isMaximal_of_nonzero
        (A := A) (B := B) e hdom i P' hP
  letI : IsNoetherianRing (R i) := hNoetherian
  letI : Ring.DimensionLEOne (R i) := hDimensionLEOne
  have hIntegralClosure :
      ∀ {x : FractionRing (R i)}, IsIntegral (R i) x →
        ∃ y, (algebraMap (R i) (FractionRing (R i))) y = x :=
    (isIntegrallyClosed_iff (FractionRing (R i))).mp (hintegrallyClosed i)
  -- With the domain, Noetherian, dimension-one, and integral-closure owners in place, the
  -- canonical Dedekind-domain criterion closes the factor.
  exact
    (isDedekindDomain_iff (R i) (FractionRing (R i))).2
      ⟨inferInstance, hNoetherian, hDimensionLEOne, fun {_} hx ↦ hIntegralClosure hx⟩

/-- Helper for Lemma 15.44.4: explicit-parameter wrapper for the factor-first proof. -/
private theorem exists_finite_product_dedekindDomain_of_etale_explicit
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] :
    ∃ (ι : Type v) (_ : Finite ι) (R : ι → Type v)
      (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDedekindDomain (R i)),
      Nonempty (B ≃+* Π i, R i) := by
  obtain ⟨ι, hfin, R, hComm, e, hdom, hintegrallyClosed⟩ :=
    normal_domain_product_of_etale (A := A) (B := B)
  have hDedekind : ∀ i, IsDedekindDomain (R i) := by
    -- The structural split is already done; only the factorwise Dedekind package remains.
    exact
      factor_isDedekindDomain_of_normal_product_equiv
        (A := A) (B := B) e hdom hintegrallyClosed
  exact ⟨ι, hfin, R, hComm, hDedekind, ⟨e⟩⟩

/-- Helper for Lemma 15.44.4: reindexing by `ULift` and lifting each factor ring preserves the
same product ring. -/
private noncomputable def ulift_pi_ringEquiv
    {ι : Type v} {R : ι → Type v} [∀ i, CommRing (R i)] :
    (Π i, R i) ≃+* Π j : ULift.{u} ι, ULift.{u} (R j.down) :=
  ((RingEquiv.piCongrLeft (fun i : ι ↦ R i) (Equiv.ulift : ULift.{u} ι ≃ ι)).symm).trans <|
    RingEquiv.piCongrRight fun j : ULift.{u} ι ↦
      (ULift.ringEquiv.symm : R j.down ≃+* ULift.{u} (R j.down))

/-- Helper for Lemma 15.44.4: the Dedekind-domain owner transports across `ULift`. -/
private theorem ulift_isDedekindDomain
    {R : Type v} [CommRing R] [IsDedekindDomain R] :
    IsDedekindDomain (ULift.{u} R) := by
  let e : ULift.{u} R ≃+* R := ULift.ringEquiv
  have hNoetherian : IsNoetherianRing (ULift.{u} R) :=
    isNoetherianRing_of_ringEquiv R e.symm
  have hDimensionLEOne : Ring.DimensionLEOne (ULift.{u} R) :=
    Ring.DimensionLEOne.of_ringEquiv (A := R) e
  have hIntegrallyClosed : IsIntegrallyClosed (ULift.{u} R) := by
    -- Transport integrally closedness across the canonical equivalence with the original ring.
    exact IsIntegrallyClosed.of_equiv (ULift.ringEquiv.symm : R ≃+* ULift.{u} R)
  have hDedekindRing : IsDedekindRing (ULift.{u} R) := by
    -- The standard owner package is exactly Noetherianity, dimension at most one, and integral
    -- closedness in the canonical fraction field.
    exact
      (isDedekindRing_iff (A := ULift.{u} R) (K := FractionRing (ULift.{u} R))).2
        ⟨hNoetherian, hDimensionLEOne,
          fun {_} hx ↦
            (isIntegrallyClosed_iff (FractionRing (ULift.{u} R))).mp hIntegrallyClosed hx⟩
  letI : IsDomain (ULift.{u} R) := e.injective.isDomain e.toRingHom
  letI : IsDedekindRing (ULift.{u} R) := hDedekindRing
  exact inferInstance

/-- Helper for Lemma 15.44.4: a product decomposition stays nonempty after the `ULift`
reindexing/lifting equivalence. -/
private theorem nonempty_ringEquiv_ulift_pi_of_nonempty_ringEquiv_pi
    {C : Type v} [CommRing C] {ι : Type v} {R : ι → Type v} [∀ i, CommRing (R i)] :
    Nonempty (C ≃+* Π i, R i) →
      Nonempty (C ≃+* Π j : ULift.{u} ι, ULift.{u} (R j.down)) := by
  intro h
  rcases h with ⟨e⟩
  -- Compose the given product equivalence with the canonical `ULift` adapter.
  exact ⟨e.trans ulift_pi_ringEquiv⟩

-- Proof sketch: by Lemmas `15.44.2` and `15.44.3`, every localization `B_q` at a maximal ideal
-- has the same dimension and regularity as the corresponding localization of the Dedekind domain
-- `A`, hence is a discrete valuation ring via Algebra, Lemma `10.119.7`. Therefore `B` is a
-- Noetherian normal ring of dimension `1`, and Algebra, Lemmas `10.37.16` and `10.120.17` split
-- it as a finite product of Dedekind domains.
/-- Lemma 15.44.4: if `A → B` is an étale ring map and `A` is a Dedekind domain, then `B` is a
finite product of Dedekind domains. -/
@[stacks 0AP2]
theorem exists_finite_product_dedekindDomain_of_etale
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] :
    ∃ (ι : Type (max u v)) (_ : Finite ι) (R : ι → Type (max u v))
      (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDedekindDomain (R i)),
      Nonempty (B ≃+* Π i, R i) := by
  -- Route correction: the explicit theorem already gives the factor-first decomposition in
  -- universe `v`; only the final packaging into `Type (max u v)` remains.
  obtain ⟨ι, hfin, R, hComm, hDedekind, he⟩ :=
    exists_finite_product_dedekindDomain_of_etale_explicit (A := A) (B := B)
  letI : Finite ι := hfin
  letI : ∀ i, CommRing (R i) := hComm
  let R' : ULift.{u} ι → Type (max u v) := fun j ↦ ULift.{u} (R j.down)
  have hDedekind' : ∀ j, IsDedekindDomain (R' j) := by
    intro j
    -- Transport each factor owner separately across the canonical `ULift` equivalence.
    letI : IsDedekindDomain (R j.down) := hDedekind j.down
    simpa [R'] using (ulift_isDedekindDomain (R := R j.down))
  have he' : Nonempty (B ≃+* Π j : ULift.{u} ι, R' j) :=
    nonempty_ringEquiv_ulift_pi_of_nonempty_ringEquiv_pi
      (C := B) (R := R) he
  -- The lifted family now lives in the required universe, with the same finite-product witness.
  exact ⟨ULift.{u} ι, inferInstance, R', (fun _ ↦ inferInstance), hDedekind', he'⟩

-- Route correction: under mathlib's `IsDedekindDomain`, fields are Dedekind domains. Then
-- `A := K` and `B := K × K` give an étale counterexample to the DVR conclusion below, since the
-- localization at the nonzero maximal ideal `K × ⊥` is the field `K`, not a DVR.
-- Proof sketch: split on whether the contracted prime `q ∩ A` is zero. In the zero-contraction
-- branch the localization is a field; in the nonzero-contraction branch the source localization is
-- a DVR and Lemmas `15.44.2` and `15.44.3` transport the regular-local dimension-one package to
-- `B_q`.
/-- Helper for Lemma 15.44.4: the localization of an étale algebra over a Dedekind domain at a
maximal ideal is either a field or a discrete valuation ring, according to the contraction to the
base. -/
theorem localizationAtMaximal_field_or_dvr_of_etale
    (q : MaximalSpectrum B) (p : Ideal A) (hp : q.asIdeal.under A = p) :
    IsField (Localization.AtPrime q.asIdeal) ∨
      ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  by_cases hq : p = ⊥
  · exact Or.inl <|
      localizationAtMaximal_isField_of_zero_contraction q (hp.trans hq)
  · exact Or.inr <|
      localizationAtMaximal_isDiscreteValuationRing_of_nonzero_contraction
        q (by
          intro hbot
          exact hq (hp.symm ▸ hbot))

end
