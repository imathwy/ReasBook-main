import Mathlib
import StacksProject_2024.Chap10.Definition_10_67_1
import StacksProject_2024.Chap10.Lemma_10_157_2
import StacksProject_2024.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality
import StacksProject_2024.Chap10.Lemma_10_60_11
import StacksProject_2024.Chap10.Lemma_10_63_19
import StacksProject_2024.Chap10.Definition_10_64_1
import StacksProject_2024.Chap10.Lemma_10_64_2
import StacksProject_2024.Chap10.Lemma_10_72_7
import StacksProject_2024.Chap10.Proposition_10_63_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise ENat

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/- Domain-style sampling:
- primary domain: commutative algebra of Noetherian normal domains, with principal quotients,
  embedded associated primes, fraction fields, principal submodules in the fraction field, and
  height-one localizations;
- sampled owner/bridge declarations:
  `embeddedAssociatedPrimes`,
  `embeddedAssociatedPrimes_eq_empty_iff`,
  `Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
  `Submodule.comap`,
  `Algebra.linearMap`,
  `moduleHeightOneLocalizationIntersection`,
  and `(algebraMap A K).range` as the canonical image owner used in `Lemma_10_50_11`;
- best owner abstractions:
  `embeddedAssociatedPrimes R M` for the no-embedded-primes clause,
  `(algebraMap R K).range` for image-membership in ambient fraction fields/localizations,
  `{ p : PrimeSpectrum R // p.asIdeal.height = 1 }` for the height-one-prime quantification,
  and the contracted principal `R`-submodule
  `((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)` for `R ∩ xR`;
- primitive data vs. derived API:
  the quotient modules, the principal `R`-submodule `R ∙ x ⊆ FractionRing R`, and the canonical
  algebra-map images are primitive here,
  while the older "every associated prime is minimal" packaging and `Set.range (algebraMap ...)`
  are bridge-level restatements that should not remain the public surface.

Source/core/bridge triage:
- `source-facing`: the three Stacks statements about principal quotients and height-one
  localization tests in a normal domain;
- `core/canonical`: `embeddedAssociatedPrimes`, `associatedPrimes`, `Ideal.comap`,
  `Submodule.comap`, the principal submodule owner `R ∙ x`, and ring-hom ranges;
- `bridge/view`: the height-one-prime subtype used to index those localizations and the
  membership criterion for the fraction field.
-/

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: the support of the principal quotient `R / aR` is exactly the zero
locus of the principal ideal `(a)`. -/
lemma support_quotient_span_singleton_le_iff
    (a : R) (p : PrimeSpectrum R) :
    p ∈ Module.support R (R ⧸ Ideal.span ({a} : Set R)) ↔
      Ideal.span ({a} : Set R) ≤ p.asIdeal := by
  -- Rewrite the support through the annihilator of the quotient module.
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.mem_zeroLocus]
  exact Iff.rfl

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: once `R / aR` has no embedded primes, any associated prime of the
quotient is minimal over `(a)`. -/
lemma associatedPrime_quotient_mem_minimalPrimes_span_singleton
    {a : R}
    (hno_embedded : embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅)
    {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ Ideal.span ({a} : Set R))) :
    p ∈ (Ideal.span ({a} : Set R)).minimalPrimes := by
  let A : Type u := R ⧸ Ideal.span ({a} : Set R)
  have hp_min_assoc : Minimal (· ∈ associatedPrimes R A) p :=
    (embeddedAssociatedPrimes_eq_empty_iff (R := R) (M := A)).1 hno_embedded p hp
  let pPoint : PrimeSpectrum R := ⟨p, hp.1⟩
  have hp_support : pPoint ∈ Module.support R A := by
    simpa [pPoint] using IsAssociatedPrime.mem_support hp
  have ha_le_p : Ideal.span ({a} : Set R) ≤ p := by
    exact (support_quotient_span_singleton_le_iff (R := R) a pPoint).1 hp_support
  refine ⟨⟨hp.1, ha_le_p⟩, ?_⟩
  intro q hq hqp
  letI : q.IsPrime := hq.1
  obtain ⟨r, hr, hrq⟩ := Ideal.exists_minimalPrimes_le hq.2
  have hr_assoc : r ∈ associatedPrimes R A := by
    have hr_ann : r ∈ (Module.annihilator R A).minimalPrimes := by
      simpa [A, Ideal.annihilator_quotient] using hr
    exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      (R := R) (M := A) hr_ann
  exact hp_min_assoc.2 hr_assoc (hrq.trans hqp) |>.trans hrq

omit [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: once `R / aR` has no embedded primes, each associated prime of the
quotient has height `1` provided `a ≠ 0`. -/
lemma associatedPrime_quotient_height_eq_one_of_nonzero
    {a : R} (ha : a ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅)
    {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ Ideal.span ({a} : Set R))) :
    p.height = 1 := by
  letI : p.IsPrime := hp.1
  have hp_min :
      p ∈ (Ideal.span ({a} : Set R)).minimalPrimes :=
    associatedPrime_quotient_mem_minimalPrimes_span_singleton
      (R := R) hno_embedded hp
  have hp_le_one : p.primeHeight ≤ 1 := by
    rw [← Ideal.height_eq_primeHeight]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span ({a} : Set R)) p hp_min
  have hp_ne_bot : p ≠ ⊥ := by
    intro hp_bot
    have ha_mem : a ∈ p := hp_min.1.2 (Ideal.subset_span (by simp))
    rw [hp_bot, Ideal.mem_bot] at ha_mem
    exact ha ha_mem
  have hbot_lt : (⊥ : Ideal R) < p := bot_lt_iff_ne_bot.mpr hp_ne_bot
  have hbot_height : (⊥ : Ideal R).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hp_ge_one : (1 : ℕ∞) ≤ p.primeHeight := by
    simpa [hbot_height] using
      Ideal.primeHeight_add_one_le_of_lt (I := (⊥ : Ideal R)) (J := p) hbot_lt
  have hp_eq_one : p.primeHeight = 1 := le_antisymm hp_le_one hp_ge_one
  simpa [Ideal.height_eq_primeHeight] using hp_eq_one

/-- Helper for Lemma 10.157.6: localizing `QuotSMulTop a R` at `p` agrees with quotienting the
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

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: if the principal generator is a unit, its quotient module is
trivial. -/
lemma quotSMulTop_subsingleton_of_isUnit {a : R} (ha : IsUnit a) :
    Subsingleton (QuotSMulTop a R) := by
  -- A unit already generates the whole module, so the quotient collapses.
  rw [Submodule.Quotient.subsingleton_iff]
  refine top_unique ?_
  intro x hx
  rcases ha with ⟨u, rfl⟩
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨(↑u⁻¹ : R) • x, by simp, ?_⟩
  simp

/-- Helper for Lemma 10.157.6: a finite subsingleton module over a Noetherian local ring has
infinite depth. -/
lemma moduleDepth_eq_top_of_subsingleton
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Subsingleton M] :
    moduleDepth A M = ⊤ := by
  -- The maximal ideal acts trivially on the unique element, so the depth is infinite by
  -- definition.
  have htop_eq_bot : (⊤ : Submodule A M) = ⊥ := by
    ext x
    simp [Subsingleton.elim x 0]
  have hsmul_bot : IsLocalRing.maximalIdeal A • (⊥ : Submodule A M) = ⊥ := by
    ext x
    simp
  have hsmul_top : IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (IsLocalRing.maximalIdeal A) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal A) M hsmul_top

/-- Helper for Lemma 10.157.6: a Noetherian normal local domain satisfies the depth lower bound
coming from `(S₂)`. -/
lemma local_normal_domain_depth_ge_min_two
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] :
    WithBot.some (moduleDepth A A : ℕ∞) ≥
      min (2 : WithBot ℕ∞) (ringKrullDim A) := by
  -- Reuse the same dimension trichotomy as in Serre's criterion for normality.
  by_cases hdim0 : ringKrullDim A = 0
  · -- In dimension `0`, the lower bound is immediate.
    simpa [hdim0]
  · by_cases hdim1 : ringKrullDim A = 1
    · -- In dimension `1`, a normal local domain is a DVR and hence Cohen-Macaulay.
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
    · -- Outside dimensions `0` and `1`, the Kollár trichotomy forces depth at least `2`.
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

/-- Helper for Lemma 10.157.6: over a Noetherian normal local domain, quotienting by a nonzero
element of the maximal ideal satisfies the local `(S₁)` depth bound. -/
lemma local_principal_quotSMulTop_depth_ge_min_one
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] {a : A} (ha : a ≠ 0) (ha_mem : a ∈ IsLocalRing.maximalIdeal A) :
    WithBot.some (moduleDepth A (QuotSMulTop a A) : ℕ∞) ≥
      min (1 : WithBot ℕ∞) (Module.supportDim A (QuotSMulTop a A)) := by
  have hreg : IsSMulRegular A a := IsSMulRegular.of_ne_zero ha
  have hdepth_drop :
      moduleDepth A (QuotSMulTop a A) = moduleDepth A A - 1 :=
    IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one (R := A) (M := A) hreg ha_mem
  have hsupport_drop :
      Module.supportDim A (QuotSMulTop a A) + 1 = Module.supportDim A A :=
    Module.supportDim_quotSMulTop_succ_eq_supportDim (M := A) hreg ha_mem
  have hdepth_A :
      WithBot.some (moduleDepth A A : ℕ∞) ≥
        min (2 : WithBot ℕ∞) (ringKrullDim A) :=
    local_normal_domain_depth_ge_min_two A
  -- Split according to the localized support dimension of the quotient.
  cases hq : Module.supportDim A (QuotSMulTop a A) with
  | bot =>
      simpa [hq]
  | coe qdim =>
      by_cases hqdim_zero : qdim = 0
      · -- Zero-dimensional support makes the `(S₁)` bound automatic.
        simpa [hq, hqdim_zero]
      · -- Positive support dimension raises the ambient dimension to at least `2`.
        have hqdim_ge_one : (1 : ℕ∞) ≤ qdim :=
          ENat.one_le_iff_ne_zero.2 hqdim_zero
        have hdim_ge_two : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by
          have hqdim_succ : (2 : ℕ∞) ≤ qdim + 1 := by
            calc
              (2 : ℕ∞) = 1 + 1 := by norm_num
              _ ≤ qdim + 1 := by
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hqdim_ge_one 1
          calc
            (2 : WithBot ℕ∞) ≤ (((qdim + 1 : ℕ∞) : WithBot ℕ∞)) := by
              exact WithBot.coe_le_coe.2 hqdim_succ
            _ = ringKrullDim A := by
              simpa [hq, Module.supportDim_self_eq_ringKrullDim] using hsupport_drop
        have hdepth_A_ge_two : (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A A : ℕ∞) := by
          simpa [min_eq_left hdim_ge_two] using hdepth_A
        have hdepth_A_ge_two' : (2 : ℕ∞) ≤ moduleDepth A A := by
          exact WithBot.coe_le_coe.mp (by simpa [WithBot.some_eq_coe] using hdepth_A_ge_two)
        have hdepth_quot_ne_zero : moduleDepth A (QuotSMulTop a A) ≠ 0 := by
          intro hzero
          have hdepth_A_le_one : moduleDepth A A ≤ 1 := by
            have htsub_zero : moduleDepth A A - 1 = 0 := by
              simpa [hdepth_drop] using hzero
            exact (tsub_eq_zero_iff_le).1 htsub_zero
          have : (2 : ℕ∞) ≤ 1 := le_trans hdepth_A_ge_two' hdepth_A_le_one
          norm_num at this
        have hdepth_quot_ge_one : (1 : ℕ∞) ≤ moduleDepth A (QuotSMulTop a A) :=
          ENat.one_le_iff_ne_zero.2 hdepth_quot_ne_zero
        have hdepth_quot_ge_one' :
            (1 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A (QuotSMulTop a A) : ℕ∞) := by
          simpa [WithBot.some_eq_coe] using hdepth_quot_ge_one
        have hmin_eq :
            min (1 : WithBot ℕ∞) ((qdim : ℕ∞) : WithBot ℕ∞) = 1 := by
          exact min_eq_left (WithBot.coe_le_coe.2 hqdim_ge_one)
        simpa [hq, hmin_eq] using hdepth_quot_ge_one'

/-- Helper for Lemma 10.157.6: the principal quotient `R / aR` satisfies `(S₁)` when `a ≠ 0`. -/
lemma quotient_span_singleton_serreConditionS_one_of_nonzero
    {a : R} (ha : a ≠ 0) :
    Module.SerreConditionS R (R ⧸ Ideal.span ({a} : Set R)) 1 := by
  -- Route correction: prove `(S₁)` on the owner quotient `QuotSMulTop a R`, then transport the
  -- result across the canonical equivalence with `R / aR`.
  have hquot :
      Module.SerreConditionS R (QuotSMulTop a R) 1 := by
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    let A := Localization.AtPrime p.asIdeal
    let e := localized_quotSMulTop_atPrime_equiv (R := R) p a
    by_cases ha_mem : a ∈ p.asIdeal
    · -- When `a ∈ p`, identify the localized quotient with `A / aA` and apply the local depth
      -- estimate coming from the normal local-domain case.
      have ha_loc :
          algebraMap R A a ∈ IsLocalRing.maximalIdeal A := by
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p.asIdeal a).2 ha_mem
      letI : IsDomain A := isDomain_localizationAtPrime p
      letI : IsIntegrallyClosed A := isIntegrallyClosed_localizationAtPrime p
      have hlocal :
          WithBot.some
              (moduleDepth A (QuotSMulTop (algebraMap R A a) A) : ℕ∞) ≥
            min (1 : WithBot ℕ∞)
              (Module.supportDim A (QuotSMulTop (algebraMap R A a) A)) :=
        local_principal_quotSMulTop_depth_ge_min_one
          A
          (show algebraMap R A a ≠ 0 by
            intro hzero
            apply ha
            apply (IsLocalization.injective A p.asIdeal.primeCompl_le_nonZeroDivisors)
            simpa using hzero)
          ha_loc
      have hdepth_eq :
          moduleDepth A (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) =
            moduleDepth A (QuotSMulTop (algebraMap R A a) A) := by
        simpa [A] using moduleDepth_eq_of_equiv (R := A) (e := e)
      have hsupport_eq :
          Module.supportDim A (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) =
            Module.supportDim A (QuotSMulTop (algebraMap R A a) A) := by
        simpa [A] using Module.supportDim_eq_of_equiv e
      rw [hdepth_eq, hsupport_eq]
      exact hlocal
    · -- When `a ∉ p`, its image is a unit in `A`, so the localized quotient is zero.
      have ha_loc_not_mem :
          algebraMap R A a ∉ IsLocalRing.maximalIdeal A := by
        intro ha_loc
        exact ha_mem ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p.asIdeal a).1 ha_loc)
      have ha_unit : IsUnit (algebraMap R A a) := by
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using
          ha_loc_not_mem
      letI :
          Subsingleton (QuotSMulTop (algebraMap R A a) A) :=
        quotSMulTop_subsingleton_of_isUnit (R := A) ha_unit
      letI :
          Subsingleton (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) :=
        e.injective.subsingleton
      have hsupport :
          Module.supportDim A (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) = ⊥ :=
        Module.supportDim_eq_bot_of_subsingleton (R := A)
          (M := LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R))
      rw [hsupport]
      simp
  -- Transport the owner proof from `QuotSMulTop a R` back to the principal quotient ring.
  let ePrincipal : QuotSMulTop a R ≃ₗ[R] (R ⧸ Ideal.span ({a} : Set R)) := by
    -- Rewrite the principal ideal quotient as the quotient by `a • ⊤`.
    refine Submodule.quotEquivOfEq (a • (⊤ : Submodule R R)) (Ideal.span ({a} : Set R)) ?_
    simpa using (Submodule.ideal_span_singleton_smul a (⊤ : Submodule R R)).symm
  letI : Module.SerreConditionS R (QuotSMulTop a R) 1 := hquot
  exact Module.SerreConditionS.of_linearEquiv ePrincipal

/-- Lemma 10.157.6 (1): for a nonzero element `a` of a Noetherian normal domain `R`, the quotient
`R / aR` has no embedded associated primes, and every associated prime of `R / aR` has height
`1`. -/
-- Proof sketch: Serre's criterion gives `(S_2)` for `R`, and Lemma `10.72.6` descends this to
-- `(S_1)` for `R / aR`. Then Lemma `10.157.2` removes embedded primes, while Lemma `10.60.11`
-- shows that minimal primes over `(a)` have height at most `1`; since `a ≠ 0` in a domain, any
-- associated prime of `R / aR` is nonzero and hence has height exactly `1`.
@[stacks 031T]
theorem quotient_span_singleton_has_no_embedded_primes_and_associatedPrimes_height_eq_one
    {a : R} (ha : a ≠ 0) :
    embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅ ∧
      ∀ p ∈ associatedPrimes R (R ⧸ Ideal.span ({a} : Set R)), p.height = 1 := by
  -- First prove the quotient has no embedded primes via the `(S₁)` criterion.
  have hS1 :
      Module.SerreConditionS R (R ⧸ Ideal.span ({a} : Set R)) 1 :=
    quotient_span_singleton_serreConditionS_one_of_nonzero (R := R) ha
  have hno_embedded :
      embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅ :=
    (Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one
      (R := R) (M := R ⧸ Ideal.span ({a} : Set R))).2 hS1
  refine ⟨hno_embedded, ?_⟩
  intro p hp
  -- Then each associated prime is minimal over `(a)`, hence height one.
  exact associatedPrime_quotient_height_eq_one_of_nonzero
    (R := R) ha hno_embedded hp

-- Lemma 10.157.6 (2): an element of the fraction field of a Noetherian normal domain belongs to
-- `R` exactly when it belongs to every localization `R_𝔭` at a height-one prime `𝔭`.
-- Proof sketch: write the element as `b / a` with `a ≠ 0`. Apply part (1) to identify the
-- associated primes of `R / aR` with height-one primes and then use Lemma `10.63.19` in the cyclic
-- module `R / aR` to test membership in `aR` after localizing at those primes.
omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: for a fraction `a / b`, membership in the height-one localization
range is equivalent to vanishing of the localized class of `a` in the principal quotient `R / bR`.
-/
lemma fraction_mem_localization_range_iff_localized_quotientClass_zero
    {a b : R} (hb : b ≠ 0) (p : PrimeSpectrum R) :
    algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b ∈
        (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing R)).range ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl (R ⧸ Ideal.span ({b} : Set R))
        (Ideal.Quotient.mk (Ideal.span ({b} : Set R)) a) = 0 := by
  let K := FractionRing R
  let I : Ideal R := Ideal.span ({b} : Set R)
  let hprimeCompl :
      p.asIdeal.primeCompl ≤ nonZeroDivisors R := p.asIdeal.primeCompl_le_nonZeroDivisors
  let bNZD : nonZeroDivisors R := ⟨b, mem_nonZeroDivisors_iff_ne_zero.2 hb⟩
  constructor
  · rintro ⟨y, hy⟩
    rcases IsLocalization.exists_mk'_eq p.asIdeal.primeCompl y with ⟨c, s, rfl⟩
    -- Rewrite the localized element as the fraction `c / s` inside the global fraction field.
    have hy' :
        IsLocalization.mk' K c ⟨s.1, hprimeCompl s.2⟩ =
          algebraMap R K a / algebraMap R K b := by
      calc
        IsLocalization.mk' K c ⟨s.1, hprimeCompl s.2⟩ =
            algebraMap (Localization.AtPrime p.asIdeal) K
              (IsLocalization.mk' (Localization.AtPrime p.asIdeal) c s) := by
              exact IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le
                (S := Localization.AtPrime p.asIdeal) (T := K) (h := hprimeCompl) c s
        _ = algebraMap R K a / algebraMap R K b := hy
    have hsK : algebraMap R K s.1 ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hprimeCompl s.2)
    have hbK : algebraMap R K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors bNZD.2
    -- Cross-multiplication gives a denominator outside `p` that kills the quotient class.
    have hmul :
        algebraMap R K (c * b) = algebraMap R K (s.1 * a) := by
      rw [IsFractionRing.mk'_eq_div, div_eq_div_iff hsK hbK] at hy'
      simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using hy'
    have hs_mem : s.1 * a ∈ I := by
      change s.1 * a ∈ Ideal.span ({b} : Set R)
      rw [Ideal.mem_span_singleton']
      exact ⟨c, IsFractionRing.injective R K hmul⟩
    -- Route correction: use the localization kernel criterion directly instead of transporting
    -- through a larger quotient-localization equivalence.
    rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff]
    refine ⟨s.1, s.2, ?_⟩
    change Ideal.Quotient.mk I (s.1 * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hs_mem
  · intro hzero
    -- Read localized vanishing as a denominator outside `p` whose multiple lands in `(b)`.
    rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff] at hzero
    rcases hzero with ⟨s, hs, hs_zero⟩
    change Ideal.Quotient.mk I (s * a) = 0 at hs_zero
    rw [Ideal.Quotient.eq_zero_iff_mem] at hs_zero
    change s * a ∈ Ideal.span ({b} : Set R) at hs_zero
    rcases Ideal.mem_span_singleton'.1 hs_zero with ⟨c, hc⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime p.asIdeal) c ⟨s, hs⟩, ?_⟩
    have hfrac :
        IsLocalization.mk' K c ⟨s, hprimeCompl hs⟩ =
          IsLocalization.mk' K a bNZD := by
      rw [IsLocalization.mk'_eq_iff_eq']
      exact congrArg (algebraMap R K) <| by
        simpa [bNZD, mul_comm, mul_left_comm, mul_assoc] using hc
    -- Compare the chosen local representative with the original fraction `a / b`.
    calc
      algebraMap (Localization.AtPrime p.asIdeal) K
          (IsLocalization.mk' (Localization.AtPrime p.asIdeal) c ⟨s, hs⟩) =
        IsLocalization.mk' K c ⟨s, hprimeCompl hs⟩ := by
          symm
          exact IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le
            (S := Localization.AtPrime p.asIdeal) (T := K) (h := hprimeCompl) c ⟨s, hs⟩
      _ = IsLocalization.mk' K a bNZD := hfrac
      _ = algebraMap R K a / algebraMap R K b := by
          rw [IsFractionRing.mk'_eq_div]

theorem mem_range_algebraMap_iff_mem_range_localizationAtPrime_forall_height_one
    (x : FractionRing R) :
    x ∈ (algebraMap R (FractionRing R)).range ↔
      ∀ p : { p : PrimeSpectrum R // p.asIdeal.height = 1 },
        x ∈ (algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing R)).range := by
  constructor
  · rintro ⟨a, rfl⟩ p
    -- Any element already coming from `R` also comes from every height-one localization.
    refine ⟨algebraMap R (Localization.AtPrime p.1.asIdeal) a, ?_⟩
    simpa using
      (IsScalarTower.algebraMap_apply R (Localization.AtPrime p.1.asIdeal) (FractionRing R) a).symm
  · intro hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 hb
    let I : Ideal R := Ideal.span ({b} : Set R)
    have h_associated_height_one :
        ∀ q ∈ associatedPrimes R (R ⧸ I), q.height = 1 := by
      -- Part (1) identifies the associated primes of `R / bR` with height-one primes.
      intro q hq
      simpa [I] using
        (quotient_span_singleton_has_no_embedded_primes_and_associatedPrimes_height_eq_one
          (R := R) hb0).2 q hq
    have hclass_zero : Ideal.Quotient.mk I a = 0 := by
      -- Follow the source route: check vanishing at associated primes and use injectivity.
      apply
        to_pi_localization_at_associated_primes_injective
          (R := R) (M := R ⧸ I)
      ext q
      let qSpec : PrimeSpectrum R := ⟨q.1, q.2.1⟩
      have hq_height : qSpec.asIdeal.height = 1 := by
        simpa [qSpec] using h_associated_height_one q.1 q.2
      have hloc :
          algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b ∈
            (algebraMap (Localization.AtPrime qSpec.asIdeal) (FractionRing R)).range :=
        hx ⟨qSpec, hq_height⟩
      -- The localization-range hypothesis is exactly the localized vanishing of the quotient class.
      simpa [I, qSpec] using
        (fraction_mem_localization_range_iff_localized_quotientClass_zero
          (R := R) (a := a) (b := b) hb0 qSpec).1 hloc
    -- Zero class in `R / bR` means the fraction already comes from a global numerator.
    rw [Ideal.Quotient.eq_zero_iff_mem] at hclass_zero
    rcases (Ideal.mem_span_singleton'.1 <| by simpa [I] using hclass_zero) with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hbK : algebraMap R (FractionRing R) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    rw [eq_div_iff hbK]
    simpa [map_mul] using congrArg (algebraMap R (FractionRing R)) hc

/-- Helper for Lemma 10.157.6: a height-one localization of a Noetherian normal domain is a DVR.
-/
lemma height_one_localization_isDiscreteValuationRing
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let pSpec : PrimeSpectrum R := ⟨p, inferInstance⟩
  let A := Localization.AtPrime p
  letI : IsDomain A := isDomain_localizationAtPrime pSpec
  letI : IsIntegrallyClosed A := isIntegrallyClosed_localizationAtPrime pSpec
  have hp_primeHeight : p.primeHeight = 1 := by
    simpa [Ideal.height_eq_primeHeight] using hp
  have hregular : IsRegularLocalRing A := by
    -- Apply the `(R₁)` part of Serre's criterion at the height-one prime `p`.
    letI : IsNormalRing R := inferInstance
    exact
      (serreConditionR_one_of_isNormalRing (R := R)).isRegularLocalRing_localizationAtPrime
        pSpec (by simpa [pSpec] using hp_primeHeight.le)
  have hdim : ringKrullDim A = 1 := by
    -- The localization dimension agrees with the height of the localized prime.
    have hp_height : ((p.height : ℕ∞) : WithBot ℕ∞) = 1 := by
      simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp
    calc
      ringKrullDim A = p.height := by
        simpa [A] using (IsLocalization.AtPrime.ringKrullDim_eq_height p A)
      _ = 1 := hp_height
  -- A one-dimensional regular local domain is exactly a DVR.
  obtain ⟨_, hDVR⟩ :=
    (discreteValuationRing_iff_regularLocalRing_dim_one (A := A)).2 ⟨hregular, hdim⟩
  exact hDVR

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: membership in the `n`th power of the maximal ideal of `R_𝔭`
contracts exactly to the symbolic power `𝔭^(n)`. -/
lemma mem_maximalIdealPow_localizationAtPrime_iff_mem_symbolicPower
    (p : Ideal R) [p.IsPrime] (n : ℕ) (r : R) :
    algebraMap R (Localization.AtPrime p) r ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ n ↔
      r ∈ p.symbolicPower n := by
  -- Expand Definition `10.64.1` and rewrite the extended prime as the maximal ideal of `R_𝔭`.
  simpa [Ideal.symbolicPower, Localization.AtPrime.map_eq_maximalIdeal]

/-- Helper for Lemma 10.157.6: membership in the contraction `A ∩ xA` inside a field `K` is
equivalent to asking that `r / x` already come from `A`. -/
lemma mem_principalSubmoduleContraction_iff_div_mem_range
    {A K : Type u} [CommRing A] [Field K] [Algebra A K]
    {x : K} (hx : x ≠ 0) (r : A) :
    r ∈ ((A ∙ x).comap (Algebra.linearMap A K) : Ideal A) ↔
      algebraMap A K r / x ∈ (algebraMap A K).range := by
  -- Unpack the contraction ideal into the principal-submodule membership statement in `K`.
  change algebraMap A K r ∈ (A ∙ x) ↔
    algebraMap A K r / x ∈ (algebraMap A K).range
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    -- Rewriting `algebraMap r ∈ R ∙ x` gives the required fraction identity.
    refine ⟨c, ?_⟩
    apply (eq_div_iff hx).2
    simpa [Algebra.smul_def] using hc
  · rintro ⟨c, hc⟩
    -- Conversely, a global numerator for `r / x` shows that `algebraMap r` lies in `xR`.
    refine ⟨c, ?_⟩
    simpa [Algebra.smul_def] using (eq_div_iff hx).1 hc

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: associated primes of a finite product are contained in the union of
the associated primes of the factors. -/
lemma associatedPrimes_pi_subset_biUnion
    {ι : Type u} [Finite ι] {M : ι → Type u}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    associatedPrimes R ((i : ι) → M i) ⊆ ⋃ i, associatedPrimes R (M i) := by
  classical
  let P : Type u → Prop := fun α =>
    ∀ (N : α → Type u) (_instAdd : ∀ i, AddCommGroup (N i)) (_instMod : ∀ i, Module R (N i)),
      associatedPrimes R ((i : α) → N i) ⊆ ⋃ i, associatedPrimes R (N i)
  have hP : P ι := by
    refine Finite.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β e ih N instAdd instMod
      let _ := instAdd
      let _ := instMod
      intro p hp
      -- Reindex the product along the equivalence and transport associated primes across it.
      have hp' : p ∈ associatedPrimes R ((i : α) → N (e i)) := by
        simpa using ((LinearEquiv.AssociatedPrimes.eq
          (R := R)
          (l := LinearEquiv.piCongrLeft R N e)).symm ▸ hp)
      have hp'' := ih (fun i : α ↦ N (e i)) (fun i => instAdd (e i)) (fun i => instMod (e i)) hp'
      rcases Set.mem_iUnion.mp hp'' with ⟨i, hi⟩
      exact Set.mem_iUnion_of_mem (e i) hi
    · intro N instAdd instMod
      let _ := instAdd
      let _ := instMod
      -- The empty product is the zero module, so it has no associated primes.
      simpa using
        (associatedPrimes.eq_empty_of_subsingleton (R := R) (M := (i : PEmpty) → N i))
    · intro α _ ih N instAdd instMod
      let _ := instAdd
      let _ := instMod
      intro p hp
      -- Split off the `none` coordinate and apply the binary product formula.
      have hp' : p ∈ associatedPrimes R (N none × ((i : α) → N (some i))) := by
        simpa using ((LinearEquiv.AssociatedPrimes.eq
          (R := R)
          (l := LinearEquiv.piOptionEquivProd R (M := N))) ▸ hp)
      rw [associatedPrimes.prod] at hp'
      rcases hp' with hpnone | hpsome
      · exact Set.mem_iUnion_of_mem none hpnone
      · have htail := ih (fun i : α ↦ N (some i))
          (fun i => instAdd (some i)) (fun i => instMod (some i)) hpsome
        rcases Set.mem_iUnion.mp htail with ⟨i, hi⟩
        exact Set.mem_iUnion_of_mem (some i) hi
  exact hP M inferInstance inferInstance

/-- Helper for Lemma 10.157.6: at a height-one localization, the contracted principal submodule is
a power of the maximal ideal. -/
lemma height_one_local_principalSubmoduleContraction_eq_maximalIdealPow
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1) :
    ∃ n : ℕ,
      (((Localization.AtPrime p.asIdeal) ∙
            (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
          (Algebra.linearMap (Localization.AtPrime p.asIdeal) (FractionRing R)) :
        Ideal (Localization.AtPrime p.asIdeal)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ n := by
  let Rp := Localization.AtPrime p.asIdeal
  let K := FractionRing R
  let xab : K := algebraMap R K a / algebraMap R K b
  let J : Ideal Rp := ((Rp ∙ xab).comap (Algebra.linearMap Rp K) : Ideal Rp)
  letI : IsDomain Rp := isDomain_localizationAtPrime p
  letI : IsIntegrallyClosed Rp := isIntegrallyClosed_localizationAtPrime p
  letI : IsDiscreteValuationRing Rp :=
    height_one_localization_isDiscreteValuationRing (R := R) p.asIdeal hp
  have hxab : xab ≠ 0 := by
    exact div_ne_zero
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.2 ha))
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.2 hb))
  have ha_Rp : algebraMap R Rp a ≠ 0 := by
    intro ha_zero
    apply ha
    exact (IsLocalization.injective Rp p.asIdeal.primeCompl_le_nonZeroDivisors) (by simpa using ha_zero)
  have ha_mem_J : algebraMap R Rp a ∈ J := by
    -- The local identity `a / (a / b) = b` exhibits the image of `a` in the contracted ideal.
    refine (mem_principalSubmoduleContraction_iff_div_mem_range
      (A := Rp) (K := K) (x := xab) hxab (algebraMap R Rp a)).2 ?_
    refine ⟨algebraMap R Rp b, ?_⟩
    have haK : algebraMap R K a ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.2 ha)
    have hbK : algebraMap R K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.2 hb)
    have hmap_a :
        algebraMap Rp K (algebraMap R Rp a) = algebraMap R K a := by
      exact (IsScalarTower.algebraMap_apply R Rp K a).symm
    have hmap_b :
        algebraMap Rp K (algebraMap R Rp b) = algebraMap R K b := by
      exact (IsScalarTower.algebraMap_apply R Rp K b).symm
    have hfrac : algebraMap R K a / xab = algebraMap R K b := by
      apply (div_eq_iff hxab).2
      unfold xab
      symm
      calc
        algebraMap R K b * (algebraMap R K a / algebraMap R K b)
            = algebraMap R K b * (algebraMap R K a * (algebraMap R K b)⁻¹) := by
                rw [div_eq_mul_inv]
        _ = algebraMap R K a * (algebraMap R K b * (algebraMap R K b)⁻¹) := by ring
        _ = algebraMap R K a := by
              rw [mul_inv_cancel₀ hbK, mul_one]
    have hdiv :
        algebraMap Rp K (algebraMap R Rp a) / xab = algebraMap R K b := by
      rw [hmap_a]
      exact hfrac
    exact (hdiv.trans hmap_b.symm).symm
  have hJ_ne_bot : J ≠ ⊥ := by
    intro hJ
    rw [hJ, Ideal.mem_bot] at ha_mem_J
    exact ha_Rp ha_mem_J
  have hprincipal : (IsLocalRing.maximalIdeal Rp).IsPrincipal :=
    IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal Rp)
  -- In a DVR every nonzero ideal is a power of the maximal ideal.
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal Rp hprincipal J hJ_ne_bot
  exact ⟨n, hn⟩

/-- Helper for Lemma 10.157.6: the local range condition at a height-one prime is equivalent to
membership in a power of the maximal ideal of the localization. -/
lemma height_one_local_range_iff_mem_maximalIdealPow
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1) :
    ∃ n : ℕ,
      ∀ r : R,
        algebraMap R (FractionRing R) r /
            (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
          (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing R)).range ↔
        algebraMap R (Localization.AtPrime p.asIdeal) r ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ n := by
  obtain ⟨n, hn⟩ :=
    height_one_local_principalSubmoduleContraction_eq_maximalIdealPow
      (R := R) ha hb p hp
  refine ⟨n, ?_⟩
  intro r
  have hmap_r :
      algebraMap (Localization.AtPrime p.asIdeal) (FractionRing R)
          (algebraMap R (Localization.AtPrime p.asIdeal) r) =
        algebraMap R (FractionRing R) r := by
    simpa using
      (IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal) (FractionRing R) r).symm
  -- Read the local range predicate as membership in the contracted ideal and rewrite it by `hn`.
  simpa [hmap_r, hn] using
    (mem_principalSubmoduleContraction_iff_div_mem_range
      (A := Localization.AtPrime p.asIdeal) (K := FractionRing R)
      (x := algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)
      (div_ne_zero
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.2 ha))
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.2 hb)))
      (algebraMap R (Localization.AtPrime p.asIdeal) r)).symm

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.157.6: away from the support of `(ab)`, the fraction `r / (a / b)` already
comes from the localization `R_𝔮`. -/
lemma local_fraction_range_of_mul_not_mem
    {a b r : R} (q : PrimeSpectrum R) (hab : a * b ∉ q.asIdeal) :
    algebraMap R (FractionRing R) r /
        (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
      (algebraMap (Localization.AtPrime q.asIdeal) (FractionRing R)).range := by
  have ha_not_mem : a ∉ q.asIdeal := by
    intro ha_mem
    exact hab (q.asIdeal.mul_mem_right b ha_mem)
  have hb_not_mem : b ∉ q.asIdeal := by
    intro hb_mem
    exact hab (q.asIdeal.mul_mem_left a hb_mem)
  have ha0 : a ≠ 0 := by
    intro ha_zero
    exact ha_not_mem (ha_zero.symm ▸ q.asIdeal.zero_mem)
  have hb0 : b ≠ 0 := by
    intro hb_zero
    exact hb_not_mem (hb_zero.symm ▸ q.asIdeal.zero_mem)
  let aq : q.asIdeal.primeCompl := ⟨a, ha_not_mem⟩
  have haK : algebraMap R (FractionRing R) a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.2 ha0)
  have hbK : algebraMap R (FractionRing R) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.2 hb0)
  -- Use the explicit local representative `(r * b) / a` in `R_𝔮`.
  refine ⟨IsLocalization.mk' (Localization.AtPrime q.asIdeal) (r * b) aq, ?_⟩
  calc
    algebraMap (Localization.AtPrime q.asIdeal) (FractionRing R)
        (IsLocalization.mk' (Localization.AtPrime q.asIdeal) (r * b) aq) =
      IsLocalization.mk' (FractionRing R) (r * b)
        ⟨a, q.asIdeal.primeCompl_le_nonZeroDivisors aq.2⟩ := by
          symm
          exact IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le
            (S := Localization.AtPrime q.asIdeal) (T := FractionRing R)
            (h := q.asIdeal.primeCompl_le_nonZeroDivisors) (r * b) aq
    _ = algebraMap R (FractionRing R) (r * b) / algebraMap R (FractionRing R) a := by
          rw [IsFractionRing.mk'_eq_div]
    _ = algebraMap R (FractionRing R) r /
          (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) := by
          rw [map_mul]
          apply (eq_div_iff (div_ne_zero haK hbK)).2
          field_simp [haK, hbK]

/-- Helper for Lemma 10.157.6: a minimal prime over a nonzero principal ideal has height `1`. -/
lemma minimalPrime_span_singleton_height_eq_one_of_nonzero
    {a : R} (ha : a ≠ 0) {p : Ideal R}
    (hp : p ∈ (Ideal.span ({a} : Set R)).minimalPrimes) :
    p.height = 1 := by
  let A : Type u := R ⧸ Ideal.span ({a} : Set R)
  have hp_assoc : p ∈ associatedPrimes R A := by
    -- Minimal primes of the annihilator of `R / aR` are associated primes of the quotient.
    have hp_ann : p ∈ (Module.annihilator R A).minimalPrimes := by
      simpa [A, Ideal.annihilator_quotient] using hp
    exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      (R := R) (M := A) hp_ann
  -- Part (1) already proves the height-one conclusion for all associated primes of `R / aR`.
  simpa [A] using
    (quotient_span_singleton_has_no_embedded_primes_and_associatedPrimes_height_eq_one
      (R := R) ha).2 p hp_assoc

/-- Helper for Lemma 10.157.6: a height-one prime containing a nonzero product `ab` is already
minimal over the principal ideal `(ab)`. -/
lemma height_one_prime_mem_minimalPrimes_span_singleton_of_mul_mem
    {a b : R} (hab0 : a * b ≠ 0) {q : Ideal R} [q.IsPrime]
    (hq : q.height = 1) (hab : a * b ∈ q) :
    q ∈ (Ideal.span ({a * b} : Set R)).minimalPrimes := by
  have hspan_le_q : Ideal.span ({a * b} : Set R) ≤ q := by
    -- The principal ideal `(ab)` is contained in `q` because `ab ∈ q`.
    simpa using (Ideal.span_singleton_le_iff_mem (I := q) (x := a * b)).2 hab
  obtain ⟨p, hp, hpq⟩ :=
    Ideal.exists_minimalPrimes_le
      (I := Ideal.span ({a * b} : Set R)) (J := q) hspan_le_q
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
  have hp_height : p.height = 1 :=
    minimalPrime_span_singleton_height_eq_one_of_nonzero
      (R := R) (a := a * b) hab0 hp
  have hp_eq_q : p = q := by
    -- Height-one minimal primes cannot sit strictly below another height-one prime.
    by_contra hp_ne_q
    have hp_lt_q : p < q := lt_of_le_of_ne hpq hp_ne_q
    have hp_primeHeight : p.primeHeight = 1 := by
      simpa [Ideal.height_eq_primeHeight] using hp_height
    have hq_primeHeight : q.primeHeight = 1 := by
      simpa [Ideal.height_eq_primeHeight] using hq
    have htwo_le : (2 : ℕ∞) ≤ q.primeHeight := by
      calc
        (2 : ℕ∞) = 1 + 1 := by norm_num
        _ = p.primeHeight + 1 := by simp [hp_primeHeight]
        _ ≤ q.primeHeight := Ideal.primeHeight_add_one_le_of_lt hp_lt_q
    rw [hq_primeHeight] at htwo_le
    norm_num at htwo_le
  simpa [hp_eq_q] using hp

/-- Helper for Lemma 10.157.6: for a height-one prime, containing `ab` is equivalent to being a
minimal prime over the principal ideal `(ab)` as soon as `ab ≠ 0`. -/
lemma height_one_prime_mem_minimalPrimes_span_singleton_iff_mul_mem
    {a b : R} (hab0 : a * b ≠ 0) {q : Ideal R} [q.IsPrime]
    (hq : q.height = 1) :
    q ∈ (Ideal.span ({a * b} : Set R)).minimalPrimes ↔ a * b ∈ q := by
  constructor
  · intro hq_min
    -- Membership in a minimal prime over `(ab)` immediately gives `ab ∈ q`.
    exact hq_min.1.2 (Ideal.subset_span (by simp))
  · intro hab
    -- The converse is the height-one classification proved just above.
    exact height_one_prime_mem_minimalPrimes_span_singleton_of_mul_mem
      (R := R) hab0 hq hab

/-- Helper for Lemma 10.157.6: for `x = a / b`, testing membership in `R ∩ xR` only needs the
height-one localizations coming from the minimal primes over `(ab)`. -/
lemma mem_principalSubmoduleContraction_iff_forall_minimalPrimes_mul_local
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (r : R) :
    r ∈ ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
          (Algebra.linearMap R (FractionRing R)) : Ideal R) ↔
      ∀ p : { p : PrimeSpectrum R // p.asIdeal ∈ (Ideal.span ({a * b} : Set R)).minimalPrimes },
        algebraMap R (FractionRing R) r /
            (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
          (algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing R)).range := by
  have hx :
      algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b ≠ 0 := by
    exact div_ne_zero
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.2 ha))
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.2 hb))
  constructor
  · intro hr
    have hglobal :
        algebraMap R (FractionRing R) r /
            (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
          (algebraMap R (FractionRing R)).range := by
      -- First pass from the contraction ideal to the global fraction-field range test.
      exact (mem_principalSubmoduleContraction_iff_div_mem_range
        (A := R) (K := FractionRing R) (x := _ ) hx r).1 hr
    have hheight_one_local :
        ∀ q : { q : PrimeSpectrum R // q.asIdeal.height = 1 },
          algebraMap R (FractionRing R) r /
              (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
            (algebraMap (Localization.AtPrime q.1.asIdeal) (FractionRing R)).range :=
      (mem_range_algebraMap_iff_mem_range_localizationAtPrime_forall_height_one
        (R := R)
        (algebraMap R (FractionRing R) r /
          (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b))).1 hglobal
    intro p
    have hp_height : p.1.asIdeal.height = 1 := by
      simpa using
        minimalPrime_span_singleton_height_eq_one_of_nonzero
          (R := R) (a := a * b) (mul_ne_zero ha hb) p.2
    exact hheight_one_local ⟨p.1, hp_height⟩
  · intro hlocal
    have hheight_one_local :
        ∀ q : { q : PrimeSpectrum R // q.asIdeal.height = 1 },
          algebraMap R (FractionRing R) r /
              (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
            (algebraMap (Localization.AtPrime q.1.asIdeal) (FractionRing R)).range := by
      intro q
      by_cases hab_mem : a * b ∈ q.1.asIdeal
      · -- When `q` contains `(ab)`, the height-one criterion identifies it with a minimal prime.
        have hq_min :
            q.1.asIdeal ∈ (Ideal.span ({a * b} : Set R)).minimalPrimes := by
          exact height_one_prime_mem_minimalPrimes_span_singleton_of_mul_mem
            (R := R) (a := a) (b := b) (mul_ne_zero ha hb) q.2 hab_mem
        exact hlocal ⟨q.1, hq_min⟩
      · -- Away from `(ab)`, the local range condition is automatic by the explicit witness `(r*b)/a`.
        exact local_fraction_range_of_mul_not_mem
          (R := R) (a := a) (b := b) (r := r) q.1 hab_mem
    have hglobal :
        algebraMap R (FractionRing R) r /
            (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
          (algebraMap R (FractionRing R)).range :=
      (mem_range_algebraMap_iff_mem_range_localizationAtPrime_forall_height_one
        (R := R)
        (algebraMap R (FractionRing R) r /
          (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b))).2
        hheight_one_local
    -- Return from the global range test to the contraction ideal.
    exact (mem_principalSubmoduleContraction_iff_div_mem_range
      (A := R) (K := FractionRing R) (x := _ ) hx r).2 hglobal

/-- Helper for Lemma 10.157.6: the contraction ideal for `a / b` is the infimum of the symbolic
powers attached to the minimal primes over `(ab)`. -/
lemma principalSubmoduleContraction_eq_iInf_symbolicPower_over_minimalPrimes
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ n : { p : PrimeSpectrum R //
        p.asIdeal ∈ (Ideal.span ({a * b} : Set R)).minimalPrimes } → ℕ,
      ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
          (Algebra.linearMap R (FractionRing R)) : Ideal R) =
        ⨅ p : { p : PrimeSpectrum R //
            p.asIdeal ∈ (Ideal.span ({a * b} : Set R)).minimalPrimes },
          p.1.asIdeal.symbolicPower (n p) := by
  let S : Set (Ideal R) := (Ideal.span ({a * b} : Set R)).minimalPrimes
  let P : Type u := { p : PrimeSpectrum R // p.asIdeal ∈ S }
  have hfinite_S : S.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span ({a * b} : Set R))
  haveI : Fintype S := hfinite_S.fintype
  haveI : Finite P := by
    refine Finite.of_injective (fun p : P ↦ (⟨p.1.asIdeal, p.2⟩ : S)) ?_
    intro p q hpq
    apply Subtype.ext
    exact PrimeSpectrum.ext <| Subtype.ext_iff.mp hpq
  have hheight_one : ∀ p : P, p.1.asIdeal.height = 1 := by
    intro p
    exact minimalPrime_span_singleton_height_eq_one_of_nonzero
      (R := R) (a := a * b) (mul_ne_zero ha hb) p.2
  choose n hn using fun p : P =>
    height_one_local_range_iff_mem_maximalIdealPow
      (R := R) (a := a) (b := b) ha hb p.1 (hheight_one p)
  refine ⟨fun p ↦ n p, ?_⟩
  ext r
  constructor
  · intro hr
    rw [Ideal.mem_iInf]
    intro p
    have hr_local :=
      (mem_principalSubmoduleContraction_iff_forall_minimalPrimes_mul_local
        (R := R) (a := a) (b := b) ha hb r).1 hr p
    have hr_pow : algebraMap R (Localization.AtPrime p.1.asIdeal) r ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.1.asIdeal) ^ n p := by
      exact (hn p r).1 hr_local
    exact (mem_maximalIdealPow_localizationAtPrime_iff_mem_symbolicPower
      (R := R) p.1.asIdeal (n p) r).1 hr_pow
  · intro hr
    rw [Ideal.mem_iInf] at hr
    refine
      (mem_principalSubmoduleContraction_iff_forall_minimalPrimes_mul_local
        (R := R) (a := a) (b := b) ha hb r).2 ?_
    intro p
    have hr_pow : algebraMap R (Localization.AtPrime p.1.asIdeal) r ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.1.asIdeal) ^ n p := by
      exact (mem_maximalIdealPow_localizationAtPrime_iff_mem_symbolicPower
        (R := R) p.1.asIdeal (n p) r).2 (by simpa [S] using hr p)
    exact (hn p r).2 hr_pow

/-- Lemma 10.157.6 (3): for a nonzero element `x` of the fraction field of a Noetherian normal
domain `R`, the quotient by the contraction of the principal `R`-submodule `xR ⊆ FractionRing R`,
namely `R / (R ∩ xR)`, has no embedded associated primes, and every associated prime of this
quotient has height `1`. -/
-- Proof sketch: write `x = a / b` and use part (2) to express `R ∩ xR` as an intersection over
-- the height-one primes minimal over `(ab)`. This embeds `R / (R ∩ xR)` into a finite direct sum
-- of quotients by symbolic powers of those primes, whose associated primes are singletons by Lemma
-- `10.64.2`; hence every associated prime is height one and none is embedded.
@[stacks 031T]
theorem quotient_fractionRing_principalSubmoduleContraction_has_no_embedded_primes_and_associatedPrimes_height_eq_one
    {x : FractionRing R} (hx : x ≠ 0) :
    embeddedAssociatedPrimes R
        (R ⧸
          ((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)) = ∅ ∧
      ∀ p ∈ associatedPrimes R
          (R ⧸
            ((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)),
        p.height = 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply hx
    simp [ha]
  have haK : algebraMap R (FractionRing R) a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.2 ha0)
  have hx' :
      algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b ≠ 0 := by
    exact div_ne_zero haK
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)
  let S : Set (Ideal R) := (Ideal.span ({a * b} : Set R)).minimalPrimes
  have hcontraction :
      ∀ r : R,
        r ∈ ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
              (Algebra.linearMap R (FractionRing R)) : Ideal R) ↔
          algebraMap R (FractionRing R) r /
              (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
            (algebraMap R (FractionRing R)).range := by
    intro r
    -- This is the source-facing bridge from the contraction ideal to a fraction-field criterion.
    exact mem_principalSubmoduleContraction_iff_div_mem_range
      (A := R) (K := FractionRing R) (x := _ ) hx' r
  have hheight_one :
      ∀ p : Ideal R, p ∈ S → p.height = 1 := by
    intro p hp
    -- The primes controlling clause (3) are the minimal primes over `(ab)`, hence height one.
    exact minimalPrime_span_singleton_height_eq_one_of_nonzero
      (R := R) (a := a * b) (mul_ne_zero ha0 hb0) hp
  have hfinite_localization :
      ∀ r : R,
        r ∈ ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
              (Algebra.linearMap R (FractionRing R)) : Ideal R) ↔
          ∀ p : { p : PrimeSpectrum R // p.asIdeal ∈ S },
            algebraMap R (FractionRing R) r /
                (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) ∈
              (algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing R)).range := by
    intro r
    -- Route correction: the global height-one test has now been reduced to the finite family of
    -- minimal primes over `(ab)`, matching the source proof exactly.
    simpa [S] using
      mem_principalSubmoduleContraction_iff_forall_minimalPrimes_mul_local
        (R := R) (a := a) (b := b) ha0 hb0 r
  obtain ⟨n, hcontraction_eq⟩ :=
    principalSubmoduleContraction_eq_iInf_symbolicPower_over_minimalPrimes
      (R := R) (a := a) (b := b) ha0 hb0
  let P : Type u := { p : PrimeSpectrum R // p.asIdeal ∈ S }
  have hfinite_S : S.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span ({a * b} : Set R))
  haveI : Fintype S := hfinite_S.fintype
  haveI : Finite P := by
    refine Finite.of_injective (fun p : P ↦ (⟨p.1.asIdeal, p.2⟩ : S)) ?_
    intro p q hpq
    apply Subtype.ext
    exact PrimeSpectrum.ext <| Subtype.ext_iff.mp hpq
  let I : P → Ideal R := fun p ↦ p.1.asIdeal.symbolicPower (n p)
  let φ : (R ⧸ ⨅ p, I p) →ₗ[R] ((p : P) → R ⧸ I p) :=
    { toFun := Ideal.quotientInfToPiQuotient I
      map_add' := by simp
      map_smul' := by
        intro c y
        refine Quotient.inductionOn y ?_
        intro y
        ext p
        rfl }
  have hassociated_subset :
      associatedPrimes R
          (R ⧸ ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
            (Algebra.linearMap R (FractionRing R)) : Ideal R)) ⊆
        ⋃ p, associatedPrimes R (R ⧸ I p) := by
    -- Inject the quotient into the product of symbolic-power quotients and bound associated primes
    -- factorwise.
    have hsubset_pi :
        associatedPrimes R (R ⧸ ⨅ p, I p) ⊆ associatedPrimes R ((p : P) → R ⧸ I p) :=
      associatedPrimes.subset_of_injective
        (R := R) (f := φ) (Ideal.quotientInfToPiQuotient_inj I)
    have hsubset_union :
        associatedPrimes R (R ⧸ ⨅ p, I p) ⊆ ⋃ p, associatedPrimes R (R ⧸ I p) :=
      Set.Subset.trans hsubset_pi
        (associatedPrimes_pi_subset_biUnion (R := R) (M := fun p : P ↦ R ⧸ I p))
    have hInf_eq :
        (⨅ p, I p) =
          ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
            (Algebra.linearMap R (FractionRing R)) : Ideal R) := by
      simpa [P, S, I] using hcontraction_eq.symm
    rw [hInf_eq] at hsubset_union
    exact hsubset_union
  have hassociated_height_one :
      ∀ q ∈ associatedPrimes R
          (R ⧸ ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
            (Algebra.linearMap R (FractionRing R)) : Ideal R)),
        q.height = 1 := by
    intro q hq
    rcases Set.mem_iUnion.mp (hassociated_subset hq) with ⟨p, hp_assoc⟩
    by_cases hn_zero : n p = 0
    · letI : Subsingleton (R ⧸ p.1.asIdeal.symbolicPower 0) := by
        simpa [Ideal.symbolicPower] using (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
      have hI_zero : I p = p.1.asIdeal.symbolicPower 0 := by
        simp [I, hn_zero]
      have hp_empty :
          associatedPrimes R (R ⧸ I p) = ∅ := by
        rw [hI_zero]
        simpa using
          (associatedPrimes.eq_empty_of_subsingleton
            (R := R) (M := R ⧸ p.1.asIdeal.symbolicPower 0))
      rw [hp_empty] at hp_assoc
      exact hp_assoc.elim
    · have hn_pos : 0 < n p := Nat.pos_of_ne_zero hn_zero
      have hp_singleton :
          associatedPrimes R (R ⧸ I p) = {p.1.asIdeal} := by
        simpa [I] using
          (associatedPrimes_quotient_symbolicPower_eq_singleton
            (R := R) p.1.asIdeal (n := n p) hn_pos)
      have hq_eq : q = p.1.asIdeal := by
        simpa [hp_singleton] using hp_assoc
      simpa [hq_eq] using hheight_one p.1.asIdeal p.2
  have hno_embedded :
      embeddedAssociatedPrimes R
          (R ⧸ ((R ∙ (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)).comap
            (Algebra.linearMap R (FractionRing R)) : Ideal R)) = ∅ := by
    rw [embeddedAssociatedPrimes_eq_empty_iff]
    intro q hq
    refine ⟨hq, ?_⟩
    intro q' hq' hq'le
    by_cases hqq : q' = q
    · simpa [hqq]
    · exfalso
      have hq_height : q.height = 1 := hassociated_height_one q hq
      have hq'_height : q'.height = 1 := hassociated_height_one q' hq'
      have hlt : q' < q := lt_of_le_of_ne hq'le hqq
      letI : q.IsPrime := hq.toIsPrime
      letI : q'.IsPrime := hq'.toIsPrime
      have hq_primeHeight : q.primeHeight = 1 := by
        rw [Ideal.height_eq_primeHeight (I := q)] at hq_height
        exact hq_height
      have hq'_primeHeight : q'.primeHeight = 1 := by
        rw [Ideal.height_eq_primeHeight (I := q')] at hq'_height
        exact hq'_height
      have htwo_le : (2 : ℕ∞) ≤ q.primeHeight := by
        calc
          (2 : ℕ∞) = 1 + 1 := by norm_num
          _ = q'.primeHeight + 1 := by rw [hq'_primeHeight]
          _ ≤ q.primeHeight := Ideal.primeHeight_add_one_le_of_lt hlt
      rw [hq_primeHeight] at htwo_le
      norm_num at htwo_le
  exact ⟨hno_embedded, hassociated_height_one⟩

end
