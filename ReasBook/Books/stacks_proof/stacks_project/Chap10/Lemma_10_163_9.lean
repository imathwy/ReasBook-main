import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Lemma_10_37_13
import StacksProject_2024.Chap10.Lemma_10_37_14
import StacksProject_2024.Chap10.Lemma_10_37_17
import StacksProject_2024.Chap10.Lemma_10_140_3
import StacksProject_2024.Chap10.Lemma_10_157_5
import StacksProject_2024.Chap10.Lemma_10_163_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S]

/-- Helper for Chap10 Lemma 10 163 9: a ring covered by normal basic localizations is normal. -/
lemma isNormalRing_of_span_range_localizationAway
    {A : Type u} [CommRing A] (s : Set A) (hs : Ideal.span s = ⊤)
    (h : ∀ x ∈ s, IsNormalRing (Localization.Away x)) : IsNormalRing A := by
  -- Proof comment: to check normality at a prime `p`, choose a basic open in the cover meeting
  -- the point and compare the two prime localizations.
  refine ⟨fun p ↦ ?_⟩
  obtain ⟨x, hxs, hdisj⟩ :=
    Ideal.exists_disjoint_powers_of_span_eq_top s hs p.asIdeal p.2.ne_top
  let M : Submonoid A := Submonoid.powers x
  let Aₓ := Localization.Away x
  let q' : Ideal Aₓ := Ideal.map (algebraMap A Aₓ) p.asIdeal
  have hq' : Ideal.comap (algebraMap A Aₓ) q' = p.asIdeal := by
    simpa [M, Aₓ, q'] using
      IsLocalization.comap_map_of_isPrime_disjoint M Aₓ p.2 hdisj.symm
  letI : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M Aₓ p.asIdeal p.2 hdisj.symm
  let qSpec : PrimeSpectrum Aₓ := ⟨q', inferInstance⟩
  letI : IsNormalRing Aₓ := h x hxs
  -- Proof comment: normality of the selected basic localization gives the prime-local domain and
  -- integrally closed facts at the corresponding prime.
  have hqDomain : IsDomain (Localization.AtPrime q') := isDomain_localizationAtPrime qSpec
  have hqClosed : IsIntegrallyClosed (Localization.AtPrime q') :=
    isIntegrallyClosed_localizationAtPrime qSpec
  letI : IsLocalization.AtPrime (Localization.AtPrime q') p.asIdeal := by
    simpa [M, Aₓ, hq'] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        M (Localization.AtPrime q') q')
  let e : Localization.AtPrime p.asIdeal ≃ₐ[A] Localization.AtPrime q' :=
    IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q')
  -- Proof comment: transport the two local normal-domain conditions back to the original prime
  -- localization of `A`.
  exact ⟨Function.Injective.isDomain e e.injective, hqClosed.of_equiv e.symm.toRingEquiv⟩

/-- Helper for Chap10 Lemma 10 163 9: finite multivariable polynomial rings over normal rings
are normal. -/
lemma isNormalRing_mvPolynomial_fin
    {A : Type u} [CommRing A] [IsNormalRing A] (n : ℕ) :
    IsNormalRing (MvPolynomial (Fin n) A) := by
  -- Proof comment: peel off one variable at a time using the polynomial-ring normality theorem
  -- and the standard `MvPolynomial.finSuccEquiv`.
  induction n with
  | zero =>
      have e : A ≃+* MvPolynomial (Fin 0) A :=
        (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv
      exact isNormalRing_of_equiv e
  | succ n ih =>
      have hpoly : IsNormalRing (Polynomial (MvPolynomial (Fin n) A)) := by
        let _ : IsNormalRing (MvPolynomial (Fin n) A) := ih
        exact isNormalRing_polynomial
      let _ : IsNormalRing (Polynomial (MvPolynomial (Fin n) A)) := hpoly
      have e : Polynomial (MvPolynomial (Fin n) A) ≃+* MvPolynomial (Fin (n + 1)) A :=
        (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv
      exact isNormalRing_of_equiv e

/-- Helper for Chap10 Lemma 10.163.9: a smooth algebra over a field is a regular ring. -/
lemma isRegularRing_of_smooth_over_field
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] :
    IsRegularRing A := by
  -- Proof comment: smoothness makes the smooth locus all of `Spec A`.
  let _ : Algebra.FinitePresentation K A := inferInstance
  let _ : Algebra.FiniteType K A := inferInstance
  refine
    { toIsNoetherian := Algebra.FiniteType.isNoetherianRing K A
      isRegularLocalRing_atPrime := ?_ }
  intro q
  -- Proof comment: the earlier smooth-point criterion converts smoothness at `q` into
  -- regularity of the local ring at `q`.
  have hsmoothLocus : Algebra.smoothLocus K A = Set.univ := Algebra.smoothLocus_eq_univ
  have hqSmooth : Algebra.IsSmoothAt K q.asIdeal := by
    simpa [Algebra.smoothLocus] using (Set.eq_univ_iff_forall.mp hsmoothLocus) q
  simpa using Algebra.isRegularLocalRing_of_isSmoothAt (k := K) (S := A) q.asIdeal hqSmooth

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth ring maps and ascent of normality;
* sampled owner declarations:
  `IsNormalRing`,
  `Algebra.Smooth`,
  `isNormalRing_of_flat_of_fiber`,
  `isRegularRing_of_smooth`,
  `isNormalRing_of_isRegularRing`;
* best owner abstraction: this theorem is a `source-facing` smooth-ascent statement, while the
  canonical owner theorem is `isNormalRing_of_flat_of_fiber`; smoothness and fiber regularity
  should remain derived API rather than being repackaged locally.

Primitive data vs. derived API:
* primitive data: the smooth `R`-algebra structure on `S` and the normal-ring owner `[IsNormalRing R]`;
* derived API: flatness of `R → S`, smoothness of every residue-field fiber by base change,
  regularity of those fibers from `isRegularRing_of_smooth`, and their normality from
  `isNormalRing_of_isRegularRing`.

Layering:
* `source-facing`: `isNormalRing_of_smooth`;
* `core/canonical`: `IsNormalRing`, `Algebra.Smooth`, and `isNormalRing_of_flat_of_fiber`;
* `bridge/view`: smooth base change to `p.asIdeal.Fiber S` and the regular-to-normal bridge on the
  fibers.
-/
/-- Helper for Chap10 Lemma 10.163.9: every prime fiber of a smooth algebra is normal. -/
lemma isNormalRing_fiber_of_smooth (p : PrimeSpectrum R) :
    IsNormalRing (p.asIdeal.Fiber S) := by
  -- Proof comment: smoothness descends to residue-field fibers, giving a smooth algebra over the
  -- field `κ(p)`.
  let _ : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  have hregular : IsRegularRing (p.asIdeal.Fiber S) :=
    isRegularRing_of_smooth_over_field
      (K := p.asIdeal.ResidueField) (A := p.asIdeal.Fiber S)
  let _ : IsRegularRing (p.asIdeal.Fiber S) := hregular
  -- Proof comment: regular rings are normal by the earlier regular-to-normal bridge.
  exact isNormalRing_of_isRegularRing

/-- Helper for Chap10 Lemma 10.163.9: smooth algebras have the normal fiber family needed for
flat-fiber ascent. -/
lemma normalFibers_of_smooth :
    ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S) := by
  -- Proof comment: package the pointwise smooth-fiber normality statement in the exact
  -- dependent-function shape consumed by the ascent theorem.
  exact fun p ↦ isNormalRing_fiber_of_smooth p

variable [IsNormalRing R]

/-- Helper for Chap10 Lemma 10.163.9: in the Noetherian smooth setting, normal fibers ascend
normality from the base to the target. -/
lemma isNormalRing_of_smooth_of_fiber_normal
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hfiber : ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S)) :
    IsNormalRing S := by
  -- Proof comment: the earlier flat-fiber ascent theorem is exactly the Noetherian version of
  -- the smooth-fiber route.
  exact isNormalRing_of_flat_of_fiber (R := R) (S := S) hfiber

/-- Helper for Chap10 Lemma 10 163 9: a prime-indexed family of normal basic localizations
globalizes normality. -/
lemma isNormalRing_of_prime_local_away_cover
    {A : Type u} [CommRing A] (f : PrimeSpectrum A → A)
    (hf : ∀ q, f q ∉ q.asIdeal)
    (h : ∀ q, IsNormalRing (Localization.Away (f q))) :
    IsNormalRing A := by
  -- Proof comment: it is enough to prove that the chosen denominators generate the unit ideal,
  -- then use the existing basic-open local normality theorem.
  refine isNormalRing_of_span_range_localizationAway (Set.range f) ?_ ?_
  · by_contra hspan
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hspan
    let q : PrimeSpectrum A := ⟨m, inferInstance⟩
    -- Proof comment: the chosen element for this maximal prime lies in the generated ideal, hence
    -- in the prime itself, contradicting the defining avoidance condition.
    exact hf q (hle (Ideal.subset_span (Set.mem_range_self q)))
  · intro x hx
    rcases hx with ⟨q, rfl⟩
    exact h q

/-- Helper for Chap10 Lemma 10 163 9: standard-étale base change preserves the canonical
integral-closure comparison map. -/
lemma standardEtale_toIntegralClosure_bijective
    {A : Type u} {B : Type v} {C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.IsStandardEtale A B] :
    Function.Bijective (TensorProduct.toIntegralClosure A B C) := by
  -- Proof comment: injectivity is the flat part of standard étaleness, already exposed by
  -- Mathlib's integral-closure comparison API.
  refine ⟨TensorProduct.toIntegralClosure_injective_of_flat, ?_⟩
  intro x
  rcases x with ⟨x, hx⟩
  -- Proof comment: the public standard-étale membership theorem says every integral element lies
  -- in the algebra generated by the image of the source integral closure; unpacking that generated
  -- subalgebra gives surjectivity of the comparison map.
  simp only [TensorProduct.toIntegralClosure, Subtype.ext_iff, AlgHom.coe_codRestrict,
    ← AlgHom.mem_range]
  refine Algebra.adjoin_le ?_ (mem_adjoin_map_integralClosure_of_isStandardEtale x hx)
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨1 ⊗ₜ ⟨y, hy⟩, ?_⟩
  simp

/-- Helper for Chap10 Lemma 10 163 9: a standard-étale algebra is formally unramified after
localizing at a target prime and its contraction. -/
lemma localizationAtPrime_formallyUnramified_of_isStandardEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsStandardEtale A B] (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: standard étaleness gives formal unramifiedness over `A`; target localization
  -- preserves it, and then we restrict scalars from the prime localization of the source.
  dsimp
  let p : Ideal A := Ideal.comap (algebraMap A B) q.asIdeal
  haveI : q.asIdeal.LiesOver p := Ideal.LiesOver.mk rfl
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := inferInstance
  haveI : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    inferInstance
  exact Algebra.FormallyUnramified.localization_base (R := A)
    (Rₘ := Localization.AtPrime p) (Sₘ := Localization.AtPrime q.asIdeal) p.primeCompl

/-- Helper for Chap10 Lemma 10 163 9: a standard-étale algebra over a normal base is normal. -/
lemma isNormalRing_of_isStandardEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsStandardEtale A B] [IsNormalRing A] :
    IsNormalRing B := by
  -- Proof comment: reduce normality of `B` to the normal-domain pair at an arbitrary prime
  -- localization of a standard-étale chart.
  refine ⟨fun q ↦ ?_⟩
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  have hunram :
      Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := by
    simpa [p] using localizationAtPrime_formallyUnramified_of_isStandardEtale
      (A := A) (B := B) q
  -- Proof comment: the source localization is normal by the base hypothesis; the remaining
  -- missing bridge must turn the prime-local standard-étale algebra into a domain and prove
  -- integrally closedness, using `hunram` and the integral-closure comparison above.
  letI : IsDomain (Localization.AtPrime p.asIdeal) := isDomain_localizationAtPrime p
  letI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    isIntegrallyClosed_localizationAtPrime p
  -- TODO: prove the generic-fiber/fraction-ring bridge for
  -- `Localization.AtPrime q.asIdeal` over `Localization.AtPrime p.asIdeal`, then use
  -- `standardEtale_toIntegralClosure_bijective` to obtain the integrally closed component.
  sorry

/-- Helper for Chap10 Lemma 10 163 9: a smooth point admits a normal principal-open
neighborhood. -/
lemma normalLocalizationAway_of_smoothAt
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNormalRing A] [Algebra.FinitePresentation A B]
    (q : PrimeSpectrum B) [Algebra.IsSmoothAt A q.asIdeal] :
    ∃ f : B, f ∉ q.asIdeal ∧ IsNormalRing (Localization.Away f) := by
  -- Proof comment: local smoothness gives a principal open standard-étale over a finite
  -- polynomial algebra over the base.
  obtain ⟨f, hfq, n, hAlg, hTower, hStd⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q.asIdeal)
  refine ⟨f, hfq, ?_⟩
  letI : Algebra (MvPolynomial (Fin n) A) (Localization.Away f) := hAlg
  letI : IsScalarTower A (MvPolynomial (Fin n) A) (Localization.Away f) := hTower
  letI : Algebra.IsStandardEtale (MvPolynomial (Fin n) A) (Localization.Away f) := hStd
  letI : IsNormalRing (MvPolynomial (Fin n) A) := isNormalRing_mvPolynomial_fin n
  -- Proof comment: the standard-étale chart-normality bridge turns polynomial normality into
  -- normality of the selected principal open.
  exact isNormalRing_of_isStandardEtale (A := MvPolynomial (Fin n) A)
    (B := Localization.Away f)

-- Route correction: the old flat-fiber route requires Noetherian hypotheses on `R` and `S`, and
-- the previous standard-smooth route hid the same issue in one global chart-normality helper. The
-- current skeleton uses smoothness at each target prime to choose a normal principal-open chart
-- and then globalizes from a prime-indexed basic-open cover.
-- Proof sketch: for every `q : Spec S`, use `smoothLocus_eq_univ` and the smooth-at chart lemma
-- to choose `f q ∉ q` with `S[1/f q]` normal; these elements span the unit ideal by maximal-ideal
-- avoidance, so normality globalizes.
include R S

/-- Lemma 10.163.9: if `R → S` is smooth and `R` is a normal ring, then `S` is a normal ring. -/
@[stacks 033C]
theorem isNormalRing_of_smooth :
    IsNormalRing S := by
  -- Proof comment: global smoothness identifies every prime of `S` as a smooth point over `R`.
  have hpointwise :
      ∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧ IsNormalRing (Localization.Away f) := by
    intro q
    have hqSmooth : Algebra.IsSmoothAt R q.asIdeal := by
      have hsmoothLocus : Algebra.smoothLocus R S = Set.univ := Algebra.smoothLocus_eq_univ
      simpa [Algebra.smoothLocus] using (Set.eq_univ_iff_forall.mp hsmoothLocus) q
    let _ : Algebra.IsSmoothAt R q.asIdeal := hqSmooth
    exact normalLocalizationAway_of_smoothAt (A := R) (B := S) q
  choose f hf hnormal using hpointwise
  -- Proof comment: the prime-indexed chosen basic opens cover `Spec S`, so the local normality
  -- statements assemble to normality of `S`.
  exact isNormalRing_of_prime_local_away_cover f hf hnormal

end
