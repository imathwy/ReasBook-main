import Mathlib
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.RingTheory.Valuation.Discrete.Basic
import stacks_proof.stacks_project.Chap10.Definition_10_37_11
import stacks_proof.stacks_project.Chap10.Lemma_10_39_2
import stacks_proof.stacks_project.Chap10.Lemma_10_60_11
import stacks_proof.stacks_project.Chap10.Lemma_10_63_5
import stacks_proof.stacks_project.Chap10.Lemma_10_119_7
import stacks_proof.stacks_project.Chap10.Lemma_10_157_6
import stacks_proof.stacks_project.Chap10.Lemma_10_55_8
import stacks_proof.stacks_project.Chap10.Lemma_10_78_6
import stacks_proof.stacks_project.Chap15.Definition_15_124_1
import stacks_proof.stacks_project.Chap15.Definition_15_112_1
import stacks_proof.stacks_project.Chap15.Lemma_15_112_2
import stacks_proof.stacks_project.Chap15.Lemma_15_112_4

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open IsExtensionOfValuationRings

universe u v

section

variable {R : Type u}
variable [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsNormalRing R]

/- Domain-style sampling for Lemma 15.124.4:
- primary domain: height-one localizations of Noetherian normal domains and weakly unramified
  extensions of valuation rings;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings`,
  `IsExtensionOfValuationRings`,
  `IsExtensionOfValuationRings.WeaklyUnramified`,
  `Localization.AtPrime.algebraOfLiesOver`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- best owner abstraction: the localized branch should use the discrete-valuation-ring owner
  `IsExtensionOfDiscreteValuationRings`, with the valuation-ring owner
  `IsExtensionOfValuationRings` and the weakly-unramified predicate derived from it; the localized
  algebra is already the canonical `Localization.AtPrime` owner instance from the lying-over
  hypothesis rather than local wrapper data;
- primitive-vs-derived split: the primitive source data are the height-one points
  `p : { p : PrimeSpectrum _ // p.asIdeal.height = 1 }` and
  `q : { q : PrimeSpectrum _ // q.asIdeal.height = 1 }` together with the lying-over condition
  `q.1.asIdeal.LiesOver p.1.asIdeal`; the localized algebra, valuation-ring structure,
  extension-of-discrete-valuation-rings instance, and weakly unramified predicate are derived
  API on that owner.

Source/core/bridge triage:
- `source-facing`: `IsWeaklyUnramifiedHeightOneBranch` and
  `HasWeaklyUnramifiedHeightOneBranches`;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings`, `IsExtensionOfValuationRings`, and
  `IsExtensionOfValuationRings.WeaklyUnramified`;
- `bridge/view`: the canonical localized `Algebra` structure
  `Localization.AtPrime p → Localization.AtPrime q` induced by `q.LiesOver p`. -/

/-- A height-one localization of a Noetherian normal domain is a discrete valuation ring. -/
private instance localizationAtHeightOnePrime_isDiscreteValuationRing
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) := by
  -- Route correction: instead of searching for a separate Dedekind-domain bridge, apply the
  -- dimension-one normal-local clause of Lemma `10.119.7` directly to `R_p`.
  let S := Localization.AtPrime p.1.asIdeal
  have hnormal_dim_one :
      ∃ (_ : IsLocalRing S) (_ : IsNoetherianRing S) (_ : IsDomain S)
        (_ : IsIntegrallyClosed S), ringKrullDim S = 1 := by
    -- The canonical localization inherits the local, Noetherian, domain, and normal owners.
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    -- Height one identifies the local Krull dimension with `1`.
    calc
      ringKrullDim S = ↑p.1.asIdeal.height := by
        simpa [S] using
          (IsLocalization.AtPrime.ringKrullDim_eq_height p.1.asIdeal S)
      _ = (1 : WithBot ℕ∞) := by
        simpa [p.2] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat p.2).symm
  have hdvr : ∃ (_ : IsDomain S), IsDiscreteValuationRing S := by
    -- Clause `(5) → (1)` of the TFAE is exactly the source-local DVR criterion we need.
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
    exact (htfae.out 4 0).mp hnormal_dim_one
  -- The TFAE returns the desired owner instance.
  exact hdvr.choose_spec

end

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsDomain A] [IsDomain B]
variable [IsNormalRing A] [IsNormalRing B]
variable [Module.Flat A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/-- Helper for Lemma 15.124.4: a minimal prime over `(a)` is an associated prime of the quotient
`A / (a)`. -/
private theorem minimal_prime_span_singleton_is_associated
    (a : A) {p : Ideal A} (hp : p ∈ (Ideal.span ({a} : Set A)).minimalPrimes) :
    p ∈ associatedPrimes A (A ⧸ Ideal.span ({a} : Set A)) := by
  -- Rewrite the annihilator of the principal quotient so the standard minimal-prime bridge applies.
  have hp_ann : p ∈ (Module.annihilator A (A ⧸ Ideal.span ({a} : Set A))).minimalPrimes := by
    simpa [Ideal.annihilator_quotient] using hp
  exact
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      A (A ⧸ Ideal.span ({a} : Set A)) hp_ann

/-- Helper for Lemma 15.124.4: every minimal prime over `(a)` has height exactly `1` when `a` is
nonzero. -/
private theorem minimal_prime_span_singleton_height_eq_one
    (a : A) (ha : a ≠ 0) {p : Ideal A} (hp : p ∈ (Ideal.span ({a} : Set A)).minimalPrimes) :
    p.height = 1 := by
  letI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
  -- Krull's principal ideal theorem bounds the height of a minimal prime over `(a)` by `1`.
  have hp_le_one : p.height ≤ 1 := by
    simpa using
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span ({a} : Set A)) p hp
  -- Since `a ≠ 0`, this prime cannot be minimal in the domain itself.
  have hp_not_minimal : p ∉ minimalPrimes A := by
    intro hpmin
    have hp_eq_bot : p = (⊥ : Ideal A) := by
      simpa [IsDomain.minimalPrimes_eq_singleton_bot A] using hpmin
    have ha_mem_p : a ∈ p := by
      exact hp.1.2 (by simpa using Ideal.mem_span_singleton_self a)
    exact ha (by simpa [hp_eq_bot] using ha_mem_p)
  -- The only remaining finite extended natural below `1` is exactly `1`.
  rcases (ENat.le_coe_iff).1 hp_le_one with ⟨m, hm, hm_le⟩
  have hm_ne_zero : m ≠ 0 := by
    intro hm_zero
    have hp_height_zero : p.height = 0 := by
      simpa [hm_zero] using hm
    have hp_primeHeight_zero : p.primeHeight = 0 := by
      simpa [Ideal.height_eq_primeHeight p] using hp_height_zero
    exact hp_not_minimal ((Ideal.primeHeight_eq_zero_iff).1 hp_primeHeight_zero)
  have hm_eq_one : m = 1 := by
    omega
  simpa [hm_eq_one] using hm

/-- Helper for Lemma 15.124.4: the minimal primes over `(f)` form a finite family of height-one
prime-spectrum points. -/
private theorem principalIdeal_height_one_support_finset
    {f : A} (hf : f ≠ 0) :
    ∃ ps : Finset { p : PrimeSpectrum A // p.asIdeal.height = 1 },
      ∀ P ∈ (Ideal.span ({f} : Set A)).minimalPrimes, ∃ p ∈ ps, p.1.asIdeal = P := by
  classical
  -- The principal quotient has finitely many associated primes, so its minimal primes are finite.
  have hassoc_finite : (associatedPrimes A (A ⧸ Ideal.span ({f} : Set A))).Finite :=
    associatedPrimes.finite A (A ⧸ Ideal.span ({f} : Set A))
  have hmin_finite : ((Ideal.span ({f} : Set A)).minimalPrimes).Finite := by
    refine hassoc_finite.subset ?_
    intro P hP
    exact minimal_prime_span_singleton_is_associated (A := A) f hP
  let s : Finset (Ideal A) := hmin_finite.toFinset
  let toHeightOne :
      { P : Ideal A // P ∈ s } → { p : PrimeSpectrum A // p.asIdeal.height = 1 } :=
    fun P ↦
      let hP : P.1 ∈ (Ideal.span ({f} : Set A)).minimalPrimes := by
        exact (Set.Finite.mem_toFinset hmin_finite).1 P.2
      ⟨⟨P.1, Ideal.minimalPrimes_isPrime hP⟩,
        minimal_prime_span_singleton_height_eq_one (A := A) f hf hP⟩
  let ps : Finset { p : PrimeSpectrum A // p.asIdeal.height = 1 } := s.attach.image toHeightOne
  refine ⟨ps, ?_⟩
  intro P hP
  have hP_mem_s : P ∈ s := (Set.Finite.mem_toFinset hmin_finite).2 hP
  let P' : { P : Ideal A // P ∈ s } := ⟨P, hP_mem_s⟩
  -- Repackage each minimal prime ideal as its corresponding height-one point of `Spec A`.
  refine ⟨toHeightOne P', ?_, rfl⟩
  exact Finset.mem_image.mpr ⟨P', by simp, rfl⟩

/-- Helper for Lemma 15.124.4: multiplying by a unit does not change the associated class. -/
private lemma associated_of_unit_mul_left {M : Type*} [CommMonoid M] (u : Units M) (x : M) :
    Associated ((u : M) * x) x := by
  -- Cancel the displayed unit on the right to witness the association.
  refine ⟨u⁻¹, ?_⟩
  simp [mul_assoc, mul_comm]

/-- Helper for Lemma 15.124.4: an association can be rewritten as equality up to a left unit. -/
private lemma eq_unit_mul_of_associated {M : Type*} [CommMonoid M] {x y : M}
    (hxy : Associated x y) :
    ∃ u : Units M, x = (u : M) * y := by
  -- Reverse the association so the unit multiplies the target into the source.
  rcases hxy.symm with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-- Helper for Lemma 15.124.4: associated elements generate the same principal ideal. -/
private theorem span_singleton_eq_span_singleton_of_associated
    {R : Type*} [CommRing R] {x y : R} (hxy : Associated x y) :
    Ideal.span ({x} : Set R) = Ideal.span ({y} : Set R) := by
  rcases eq_unit_mul_of_associated hxy with ⟨u, hu⟩
  rcases eq_unit_mul_of_associated hxy.symm with ⟨v, hv⟩
  apply le_antisymm
  · -- Rewrite the source generator as a unit multiple of `y`.
    refine Ideal.span_le.2 ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [hu]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self y)
  · -- Symmetrically, `y` is a unit multiple of `x`.
    refine Ideal.span_le.2 ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [hv]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)

/-- Helper for Lemma 15.124.4: if the target-side factorization has exponent `0`, then `f` is
already a unit in `A`, so the source factorization is immediate. -/
private theorem exists_unit_mul_pow_of_target_zero_exponent
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B}
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ 0) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ 0 := by
  rcases hpow with ⟨w, hw⟩
  -- Rewrite the target equality to expose that `algebraMap A B f` is already a unit.
  rw [pow_zero, mul_one] at hw
  have hunitB : IsUnit (algebraMap A B f) := hw ▸ w.isUnit
  have hunitA : IsUnit f := isUnit_of_map_unit (algebraMap A B) f hunitB
  rcases hunitA with ⟨u, hu⟩
  -- Choose `g = 1`; then the desired source factorization is just the unit expression for `f`.
  refine ⟨1, u, ?_⟩
  simpa [pow_zero] using hu.symm

/-- Helper for Lemma 15.124.4: if `f = 0` and `n > 0`, then `f` is trivially a unit times an
`n`-th power in `A`. -/
private theorem exists_unit_mul_pow_of_eq_zero
    {f : A} {n : ℕ} (hf : f = 0) (hn : 0 < n) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ n := by
  subst hf
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  -- With positive exponent, choosing `g = 0` and the trivial unit closes the equality.
  refine ⟨0, 1, ?_⟩
  simp

/-- The canonical localized algebra for a height-one branch `q` lying over `p`. -/
private noncomputable instance localizationAtHeightOnePrime_algebra
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) :
    Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
  (Localization.localRingHom p.1.asIdeal q.1.asIdeal (algebraMap A B)
    (Ideal.over_def q.1.asIdeal p.1.asIdeal)).toAlgebra

/-- A height-one branch lying over another height-one branch induces an extension of discrete
valuation rings on localizations. -/
private instance localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) :
    IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) := by
  let _ : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    localizationAtHeightOnePrime_algebra p q hq
  refine
    { toIsLocalHom := ?_
      algebraMap_injective := ?_ }
  · -- The canonical branch map is the local ring hom induced by the lying-over equality.
    simpa [RingHom.algebraMap_toAlgebra] using
      Localization.isLocalHom_localRingHom p.1.asIdeal q.1.asIdeal (algebraMap A B)
        (Ideal.over_def q.1.asIdeal p.1.asIdeal)
  · -- Flatness plus locality upgrades the localized map to faithfully flat, hence injective.
    let _ :
        Module.FaithfullyFlat (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime q.1.asIdeal) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective _ _

variable (A) (B) in
/-- A height-one branch `q` over `p` is weakly unramified when the induced localization
`A_p → B_q` is weakly unramified. -/
def IsWeaklyUnramifiedHeightOneBranch
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) : Prop :=
  letI : q.1.asIdeal.LiesOver p.1.asIdeal := hq
  let _ : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    localizationAtHeightOnePrime_algebra p q hq
  let _ : IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q hq
  WeaklyUnramified (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal)

variable (A) (B) in
/-- Every height-one prime of `A` admits a height-one branch in `B` whose localized extension is
weakly unramified. -/
def HasWeaklyUnramifiedHeightOneBranches : Prop :=
  ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
    ∃ q : { q : PrimeSpectrum B // q.asIdeal.height = 1 },
      ∃ hq : q.1.asIdeal.LiesOver p.1.asIdeal,
        IsWeaklyUnramifiedHeightOneBranch A B p q hq

/-- Helper for Lemma 15.124.4: after localizing the target-side equality at a height-one prime of
`B`, the localized image of `f` is associated to an `n`-fold power of a chosen target
uniformizer. -/
private theorem localized_target_factorization_associated
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hf : f ≠ 0) (hn : 0 < n)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n)
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (πq : Localization.AtPrime q.1.asIdeal)
    (hπq : maximalIdeal (Localization.AtPrime q.1.asIdeal) =
      Ideal.span ({πq} : Set (Localization.AtPrime q.1.asIdeal))) :
    ∃ b : ℕ,
      Associated
        (algebraMap A (Localization.AtPrime q.1.asIdeal) f)
        (πq ^ (b * n)) := by
  let Bq := Localization.AtPrime q.1.asIdeal
  have hff : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hfq : algebraMap A Bq f ≠ 0 := by
    intro hzero
    have hinjBq : Function.Injective (algebraMap B Bq) :=
      IsLocalization.injective Bq q.1.asIdeal.primeCompl_le_nonZeroDivisors
    have hfB : algebraMap A B f = 0 := by
      apply hinjBq
      calc
        algebraMap B Bq (algebraMap A B f) = algebraMap A Bq f := by
          simpa [Bq, RingHom.comp_apply] using
            (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B Bq) f).symm
        _ = algebraMap A Bq 0 := by
          simpa using hzero
        _ = algebraMap B Bq 0 := by
          simp [Bq, RingHom.comp_apply]
    exact hf (hinjAB (by simpa using hfB))
  rcases hpow with ⟨w, hw⟩
  have hEqq :
      algebraMap A Bq f =
        ((Units.map (algebraMap B Bq).toMonoidHom w : Units Bq) : Bq) *
          (algebraMap B Bq h) ^ n := by
    -- Localize the given target equality at `q`.
    calc
      algebraMap A Bq f = algebraMap B Bq (algebraMap A B f) := by
        simpa [Bq, RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B Bq) f
      _ = algebraMap B Bq ((w : B) * h ^ n) := by
        rw [hw]
      _ =
          ((Units.map (algebraMap B Bq).toMonoidHom w : Units Bq) : Bq) *
            (algebraMap B Bq h) ^ n := by
              simp [Bq, map_mul]
  have hhq : algebraMap B Bq h ≠ 0 := by
    intro hhq
    have : algebraMap A Bq f = 0 := by
      rw [hEqq, hhq]
      simp [hn.ne']
    exact hfq this
  obtain ⟨b, hb⟩ :=
    associated_uniformizer_pow_of_nonzero πq (algebraMap B Bq h) hπq hhq
  -- Normalize the localized target factorization by discarding the unit and collecting powers.
  refine ⟨b, ?_⟩
  refine Associated.trans (associated_of_eq hEqq) ?_
  refine Associated.trans
    (associated_of_unit_mul_left (Units.map (algebraMap B Bq).toMonoidHom w)
      ((algebraMap B Bq h) ^ n)) ?_
  have hpowAssoc : Associated ((algebraMap B Bq h) ^ n) ((πq ^ b) ^ n) := by
    simpa using associated_pow hb n
  exact Associated.trans hpowAssoc (by
    simpa using associated_of_eq (pow_mul πq b n).symm)

/-- Helper for Lemma 15.124.4: for DVR extensions, equality of mapped maximal ideals makes the
chosen source and target uniformizers associated. -/
private theorem uniformizer_image_associated_of_map_maximalIdeal
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    {πR : R} {πS : S}
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S)
    (hπR : maximalIdeal R = Ideal.span ({πR} : Set R))
    (hπS : maximalIdeal S = Ideal.span ({πS} : Set S)) :
    Associated (algebraMap R S πR) πS := by
  -- Convert the maximal-ideal equality into the DVR-side weakly unramified owner.
  have hweak : IsExtensionOfDiscreteValuationRings.WeaklyUnramified R S := by
    rw [IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal]
    exact hmap
  have hram : IsExtensionOfDiscreteValuationRings.ramificationIndex R S = 1 :=
    (IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_ramificationIndex_eq_one
      (A := R) (B := S)).1 hweak
  -- The ramification-index comparison theorem from Lemma `15.112.4` now collapses to exponent `1`.
  have hassoc :
      Associated (algebraMap R S πR)
        (πS ^ IsExtensionOfDiscreteValuationRings.ramificationIndex R S) :=
    uniformizer_image_associated_uniformizer_pow_ramificationIndex
      (A := R) (B := S) πR πS hπR hπS
  rw [hram] at hassoc
  simpa using hassoc

/-- Helper for Lemma 15.124.4: inside a DVR target, a unit times an `n`-th power has the same
uniformizer exponent as an `n`-fold multiple. -/
private theorem target_factorization_associated_in_dvr
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    {x : R} {y : S} {n : ℕ}
    (hx : x ≠ 0) (hn : 0 < n)
    (hpow : ∃ w : Sˣ, algebraMap R S x = (w : S) * y ^ n)
    (πS : S)
    (hπS : maximalIdeal S = Ideal.span ({πS} : Set S)) :
    ∃ b : ℕ, Associated (algebraMap R S x) (πS ^ (b * n)) := by
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have hxS : algebraMap R S x ≠ 0 := by
    intro hxS
    exact hx (hinj (by simpa using hxS))
  rcases hpow with ⟨w, hw⟩
  have hyS : y ≠ 0 := by
    intro hyS
    have : algebraMap R S x = 0 := by
      rw [hw, hyS]
      simp [hn.ne']
    exact hxS this
  obtain ⟨b, hb⟩ := associated_uniformizer_pow_of_nonzero (R := S) πS y hπS hyS
  -- Discard the explicit unit and rewrite the target factorization in terms of `πS`.
  refine ⟨b, ?_⟩
  refine Associated.trans (associated_of_eq hw) ?_
  refine Associated.trans (associated_of_unit_mul_left w (y ^ n)) ?_
  have hpowAssoc : Associated (y ^ n) ((πS ^ b) ^ n) := by
    simpa using associated_pow hb n
  exact Associated.trans hpowAssoc (by
    simpa using associated_of_eq (pow_mul πS b n).symm)

/-- Helper for Lemma 15.124.4: over a weakly unramified DVR branch, a source element that becomes
an `n`-th power up to unit in the target is already an `n`-th power up to unit in the source. -/
private theorem exists_unit_mul_pow_in_source_dvr_of_map_maximalIdeal
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    {x : R} {y : S} {n : ℕ}
    (hx : x ≠ 0) (hn : 0 < n)
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S)
    (hpow : ∃ w : Sˣ, algebraMap R S x = (w : S) * y ^ n) :
    ∃ g : R, ∃ u : Rˣ, x = (u : R) * g ^ n := by
  obtain ⟨πR, -, hπR⟩ := exists_uniformizer_generator R
  obtain ⟨πS, -, hπS⟩ := exists_uniformizer_generator S
  obtain ⟨m, hm⟩ := associated_uniformizer_pow_of_nonzero (R := R) πR x hπR hx
  obtain ⟨b, hb⟩ := target_factorization_associated_in_dvr
    (R := R) (S := S) hx hn hpow πS hπS
  have hmapπ : Associated (algebraMap R S πR) πS :=
    uniformizer_image_associated_of_map_maximalIdeal
      (R := R) (S := S) hmap hπR hπS
  have hsourceS : Associated (algebraMap R S x) ((algebraMap R S πR) ^ m) := by
    simpa [RingHom.map_pow] using associated_map (algebraMap R S).toMonoidHom hm
  have hsourceS' : Associated (algebraMap R S x) (πS ^ m) := by
    refine Associated.trans hsourceS ?_
    simpa using associated_pow hmapπ m
  -- Compare the two target-side uniformizer exponents to recover divisibility by `n`.
  have hexp : m = b * n :=
    uniformizer_power_associated_injective (R := S) πS hπS
      (Associated.trans (Associated.symm hsourceS') hb)
  have hsourceR : Associated x (πR ^ (b * n)) := by
    simpa [hexp] using hm
  have hpowR : Associated (πR ^ (b * n)) ((πR ^ b) ^ n) := by
    simpa using associated_of_eq (pow_mul πR b n)
  obtain ⟨u, hu⟩ := eq_unit_mul_of_associated (Associated.trans hsourceR hpowR)
  exact ⟨πR ^ b, u, hu⟩

/-- Helper for Lemma 15.124.4: valuation-side weak unramifiedness forces valuation ramification
index `1` on a localized DVR branch. -/
private theorem valuation_weaklyUnramified_ramificationIndex_eq_one
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    (hweak : IsExtensionOfValuationRings.WeaklyUnramified R S) :
    IsExtensionOfValuationRings.ramificationIndex R S = 1 := by
  let f := ValuativeExtension.mapValueGroupWithZero (FractionRing R) (FractionRing S)
  let ΓS := ValuativeRel.ValueGroupWithZero (FractionRing S)
  have hvalueGroup_top : MonoidWithZeroHom.valueGroup f = ⊤ := by
    -- Surjectivity puts every target value-group unit directly into the source image subgroup.
    rw [Subgroup.eq_top_iff']
    intro γ
    apply Subgroup.subset_closure
    rcases hweak.surjective (γ : ΓS) with ⟨δ, hδ⟩
    exact ⟨δ, hδ⟩
  have hsubsingleton : Subsingleton (ΓSˣ ⧸ MonoidWithZeroHom.valueGroup f) := by
    -- Once the value-group image is all of `ΓSˣ`, the quotient has a single class.
    rw [hvalueGroup_top]
    refine ⟨?_⟩
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact (QuotientGroup.eq).2 (by simp)
  letI := hsubsingleton
  letI : Fintype (ΓSˣ ⧸ MonoidWithZeroHom.valueGroup f) :=
    Fintype.ofSubsingleton (QuotientGroup.mk (1 : ΓSˣ))
  -- Read the valuation-side ramification index as the cardinality of that singleton quotient.
  calc
    IsExtensionOfValuationRings.ramificationIndex R S =
        ENat.card (ΓSˣ ⧸ MonoidWithZeroHom.valueGroup f) := by
          simp [IsExtensionOfValuationRings.ramificationIndex, f, ΓS]
    _ = 1 := by
      rw [ENat.card_eq_coe_fintype_card]
      norm_num [Fintype.card_ofSubsingleton (QuotientGroup.mk (1 : ΓSˣ))]

/-- Helper for Lemma 15.124.4: the canonical value group of the fraction field of a DVR agrees
with the adic value group of its maximal-ideal valuation. -/
private noncomputable instance dvr_fractionRingValuativeRel (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ValuativeRel (FractionRing R) :=
  ValuativeRel.ofValuation
    ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R))

/-- Helper for Lemma 15.124.4: the adic valuation on the fraction field of a DVR is compatible
with the canonical valuative relation. -/
private instance dvr_fractionRing_valuation_compatible (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Valuation.Compatible
      ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)) :=
  Valuation.Compatible.ofValuation
    ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R))

/-- Helper for Lemma 15.124.4: the canonical value group of the fraction field of a DVR agrees
with the adic value group of its maximal-ideal valuation. -/
private noncomputable def dvr_canonical_value_group_orderMonoidIso_adic (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ValuativeRel.ValueGroupWithZero (FractionRing R) ≃*o
      MonoidWithZeroHom.ValueGroup₀
        ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)) :=
  ValuativeRel.ValueGroupWithZero.orderMonoidIso
    ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R))

/-- Helper for Lemma 15.124.4: the canonical/adic value-group transport sends the canonical
valuation class of a fraction to its adic valuation class. -/
private lemma dvr_canonical_value_group_orderMonoidIso_adic_valuation (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (x : FractionRing R) :
    dvr_canonical_value_group_orderMonoidIso_adic (R := R)
        (ValuativeRel.valuation (FractionRing R) x) =
      ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)).restrict x := by
  -- The transport is defined so that the canonical and adic valuations agree after conversion.
  simpa [dvr_canonical_value_group_orderMonoidIso_adic, Valuation.restrict_def] using
    (ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀
      (((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R))) x)

/-- Helper for Lemma 15.124.4: transporting units along the canonical/adic value-group
identification sends the nonzero canonical valuation class of a fraction to the corresponding
nonzero adic valuation class. -/
private noncomputable def dvr_canonical_value_group_units_mulEquiv_adic (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    (ValuativeRel.ValueGroupWithZero (FractionRing R))ˣ ≃*
      (MonoidWithZeroHom.ValueGroup₀
        ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)))ˣ :=
  (OrderMonoidIso.unitsCongr
    (dvr_canonical_value_group_orderMonoidIso_adic (R := R))).toMulEquiv

/-- Helper for Lemma 15.124.4: the units-level canonical/adic transport respects `Units.mk0` on
nonzero valuation classes. -/
private lemma dvr_canonical_value_group_unit_transport_mk0 (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : FractionRing R} (hx : x ≠ 0) :
    dvr_canonical_value_group_units_mulEquiv_adic (R := R)
      (Units.mk0 (ValuativeRel.valuation (FractionRing R) x) (by simpa [hx])) =
        Units.mk0 (((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)).restrict x) (by
          -- The restricted adic valuation of a nonzero fraction is nonzero because valuation and
          -- restriction have the same zero locus.
          intro hzero
          have hzero' :
              ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)) x = 0 :=
            (Valuation.restrict_eq_zero_iff
              (v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R))).1 hzero
          exact ((Valuation.ne_zero_iff
            ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R))).2 hx) hzero') := by
  -- Reduce the units statement to the already-established equality on underlying values.
  ext
  simp [dvr_canonical_value_group_units_mulEquiv_adic,
    dvr_canonical_value_group_orderMonoidIso_adic_valuation, Valuation.restrict_def]

/-- Helper for Lemma 15.124.4: associated elements in a valuation subring have identical adic
valuations because the associating unit has valuation `1`. -/
private lemma valuationSubring_valuation_eq_of_associated
    {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (V : ValuationSubring K) {x y : V} (hxy : Associated x y) :
    V.valuation x = V.valuation y := by
  rcases hxy with ⟨u, hu⟩
  -- Rewrite through the valuation and cancel the unit contribution.
  calc
    V.valuation x = V.valuation x * 1 := by simp
    _ = V.valuation x * V.valuation u := by rw [V.valuation_unit u]
    _ = V.valuation (x * u) := by rw [map_mul]
    _ = V.valuation y := by
          have hu' : (x * ↑u : V) = y := hu
          have hcoe : (((x * ↑u : V) : K)) = y := congrArg Subtype.val hu'
          exact congrArg V.valuation hcoe

/-- Helper for Lemma 15.124.4: in the target adic valuation model, the image of a chosen source
uniformizer has the same valuation as the ramification-index power of a chosen target
uniformizer. -/
private theorem branch_target_adic_valuation_uniformizer_image_pow
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    {πR : R} {πS : S}
    (hπR : maximalIdeal R = Ideal.span ({πR} : Set R))
    (hπS : maximalIdeal S = Ideal.span ({πS} : Set S)) :
    let F := FractionRing S
    let v := (IsDiscreteValuationRing.maximalIdeal S).valuation F
    let e : S ≃+* v.valuationSubring :=
      IsDiscreteValuationRing.equivValuationSubring (A := S) (K := F)
    v.valuationSubring.valuation (e (algebraMap R S πR)) =
      (v.valuationSubring.valuation (e πS)) ^
        IsExtensionOfDiscreteValuationRings.ramificationIndex R S := by
  let F := FractionRing S
  let v := (IsDiscreteValuationRing.maximalIdeal S).valuation F
  let e : S ≃+* v.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := S) (K := F)
  have hassoc :
      Associated (e (algebraMap R S πR))
        ((e πS) ^ IsExtensionOfDiscreteValuationRings.ramificationIndex R S) := by
    -- First rewrite the source uniformizer image through the DVR ramification-index theorem.
    simpa [RingHom.map_pow] using
      associated_map e.toMonoidHom
        (uniformizer_image_associated_uniformizer_pow_ramificationIndex
          (A := R) (B := S) πR πS hπR hπS)
  -- Association inside the adic valuation subring exactly preserves valuation.
  calc
    v.valuationSubring.valuation (e (algebraMap R S πR)) =
        v.valuationSubring.valuation
          ((e πS) ^ IsExtensionOfDiscreteValuationRings.ramificationIndex R S) := by
            exact
              valuationSubring_valuation_eq_of_associated
                (Γ := MonoidWithZeroHom.ValueGroup₀ v)
                (V := v.valuationSubring) hassoc
    _ =
        (v.valuationSubring.valuation (e πS)) ^
          IsExtensionOfDiscreteValuationRings.ramificationIndex R S := by
            rw [map_pow]

/-- Helper for Lemma 15.124.4: on a localized height-one branch, valuation-side weak
unramifiedness already implies the DVR-side weakly unramified owner needed downstream. -/
private theorem height_one_branch_dvr_weakly_unramified_of_valuation_weakly_unramified
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal)
    (hweak : IsWeaklyUnramifiedHeightOneBranch A B p q hq) :
    let Ap := Localization.AtPrime p.1.asIdeal
    let Bq := Localization.AtPrime q.1.asIdeal
    letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
    letI : IsExtensionOfDiscreteValuationRings Ap Bq :=
      localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q hq
    IsExtensionOfDiscreteValuationRings.WeaklyUnramified Ap Bq := by
  let Ap := Localization.AtPrime p.1.asIdeal
  let Bq := Localization.AtPrime q.1.asIdeal
  letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
  letI : IsExtensionOfDiscreteValuationRings Ap Bq :=
    localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q hq
  -- Route correction: the source proof only needs DVR weak unramifiedness, not a full equality
  -- between the valuation-side and DVR-side ramification-index owners.
  have hram_val :
      IsExtensionOfValuationRings.ramificationIndex Ap Bq = 1 :=
    valuation_weaklyUnramified_ramificationIndex_eq_one (R := Ap) (S := Bq) hweak
  have hram_le :
      (IsExtensionOfDiscreteValuationRings.ramificationIndex Ap Bq : ℕ∞) ≤ 1 := by
    -- Compare the chapter-local DVR ramification index with the valuation-ring one.
    calc
      (IsExtensionOfDiscreteValuationRings.ramificationIndex Ap Bq : ℕ∞)
          ≤ IsExtensionOfValuationRings.ramificationIndex Ap Bq := by
            exact
              IsExtensionOfDiscreteValuationRings.valuationRing_ramificationIndex_le
                (A := Ap) (B := Bq)
      _ = 1 := hram_val
  have hram_nat_le_one :
      IsExtensionOfDiscreteValuationRings.ramificationIndex Ap Bq ≤ 1 := by
    -- Convert the `ℕ∞` inequality back to the natural-number owner used by DVR weak
    -- unramifiedness.
    exact ENat.toNat_le_of_le_coe hram_le
  have hram_eq_one :
      IsExtensionOfDiscreteValuationRings.ramificationIndex Ap Bq = 1 := by
    -- Positivity forces the only possible value below or equal to `1` to be exactly `1`.
    refine le_antisymm hram_nat_le_one ?_
    exact Nat.succ_le_of_lt (IsExtensionOfDiscreteValuationRings.ramificationIndex_pos
      (A := Ap) (B := Bq))
  -- Repackage the ramification-index equality in the DVR owner expected downstream.
  exact
    (IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_ramificationIndex_eq_one
      (A := Ap) (B := Bq)).2 hram_eq_one

/-- Helper for Lemma 15.124.4: the remaining branch-local blocker is to turn valuation-side weak
unramifiedness into the DVR-side maximal-ideal equality on localized height-one branches. -/
private theorem weakly_unramified_branch_map_maximalIdeal
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal)
    (hweak : IsWeaklyUnramifiedHeightOneBranch A B p q hq) :
    let Ap := Localization.AtPrime p.1.asIdeal
    let Bq := Localization.AtPrime q.1.asIdeal
    letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
    Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap) = maximalIdeal Bq := by
  let Ap := Localization.AtPrime p.1.asIdeal
  let Bq := Localization.AtPrime q.1.asIdeal
  letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
  letI : IsExtensionOfDiscreteValuationRings Ap Bq :=
    localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q hq
  -- Route correction: consume the weaker branch-local helper directly instead of routing through
  -- a stronger ramification-index owner comparison.
  have hweak_dvr : IsExtensionOfDiscreteValuationRings.WeaklyUnramified Ap Bq :=
    height_one_branch_dvr_weakly_unramified_of_valuation_weakly_unramified
      (A := A) (B := B) p q hq hweak
  -- Finish by the canonical maximal-ideal characterization of DVR weak unramifiedness.
  exact
    (IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal
      (A := Ap) (B := Bq)).1 hweak_dvr

/-- Helper for Lemma 15.124.4: each height-one localization of `A` already has the desired
`n`-th-power decomposition once the branch-local maximal-ideal bridge is supplied. -/
private theorem map_ne_zero_in_height_one_localization
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    {f : A} (hf : f ≠ 0) :
    algebraMap A (Localization.AtPrime p.1.asIdeal) f ≠ 0 := by
  -- The canonical map to a prime localization is injective in a domain, so nonzero elements stay
  -- nonzero after passing to the height-one local ring used in the source proof.
  intro hfAp
  have hinjAp : Function.Injective (algebraMap A (Localization.AtPrime p.1.asIdeal)) :=
    IsLocalization.injective
      (Localization.AtPrime p.1.asIdeal) p.1.asIdeal.primeCompl_le_nonZeroDivisors
  exact hf (hinjAp (by simpa using hfAp))

/-- Helper for Lemma 15.124.4: each height-one localization of `A` already has the desired
`n`-th-power decomposition once the branch-local maximal-ideal bridge is supplied. -/
private theorem exists_unit_mul_pow_in_height_one_localization
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hf : f ≠ 0) (hn : 0 < n)
    (hbranch : HasWeaklyUnramifiedHeightOneBranches A B)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n)
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 }) :
    ∃ g : Localization.AtPrime p.1.asIdeal,
      ∃ u : Units (Localization.AtPrime p.1.asIdeal),
        algebraMap A (Localization.AtPrime p.1.asIdeal) f = (u : _) * g ^ n := by
  rcases hbranch p with ⟨q, hq, hweak⟩
  let Ap := Localization.AtPrime p.1.asIdeal
  let Bq := Localization.AtPrime q.1.asIdeal
  letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
  letI : IsExtensionOfDiscreteValuationRings Ap Bq :=
    localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q hq
  have hmap : Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap) = maximalIdeal Bq :=
    weakly_unramified_branch_map_maximalIdeal (A := A) (B := B) p q hq hweak
  have hfAp : algebraMap A Ap f ≠ 0 :=
    map_ne_zero_in_height_one_localization (A := A) p hf
  have hpowAp :
      ∃ w : Units Bq,
        algebraMap Ap Bq (algebraMap A Ap f) =
          (w : Bq) * (algebraMap B Bq h) ^ n := by
    rcases hpow with ⟨w, hw⟩
    refine ⟨Units.map (algebraMap B Bq).toMonoidHom w, ?_⟩
    -- Localize the target-side factorization along the chosen height-one branch.
    calc
      algebraMap Ap Bq (algebraMap A Ap f) = algebraMap A Bq f := by
        simpa [Ap, Bq, RingHom.comp_apply] using
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A Ap Bq) f).symm
      _ = algebraMap B Bq (algebraMap A B f) := by
        simpa [Bq, RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B Bq) f
      _ = algebraMap B Bq ((w : B) * h ^ n) := by rw [hw]
      _ = ((Units.map (algebraMap B Bq).toMonoidHom w : Units Bq) : Bq) *
            (algebraMap B Bq h) ^ n := by
              simp [map_mul]
  -- With the branch-local maximal-ideal equality in hand, the DVR-local exponent comparison
  -- theorem applies directly.
  exact exists_unit_mul_pow_in_source_dvr_of_map_maximalIdeal
    (R := Ap) (S := Bq) hfAp hn hmap hpowAp

/-- Helper for Lemma 15.124.4: once a height-one localization of `f` is a unit times an `n`-th
power, the uniformizer exponent of `f` in that localization is divisible by `n`. -/
private theorem localized_source_root_associated_target_root
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hf : f ≠ 0) (hn : 0 < n)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n)
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal)
    {g : Localization.AtPrime p.1.asIdeal}
    {u : Units (Localization.AtPrime p.1.asIdeal)}
    (hu : algebraMap A (Localization.AtPrime p.1.asIdeal) f = (u : _) * g ^ n) :
    let Ap := Localization.AtPrime p.1.asIdeal
    let Bq := Localization.AtPrime q.1.asIdeal
    letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
    Associated (algebraMap Ap Bq g) (algebraMap B Bq h) := by
  let Ap := Localization.AtPrime p.1.asIdeal
  let Bq := Localization.AtPrime q.1.asIdeal
  letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
  letI : IsExtensionOfDiscreteValuationRings Ap Bq :=
    localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q hq
  have hfAp : algebraMap A Ap f ≠ 0 :=
    map_ne_zero_in_height_one_localization (A := A) p hf
  have hfBq : algebraMap A Bq f ≠ 0 := by
    -- Nonzero source elements stay nonzero after passing from `A_p` to the chosen DVR branch.
    intro hfBq
    have hinjApBq : Function.Injective (algebraMap Ap Bq) :=
      FaithfulSMul.algebraMap_injective Ap Bq
    apply hfAp
    apply hinjApBq
    calc
      algebraMap Ap Bq (algebraMap A Ap f) = algebraMap A Bq f := by
        simpa [Ap, Bq, RingHom.comp_apply] using
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A Ap Bq) f).symm
      _ = 0 := hfBq
  have hpowAp :
      ∃ w : Units Bq,
        algebraMap A Bq f = (w : Bq) * (algebraMap B Bq h) ^ n := by
    rcases hpow with ⟨w, hw⟩
    refine ⟨Units.map (algebraMap B Bq).toMonoidHom w, ?_⟩
    -- Proof comment: localizing the target factorization along `q` keeps the same `n`-th root.
    calc
      algebraMap A Bq f = algebraMap B Bq (algebraMap A B f) := by
        simpa [Bq, RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B Bq) f
      _ = algebraMap B Bq ((w : B) * h ^ n) := by
        rw [hw]
      _ = ((Units.map (algebraMap B Bq).toMonoidHom w : Units Bq) : Bq) *
            (algebraMap B Bq h) ^ n := by
              simp [map_mul]
  have hpowg :
      ∃ w : Units Bq,
        algebraMap A Bq f = (w : Bq) * (algebraMap Ap Bq g) ^ n := by
    refine ⟨Units.map (algebraMap Ap Bq).toMonoidHom u, ?_⟩
    -- Proof comment: localizing the source-side root factorization transports `g` to the same
    -- branch `B_q`.
    calc
      algebraMap A Bq f = algebraMap Ap Bq (algebraMap A Ap f) := by
        simpa [Ap, Bq, RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A Ap Bq) f
      _ = algebraMap Ap Bq ((u : Ap) * g ^ n) := by
        rw [hu]
      _ = ((Units.map (algebraMap Ap Bq).toMonoidHom u : Units Bq) : Bq) *
            (algebraMap Ap Bq g) ^ n := by
              simp [map_mul]
  have hhq : algebraMap B Bq h ≠ 0 := by
    -- If the target root vanished in `B_q`, then the localized image of `f` would also vanish.
    intro hhq
    rcases hpowAp with ⟨w, hw⟩
    have : algebraMap A Bq f = 0 := by
      rw [hw, hhq]
      simp [hn.ne']
    exact hfBq this
  have hgq : algebraMap Ap Bq g ≠ 0 := by
    -- The same nonvanishing argument applies to the localized source root.
    intro hgq
    rcases hpowg with ⟨w, hw⟩
    have : algebraMap A Bq f = 0 := by
      rw [hw, hgq]
      simp [hn.ne']
    exact hfBq this
  obtain ⟨πq, -, hπq⟩ := exists_uniformizer_generator Bq
  obtain ⟨m, hm⟩ := associated_uniformizer_pow_of_nonzero
    (R := Bq) πq (algebraMap Ap Bq g) hπq hgq
  obtain ⟨k, hk⟩ := associated_uniformizer_pow_of_nonzero
    (R := Bq) πq (algebraMap B Bq h) hπq hhq
  have hf_assoc_g : Associated (algebraMap A Bq f) (πq ^ (m * n)) := by
    rcases hpowg with ⟨w, hw⟩
    -- Proof comment: replacing `g` by a uniformizer power records the branch order of `f`.
    refine Associated.trans (associated_of_eq hw) ?_
    refine Associated.trans (associated_of_unit_mul_left w ((algebraMap Ap Bq g) ^ n)) ?_
    have hpowAssoc : Associated ((algebraMap Ap Bq g) ^ n) ((πq ^ m) ^ n) := by
      simpa using associated_pow hm n
    exact Associated.trans hpowAssoc (by
      simpa using associated_of_eq (pow_mul πq m n).symm)
  have hf_assoc_h : Associated (algebraMap A Bq f) (πq ^ (k * n)) := by
    rcases hpowAp with ⟨w, hw⟩
    -- Proof comment: the original target root gives a second uniformizer-power description of
    -- the same localized element.
    refine Associated.trans (associated_of_eq hw) ?_
    refine Associated.trans (associated_of_unit_mul_left w ((algebraMap B Bq h) ^ n)) ?_
    have hpowAssoc : Associated ((algebraMap B Bq h) ^ n) ((πq ^ k) ^ n) := by
      simpa using associated_pow hk n
    exact Associated.trans hpowAssoc (by
      simpa using associated_of_eq (pow_mul πq k n).symm)
  have hmk_mul : m * n = k * n :=
    uniformizer_power_associated_injective (R := Bq) πq hπq
      (Associated.trans (Associated.symm hf_assoc_g) hf_assoc_h)
  have hmk : m = k := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_gt hn) hmk_mul
  have hk' : Associated (algebraMap B Bq h) (πq ^ m) := by
    simpa [hmk] using hk
  -- Both roots have the same branch order, hence are associated in the target DVR.
  exact Associated.trans hm (Associated.symm hk')

/-- Helper for Lemma 15.124.4: once a height-one localization of `f` is a unit times an `n`-th
power, the uniformizer exponent of `f` in that localization is divisible by `n`. -/
private theorem height_one_localization_associated_uniformizer_pow_mul
    {f : A} {n : ℕ}
    (hf : f ≠ 0) (hn : 0 < n)
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (πp : Localization.AtPrime p.1.asIdeal)
    (hπp : maximalIdeal (Localization.AtPrime p.1.asIdeal) =
      Ideal.span ({πp} : Set (Localization.AtPrime p.1.asIdeal)))
    (hlocalp :
      ∃ g : Localization.AtPrime p.1.asIdeal,
        ∃ u : Units (Localization.AtPrime p.1.asIdeal),
          algebraMap A (Localization.AtPrime p.1.asIdeal) f = (u : _) * g ^ n) :
    ∃ w : ℕ,
      Associated (algebraMap A (Localization.AtPrime p.1.asIdeal) f) (πp ^ (w * n)) := by
  let Ap := Localization.AtPrime p.1.asIdeal
  have hfAp : algebraMap A Ap f ≠ 0 :=
    map_ne_zero_in_height_one_localization (A := A) p hf
  rcases hlocalp with ⟨g, u, hu⟩
  have hg : g ≠ 0 := by
    intro hg
    have : algebraMap A Ap f = 0 := by
      rw [hu, hg]
      simp [hn.ne']
    exact hfAp this
  obtain ⟨w, hw⟩ := associated_uniformizer_pow_of_nonzero (R := Ap) πp g hπp hg
  -- Rewrite the localized factorization through the chosen uniformizer and collect the powers.
  refine ⟨w, ?_⟩
  refine Associated.trans (associated_of_eq hu) ?_
  refine Associated.trans (associated_of_unit_mul_left u (g ^ n)) ?_
  have hpowAssoc : Associated (g ^ n) ((πp ^ w) ^ n) := by
    simpa using associated_pow hw n
  exact Associated.trans hpowAssoc (by
    simpa using associated_of_eq (pow_mul πp w n).symm)

/-- Helper for Lemma 15.124.4: in a DVR, association with a `π^(w * n)`-power forces membership
in the `w`-th power of the maximal ideal. -/
private theorem mem_maximalIdeal_pow_of_associated_uniformizer_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x π : R} {w n : ℕ}
    (hn : 0 < n)
    (hπ : maximalIdeal R = Ideal.span ({π} : Set R))
    (hx : Associated x (π ^ (w * n))) :
    x ∈ maximalIdeal R ^ w := by
  rcases eq_unit_mul_of_associated hx with ⟨u, hu⟩
  rw [hu]
  have hpow_mem_top : π ^ (w * n) ∈ maximalIdeal R ^ (w * n) := by
    -- Rewrite the principal maximal-ideal power so the displayed power belongs by construction.
    rw [hπ, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self (π ^ (w * n))
  have hle : w ≤ w * n := by
    -- Positivity of `n` is exactly what lets the source order drop from `w * n` to `w`.
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left hn w
  have hpow_mem : π ^ (w * n) ∈ maximalIdeal R ^ w :=
    (Ideal.pow_le_pow_right hle) hpow_mem_top
  -- Multiplying by a unit does not change membership in the ideal.
  exact Ideal.mul_mem_left _ _ hpow_mem

/-- Helper for Lemma 15.124.4: in an extension of discrete valuation rings, extending the `w`-th
power of the source maximal ideal gives the `(e * w)`-th power of the target maximal ideal, where
`e` is the ramification index. -/
private theorem map_maximalIdeal_pow_eq_ramification_power
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    (w : ℕ) :
    Ideal.map (algebraMap R S) (maximalIdeal R ^ w) =
      maximalIdeal S ^
        (IsExtensionOfDiscreteValuationRings.ramificationIndex R S * w) := by
  obtain ⟨πR, -, hπR⟩ := exists_uniformizer_generator R
  obtain ⟨πS, -, hπS⟩ := exists_uniformizer_generator S
  let e : ℕ := IsExtensionOfDiscreteValuationRings.ramificationIndex R S
  have hassoc :
      Associated (algebraMap R S πR) (πS ^ e) := by
    -- Rewrite the mapped source uniformizer through the canonical ramification-index formula.
    simpa [e] using
      uniformizer_image_associated_uniformizer_pow_ramificationIndex
        (A := R) (B := S) πR πS hπR hπS
  have hmap_span :
      Ideal.map (algebraMap R S) (maximalIdeal R ^ w) =
        Ideal.span ({(algebraMap R S πR) ^ w} : Set S) := by
    -- Convert the source maximal-ideal power to a principal ideal before mapping it.
    calc
      Ideal.map (algebraMap R S) (maximalIdeal R ^ w)
          = Ideal.map (algebraMap R S) (Ideal.span ({πR ^ w} : Set R)) := by
              rw [hπR, Ideal.span_singleton_pow]
      _ = Ideal.span ({algebraMap R S (πR ^ w)} : Set S) := by
            simpa [Set.image_singleton] using
              (Ideal.map_span (algebraMap R S) ({πR ^ w} : Set R))
      _ = Ideal.span ({(algebraMap R S πR) ^ w} : Set S) := by
            simp [map_pow]
  have htarget_span :
      Ideal.span ({(algebraMap R S πR) ^ w} : Set S) =
        Ideal.span ({(πS ^ e) ^ w} : Set S) := by
    -- Replace the mapped source uniformizer by the associated target uniformizer power.
    exact
      span_singleton_eq_span_singleton_of_associated
        (associated_pow hassoc w)
  -- Collect the principal generators into the target maximal-ideal power.
  calc
    Ideal.map (algebraMap R S) (maximalIdeal R ^ w)
        = Ideal.span ({(algebraMap R S πR) ^ w} : Set S) := hmap_span
    _ = Ideal.span ({(πS ^ e) ^ w} : Set S) := htarget_span
    _ = Ideal.span ({πS ^ (e * w)} : Set S) := by rw [pow_mul]
    _ = maximalIdeal S ^ (e * w) := by
          rw [hπS, Ideal.span_singleton_pow]

/-- Helper for Lemma 15.124.4: along the flat map `A → B`, the finite intersection defining the
source divisor ideal can be mapped factorwise. -/
private theorem map_iInf_height_one_support_factors
    (ps : Finset { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (J : (p : ps) → Ideal A) :
    Ideal.map (algebraMap A B) (⨅ p : ps, J p) =
      ⨅ p : ps, Ideal.map (algebraMap A B) (J p) := by
  classical
  -- Proof comment: the support index is finite, so `Ideal.mapInfTopHom` converts the `iInf`
  -- over `ps` into the corresponding finite infimum of mapped factors.
  simpa [Finset.inf_eq_iInf] using
    (map_finset_inf (f := Ideal.mapInfTopHom (R := A) (S := B)) Finset.univ J)

/-- Helper for Lemma 15.124.4: tensoring the inclusion `I ↪ A` with the flat target `B` stays
injective. -/
private theorem ideal_subtype_rTensor_injective (I : Ideal A) :
    Function.Injective (I.subtype.rTensor B) := by
  -- Flatness is used exactly once here: it prevents the tensor image of `I` from collapsing.
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := B) _ I.subtype_injective

/-- Helper for Lemma 15.124.4: after tensoring an ideal inclusion `I ↪ A` with `B`, the resulting
map lands exactly in the extended ideal `IB`. -/
private theorem ideal_tensor_to_map_range
    (I : Ideal A) :
    ((((TensorProduct.lid A B).toLinearMap).comp (I.subtype.rTensor B)).range :
        Submodule A B) =
      (Ideal.map (algebraMap A B) I : Submodule A B) := by
  -- The standard tensor-range computation identifies the image with `I • ⊤ = IB`.
  simpa [Ideal.smul_top_eq_map] using Ideal.subtype_rTensor_range (M := B) I

/-- Helper for Lemma 15.124.4: the base change `I ⊗[A] B` is canonically identified with the
extended ideal `IB`. -/
private noncomputable def ideal_tensor_map_linearEquiv
    (I : Ideal A) :
    TensorProduct A I B ≃ₗ[A] (Ideal.map (algebraMap A B) I : Submodule A B) := by
  let φ : TensorProduct A I B →ₗ[A] B :=
    ((TensorProduct.lid A B).toLinearMap).comp (I.subtype.rTensor B)
  have hφinj : Function.Injective φ := by
    -- First tensor the inclusion `I ↪ A`, then use the canonical identification `A ⊗[A] B ≃ B`.
    exact ((TensorProduct.lid A B).injective.comp (ideal_subtype_rTensor_injective (A := A) (B := B) I))
  have hφrange :
      (φ.range : Submodule A B) =
        (Ideal.map (algebraMap A B) I : Submodule A B) := by
    -- The image is exactly the extended ideal computed in the previous helper.
    simpa [φ] using ideal_tensor_to_map_range (A := A) (B := B) I
  -- Package the injective map together with its computed range into the desired equivalence.
  exact
    (LinearEquiv.ofInjective φ hφinj).trans
      (LinearEquiv.ofEq _ _ hφrange)

/-- Helper for Lemma 15.124.4: in a DVR, once `x` is associated to `π ^ (w * n)` and also equal
to a unit times `g ^ n`, the chosen root `g` is associated to `π ^ w`. -/
private theorem local_root_associated_uniformizer_pow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x g π : R} {w n : ℕ}
    (hx : x ≠ 0) (hn : 0 < n)
    (hπ : maximalIdeal R = Ideal.span ({π} : Set R))
    (hxpow : Associated x (π ^ (w * n)))
    (hroot : ∃ u : Units R, x = (u : R) * g ^ n) :
    Associated g (π ^ w) := by
  rcases hroot with ⟨u, hu⟩
  have hg : g ≠ 0 := by
    -- The chosen local root cannot vanish because it still raises to the nonzero element `x`.
    intro hg
    have : x = 0 := by
      rw [hu, hg]
      simp [hn.ne']
    exact hx this
  obtain ⟨m, hm⟩ := associated_uniformizer_pow_of_nonzero (R := R) π g hπ hg
  have hxpow' : Associated x (π ^ (m * n)) := by
    -- Rewrite the local root factorization through the chosen uniformizer and collect powers.
    refine Associated.trans (associated_of_eq hu) ?_
    refine Associated.trans (associated_of_unit_mul_left u (g ^ n)) ?_
    have hpowAssoc : Associated (g ^ n) ((π ^ m) ^ n) := by
      simpa using associated_pow hm n
    exact Associated.trans hpowAssoc (by
      simpa using associated_of_eq (pow_mul π m n).symm)
  have hmn : m * n = w * n :=
    uniformizer_power_associated_injective (R := R) π hπ
      (Associated.trans (Associated.symm hxpow') hxpow)
  have hmw : m = w := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_gt hn) hmn
  simpa [hmw] using hm

/-- Helper for Lemma 15.124.4: on the height-one branch `q` lying over the supported source prime
`p`, the localized mapped source factor is exactly the principal ideal generated by the localized
target root `h`. -/
private theorem mapped_comap_factor_localization_eq_span_singleton_of_liesOver
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hf : f ≠ 0) (hn : 0 < n)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n)
    (hlocal :
      ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
        ∃ g : Localization.AtPrime p.1.asIdeal,
          ∃ u : Units (Localization.AtPrime p.1.asIdeal),
            algebraMap A (Localization.AtPrime p.1.asIdeal) f = (u : _) * g ^ n)
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (πp : Localization.AtPrime p.1.asIdeal) (w : ℕ)
    (hπw :
      maximalIdeal (Localization.AtPrime p.1.asIdeal) =
          Ideal.span ({πp} : Set (Localization.AtPrime p.1.asIdeal)) ∧
        Associated (algebraMap A (Localization.AtPrime p.1.asIdeal) f) (πp ^ (w * n)))
    (q : { q : PrimeSpectrum B // q.1.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) :
    let Ap := Localization.AtPrime p.1.asIdeal
    let Bq := Localization.AtPrime q.1.asIdeal
    letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
    Ideal.map (algebraMap B Bq)
        (Ideal.map (algebraMap A B)
          (Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w))) =
      Ideal.span ({algebraMap B Bq h} : Set Bq) := by
  let Ap := Localization.AtPrime p.1.asIdeal
  let Bq := Localization.AtPrime q.1.asIdeal
  letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
  rcases hlocal p with ⟨g, u, hu⟩
  have hg_assoc : Associated g (πp ^ w) := by
    -- The source-local root has precisely the chosen branch order `w`.
    exact local_root_associated_uniformizer_pow
      (R := Ap)
      (hx := map_ne_zero_in_height_one_localization (A := A) p hf)
      hn hπw.1 hπw.2 ⟨u, hu⟩
  have hbranch :
      Associated (algebraMap Ap Bq g) (algebraMap B Bq h) := by
    -- Compare the source-local root with the original target root on the matching branch.
    simpa using
      localized_source_root_associated_target_root
        (A := A) (B := B) hf hn hpow p q hq hu
  have hmapg :
      Associated (algebraMap Ap Bq g) ((algebraMap Ap Bq πp) ^ w) := by
    -- Mapping preserves the association between the source-local root and the chosen uniformizer
    -- power.
    simpa [map_pow] using associated_map (algebraMap Ap Bq).toMonoidHom hg_assoc
  have hh :
      Associated (algebraMap B Bq h) ((algebraMap Ap Bq πp) ^ w) := by
    -- Both local roots generate the same principal branch ideal inside `B_q`.
    exact Associated.trans (Associated.symm hbranch) hmapg
  have hfactor :
      Ideal.map (algebraMap B Bq)
          (Ideal.map (algebraMap A B)
            (Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w))) =
        Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap ^ w) := by
    -- First rewrite the composite `A → B → B_q` as `A → B_q`, then pass through `A_p`.
    calc
      Ideal.map (algebraMap B Bq)
          (Ideal.map (algebraMap A B)
            (Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w)))
          =
        Ideal.map (algebraMap A Bq)
          (Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w)) := by
            simpa [Bq, RingHom.comp_apply] using
              (Ideal.map_map (f := algebraMap A B)
                (g := algebraMap B Bq)
                (I := Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w))).symm
      _ =
        Ideal.map (algebraMap Ap Bq)
          (Ideal.map (algebraMap A Ap)
            (Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w))) := by
              simpa [Ap, Bq, RingHom.comp_apply] using
                (Ideal.map_map (f := algebraMap A Ap)
                  (g := algebraMap Ap Bq)
                  (I := Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w)))
      _ = Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap ^ w) := by
            rw [IsLocalization.map_comap p.1.asIdeal.primeCompl Ap (maximalIdeal Ap ^ w)]
  have hmappow :
      Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap ^ w) =
        Ideal.span ({(algebraMap Ap Bq πp) ^ w} : Set Bq) := by
    -- Rewrite the source maximal-ideal power through the chosen uniformizer generator.
    calc
      Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap ^ w)
          =
        Ideal.map (algebraMap Ap Bq) (Ideal.span ({πp ^ w} : Set Ap)) := by
            rw [hπw.1, Ideal.span_singleton_pow]
      _ = Ideal.span ({algebraMap Ap Bq (πp ^ w)} : Set Bq) := by
            simpa [Set.image_singleton] using
              (Ideal.map_span (algebraMap Ap Bq) ({πp ^ w} : Set Ap))
      _ = Ideal.span ({(algebraMap Ap Bq πp) ^ w} : Set Bq) := by
            simp [map_pow]
  -- Replace the localized branch-power generator by the localized target root.
  calc
    Ideal.map (algebraMap B Bq)
        (Ideal.map (algebraMap A B)
          (Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w))) =
      Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap ^ w) := hfactor
    _ = Ideal.span ({(algebraMap Ap Bq πp) ^ w} : Set Bq) := hmappow
    _ = Ideal.span ({algebraMap B Bq h} : Set Bq) := by
          exact span_singleton_eq_span_singleton_of_associated hh.symm

/-- Helper for Lemma 15.124.4: once the height-one local factorizations are known, the remaining
source-faithful step is the divisor-ideal descent back to a global generator in `A`. -/
private theorem nth_root_divisor_ideal_descends_to_generator_and_finishes
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hf : f ≠ 0) (hn : 0 < n)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n)
    (hlocal :
      ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
        ∃ g : Localization.AtPrime p.1.asIdeal,
          ∃ u : Units (Localization.AtPrime p.1.asIdeal),
            algebraMap A (Localization.AtPrime p.1.asIdeal) f = (u : _) * g ^ n) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ n := by
  classical
  obtain ⟨ps, hcover⟩ := principalIdeal_height_one_support_finset (A := A) hf
  have hdivisible :
      ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
        ∀ πp : Localization.AtPrime p.1.asIdeal,
          maximalIdeal (Localization.AtPrime p.1.asIdeal) =
              Ideal.span ({πp} : Set (Localization.AtPrime p.1.asIdeal)) →
            ∃ w : ℕ,
              Associated (algebraMap A (Localization.AtPrime p.1.asIdeal) f)
                (πp ^ (w * n)) := by
    intro p πp hπp
    -- The localized source factorization already records the valuation exponent as an `n`-multiple.
    exact height_one_localization_associated_uniformizer_pow_mul
      (A := A) hf hn p πp hπp (hlocal p)
  have hsupport_orders :
      ∀ p ∈ ps,
        ∃ πp : Localization.AtPrime p.1.asIdeal, ∃ w : ℕ,
          maximalIdeal (Localization.AtPrime p.1.asIdeal) =
              Ideal.span ({πp} : Set (Localization.AtPrime p.1.asIdeal)) ∧
            Associated (algebraMap A (Localization.AtPrime p.1.asIdeal) f) (πp ^ (w * n)) := by
    intro p hp
    -- Choose a uniformizer on each supported height-one localization and record the divisible order
    -- of `f` there; this is the source proof's finite support/exponent package.
    obtain ⟨πp, -, hπp⟩ := exists_uniformizer_generator (Localization.AtPrime p.1.asIdeal)
    obtain ⟨w, hw⟩ := hdivisible p πp hπp
    exact ⟨πp, w, hπp, hw⟩
  let π_of :
      (p : ps) → Localization.AtPrime p.1.1.asIdeal :=
    fun p ↦ Classical.choose (hsupport_orders p.1 p.2)
  let w_of : (p : ps) → ℕ :=
    fun p ↦ Classical.choose (Classical.choose_spec (hsupport_orders p.1 p.2))
  have hπw_of :
      ∀ p : ps,
        maximalIdeal (Localization.AtPrime p.1.1.asIdeal) =
            Ideal.span ({π_of p} : Set (Localization.AtPrime p.1.1.asIdeal)) ∧
          Associated (algebraMap A (Localization.AtPrime p.1.1.asIdeal) f)
            (π_of p ^ (w_of p * n)) := by
    intro p
    -- Unpack the chosen supported branch data once so the later kernel ideal can refer to it
    -- canonically.
    exact Classical.choose_spec (Classical.choose_spec (hsupport_orders p.1 p.2))
  let I : Ideal A :=
    ⨅ p : ps,
      Ideal.comap (algebraMap A (Localization.AtPrime p.1.1.asIdeal))
        (maximalIdeal (Localization.AtPrime p.1.1.asIdeal) ^ w_of p)
  have hmapI_factors :
      Ideal.map (algebraMap A B) I =
        ⨅ p : ps,
          Ideal.map (algebraMap A B)
            (Ideal.comap (algebraMap A (Localization.AtPrime p.1.1.asIdeal))
              (maximalIdeal (Localization.AtPrime p.1.1.asIdeal) ^ w_of p)) := by
    -- Proof comment: before analyzing individual branches, flatten the source divisor ideal under
    -- extension to `B` using the finite-intersection owner from Lemma `10.39.2`.
    simpa [I] using
      map_iInf_height_one_support_factors (A := A) (B := B) ps
        (fun p ↦
          Ideal.comap (algebraMap A (Localization.AtPrime p.1.1.asIdeal))
            (maximalIdeal (Localization.AtPrime p.1.1.asIdeal) ^ w_of p))
  have hf_mem_I : f ∈ I := by
    rw [Ideal.mem_iInf]
    intro p
    -- Each supported height-one localization records that the order of `f` is at least `w_of p`.
    change algebraMap A (Localization.AtPrime p.1.1.asIdeal) f ∈
      maximalIdeal (Localization.AtPrime p.1.1.asIdeal) ^ w_of p
    exact mem_maximalIdeal_pow_of_associated_uniformizer_pow_mul
      (R := Localization.AtPrime p.1.1.asIdeal) hn (hπw_of p).1 (hπw_of p).2
  have hI_ne_bot : I ≠ ⊥ := by
    -- The kernel ideal is already nonzero because it contains the given nonzero element `f`.
    intro hI
    have hf_bot : f ∈ (⊥ : Ideal A) := by
      simpa [I, hI] using hf_mem_I
    exact hf (by simpa using hf_bot)
  have hbranch_assoc :
      ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
        ∀ q : { q : PrimeSpectrum B // q.asIdeal.height = 1 },
          ∀ hq : q.1.asIdeal.LiesOver p.1.asIdeal,
            ∃ g : Localization.AtPrime p.1.asIdeal,
              let Ap := Localization.AtPrime p.1.asIdeal
              let Bq := Localization.AtPrime q.1.asIdeal
              letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p q hq
              Associated (algebraMap Ap Bq g) (algebraMap B Bq h) := by
    intro p q hq
    rcases hlocal p with ⟨g, u, hu⟩
    refine ⟨g, ?_⟩
    -- Route correction: the comparison of the localized source root with `h` is purely a
    -- branch-DVR argument, so it already works for every height-one branch above `p`.
    simpa using
      localized_source_root_associated_target_root
        (A := A) (B := B) hf hn hpow p q hq hu
  have hmatched_factor :
      ∀ p : ps,
        ∀ q : { q : PrimeSpectrum B // q.asIdeal.height = 1 },
          ∀ hq : q.1.asIdeal.LiesOver p.1.1.asIdeal,
            let Ap := Localization.AtPrime p.1.1.asIdeal
            let Bq := Localization.AtPrime q.1.asIdeal
            letI : Algebra Ap Bq := localizationAtHeightOnePrime_algebra p.1 q hq
            Ideal.map (algebraMap B Bq)
                (Ideal.map (algebraMap A B)
                  (Ideal.comap (algebraMap A Ap) (maximalIdeal Ap ^ w_of p))) =
              Ideal.span ({algebraMap B Bq h} : Set Bq) := by
    intro p q hq
    -- The matching support factor already computes to `(h)` after localizing at a branch over `p`.
    simpa [π_of, w_of] using
      mapped_comap_factor_localization_eq_span_singleton_of_liesOver
        (A := A) (B := B) hf hn hpow hlocal p.1 (π_of p) (w_of p) (hπw_of p) q hq
  -- TODO: continue from the explicit divisor ideal `I = ⨅_{p ∈ ps} comap(A → A_p)(m_p^(w_p))`.
  -- Route correction: the finite support, chosen exponents, and nontriviality of `I` are now
  -- established on the source side, and `hbranch_assoc` packages the branchwise fact that every
  -- height-one branch `B_q` above a source point `p` sees the same localized root as `h`. The
  -- new `hmatched_factor` step computes the unique on-branch localized factor exactly as `(h)`.
  -- The tensor-to-extended-ideal bridge is now also packaged as `ideal_tensor_map_linearEquiv`,
  -- so the remaining blocker is reduced to the off-branch `= ⊤` localization computation and the
  -- globalization step turning the resulting q-local ideal equalities into
  -- `Ideal.map (algebraMap A B) I = Ideal.span ({h} : Set B)` via the normal-domain height-one
  -- criterion. Once that equality is proved, the finite-projective descent route can proceed
  -- without reopening any tensor-quotient interface issues.
  sorry

-- Proof sketch: for each height-one point `p` of `Spec A`, use normality and Noetherianness to
-- view `A_p` and the chosen `B_q` as discrete valuation rings. Weak unramifiedness forces the
-- valuation of `f` in `A_p` to be divisible by `n`. Intersect the corresponding symbolic powers
-- over all minimal height-one primes of `f`, tensor the resulting ideal with `B`, and use the
-- flat local hypothesis to descend that this ideal is free of rank one. A generator `g ∈ A` then
-- has local valuations equal to those of `h`, so `f` differs from `g ^ n` by a unit of `A`.
/-- Lemma 15.124.4: let `A → B` be a flat local homomorphism of Noetherian local normal domains.
If `f ∈ A` becomes a unit times an `n`-th power in `B`, and every height-one
prime of `A` has a height-one prime of `B` above it with weakly unramified localized extension,
then `f` is already a unit times an `n`-th power in `A`. -/
@[stacks 0ASI]
theorem exists_unit_mul_pow_in_source_of_exists_unit_mul_pow_in_target
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hbranch : HasWeaklyUnramifiedHeightOneBranches A B)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ n := by
  by_cases hn : n = 0
  · subst hn
    -- The zero-exponent case is separate from the divisor-ideal route: `f` itself is a unit.
    exact exists_unit_mul_pow_of_target_zero_exponent (A := A) (B := B) hpow
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hf : f = 0
  · -- The zero-element case is also immediate once the exponent is positive.
    exact exists_unit_mul_pow_of_eq_zero (A := A) hf hn_pos
  -- Route correction: after removing the degenerate `n = 0` and `f = 0` branches, the remaining
  -- source-faithful task is the positive/nonzero divisor-ideal argument through height-one
  -- localizations.
  have hlocal :
      ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
        ∃ g : Localization.AtPrime p.1.asIdeal,
          ∃ u : Units (Localization.AtPrime p.1.asIdeal),
            algebraMap A (Localization.AtPrime p.1.asIdeal) f = (u : _) * g ^ n :=
    exists_unit_mul_pow_in_height_one_localization
      (A := A) (B := B) hf hn_pos hbranch hpow
  -- The theorem itself now stops at the stabilized source skeleton: the remaining global step is
  -- the divisor-ideal descent recorded in the dedicated helper above.
  exact
    nth_root_divisor_ideal_descends_to_generator_and_finishes
      (A := A) (B := B) hf hn_pos hpow hlocal

end
