import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_106_4
import StacksProject_2024.Chap10.Lemma_10_112_4
import StacksProject_2024.Chap10.Lemma_10_119_10
import StacksProject_2024.Chap10.Lemma_10_119_12_Krull_Akizuki
import StacksProject_2024.Chap10.Lemma_10_120_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]

local notation "B" => integralClosure A L

omit [IsNoetherianRing A] [FiniteDimensional (FractionRing A) L] in
/-- Helper for Chap10 Lemma 10 120 18: the base map into the integral closure is injective because both
rings embed in the ambient field extension `L`. -/
lemma integralClosure_algebraMap_injective :
    Function.Injective (algebraMap A B) := by
  -- Compare `A → B` with the composite map into the ambient field `L`.
  exact algebraMap_injective_of_field_isFractionRing A B (FractionRing A) L

omit [IsNoetherianRing A] in
/-- Helper for Chap10 Lemma 10 120 18: a one-dimensional domain has no nonzero nonmaximal prime ideals. -/
lemma ringDimensionLEOne_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    Ring.DimensionLEOne A := by
  classical
  refine ⟨fun {p} hp0 hpPrime ↦ ?_⟩
  have hupper' : ((p.primeHeight : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    -- The ambient dimension-one hypothesis bounds every prime height by `1`.
    simpa [hdim] using (Ideal.primeHeight_le_ringKrullDim (I := p))
  have hupper : p.primeHeight ≤ 1 := by
    exact_mod_cast hupper'
  have hbot_height : (⊥ : Ideal A).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hlower : (1 : ℕ∞) ≤ p.primeHeight := by
    -- The strict chain `(0) < p` forces positive height.
    simpa [hbot_height] using
      (Ideal.primeHeight_add_one_le_of_lt
        (I := (⊥ : Ideal A)) (J := p) (bot_lt_iff_ne_bot.mpr hp0))
  have hp_height : p.primeHeight = 1 := le_antisymm hupper hlower
  have hne_bot : ringKrullDim A ≠ ⊥ := by
    intro hbot
    have : (1 : WithBot ℕ∞) = ⊥ := by
      simpa [hdim] using hbot
    cases this
  have hne_top : ringKrullDim A ≠ ⊤ := by
    intro htop
    have : (1 : WithBot ℕ∞) = ⊤ := by
      simpa [hdim] using htop
    cases this
  letI : FiniteRingKrullDim A :=
    (finiteRingKrullDim_iff_ne_bot_and_top (R := A)).2 ⟨hne_bot, hne_top⟩
  have hp_height' : (p.primeHeight : WithBot ℕ∞) = ringKrullDim A := by
    simpa [hdim] using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp_height
  exact Ideal.isMaximal_of_primeHeight_eq_ringKrullDim hp_height'

omit [IsNoetherianRing A] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L] in
/-- Helper for Chap10 Lemma 10 120 18: the integral closure stays one-dimensional when the base ring has
Krull dimension `1`. -/
lemma integralClosure_dimensionLEOne_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    Ring.DimensionLEOne B := by
  letI : Ring.DimensionLEOne A := ringDimensionLEOne_of_ringKrullDim_eq_one (A := A) hdim
  -- Dedekind-domain API transports dimension-`≤ 1` across integral closure.
  infer_instance

/- Domain-style sampling:
- primary domain: integral closures in finite extensions of fraction fields of one-dimensional
  Noetherian domains, together with the induced prime-spectrum and residue-field behavior;
- sampled canonical/project owners:
  `IsDedekindDomain`,
  `Algebra.IsIntegral.comap_surjective`,
  `Ideal.primesOver`,
  `Ideal.primesOver_finite`,
  `moduleFinite_residueField_of_primeOver_maximalIdeal_of_finite_fractionField_extension`;
- best owner abstraction: the integral-closure owner `B = integralClosure A L`, with
  `IsDedekindDomain B` as the canonical ambient owner once Lemma `10.120.18` proves it;
- primitive data: the ambient extension tower `A ⊆ FractionRing A ⊆ L` and the owner ring `B`;
- derived API: surjectivity of `Spec(B) → Spec(A)`, finiteness of the fibers `p.primesOver B`,
  and finiteness of the residue-field extensions.

Source/core/bridge triage:
- `source-facing`: the Dedekind-domain, finite-fiber, and residue-field-finiteness statements
  specialized to `B = integralClosure A L` under the source hypothesis `ringKrullDim A = 1`;
- `core/canonical`: `IsDedekindDomain`, `Algebra.IsIntegral.comap_surjective`,
  `Ideal.primesOver_finite`, and the local one-dimensional fiber theorem from
  `Lemma_10_119_10`;
- `bridge/view`: the present file should only keep the source-facing bridges that add the
  dimension-one input. The spectrum-surjectivity clause is an exact canonical recall and should
  not survive as a parallel local theorem.
-/

-- Proof sketch: apply Krull-Akizuki to get that `B` is Noetherian, use integrality of
-- `A → B` to identify `ringKrullDim B = 1`, and then invoke the Dedekind-domain
-- characterization from Lemma `10.120.17`, noting that `B` is integrally closed by construction.
/-- Helper for Chap10 Lemma 10 120 18: if `A` is a one-dimensional Noetherian domain and `L` is a
finite extension of `FractionRing A`, then the integral closure of `A` in `L` is a Dedekind
domain. -/
@[stacks 09IG]
theorem integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    IsDedekindDomain B := by
  letI : IsNoetherianRing B :=
    Subalgebra.isNoetherianRing_of_ringKrullDim_eq_one (A := B) hdim
  letI : Ring.DimensionLEOne B :=
    integralClosure_dimensionLEOne_of_ringKrullDim_eq_one (A := A) (L := L) hdim
  have hIntClosed : IsIntegrallyClosed B :=
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := A) (K := FractionRing A) (L := L)
  -- Assemble the canonical Dedekind criterion using Noetherianity, dimension `≤ 1`,
  -- and integral closedness of the integral closure.
  have hfactor : IsDedekindDomainByFactorization B := by
    exact (isDedekindDomainByFactorization_iff B).2
      ⟨inferInstance, inferInstance, inferInstance, hIntClosed⟩
  exact (isDedekindDomain_iff_isDedekindDomainByFactorization B).2 hfactor

/-- Helper for Chap10 Lemma 10 120 18: a nonzero prime of `A` has only finitely many primes of the
integral closure lying above it. -/
lemma primesOver_finite_of_nonzero_prime
    (hdim : ringKrullDim A = 1) (p : PrimeSpectrum A) (hp0 : p.asIdeal ≠ ⊥) :
    (p.asIdeal.primesOver B).Finite := by
  let pI : Ideal A := p.asIdeal
  letI : Ring.DimensionLEOne A := ringDimensionLEOne_of_ringKrullDim_eq_one (A := A) hdim
  have hpPrime : pI.IsPrime := by
    simpa [pI] using p.isPrime
  letI : pI.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpPrime
  letI : IsDedekindDomain B :=
    integralClosure_isDedekindDomain_of_ringKrullDim_eq_one (A := A) (L := L) hdim
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr integralClosure_algebraMap_injective
  -- Once `p` is maximal and `B` is Dedekind, the standard fiber finiteness theorem applies.
  simpa [pI] using (show (pI.primesOver B).Finite from primesOver_finite pI B)

/- The map `Spec(integralClosure A L) → Spec(A)` induced by the inclusion
`A → integralClosure A L` is exactly the canonical integral-spectrum-surjectivity theorem
`Algebra.IsIntegral.comap_surjective`; the dimension-one hypothesis is redundant here and is
therefore removed from the public API. -/
recall Algebra.IsIntegral.comap_surjective

-- Proof sketch: if `p = 0`, then `B` is a domain and the only prime of `B` over `0` is `0`.
-- If `p ≠ 0`, then `p` is maximal because `A` has Krull dimension `1`; localize at `p` and apply
-- Lemma `10.119.10 (2)` to the resulting one-dimensional Noetherian local domain.
/-- For each `p : Spec(A)`, only finitely many prime ideals of `integralClosure A L` lie over
`p`. -/
theorem integralClosure_primesOver_finite_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    (p.asIdeal.primesOver B).Finite := by
  by_cases hp0 : p.asIdeal = ⊥
  · -- Over the generic point, a domain has only the zero prime.
    letI : Module.IsTorsionFree A B :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr integralClosure_algebraMap_injective
    rw [hp0, Ideal.primesOver_bot A B]
    exact Set.finite_singleton ⊥
  · -- Nonzero primes are maximal in dimension one, so Dedekind fiber finiteness applies.
    exact primesOver_finite_of_nonzero_prime (A := A) (L := L) hdim p hp0

/-- Helper for Chap10 Lemma 10 120 18: the residue field at the generic point of a domain is its
fraction field. -/
noncomputable abbrev bot_residueField_fractionRing_equiv
    {R : Type*} [CommRing R] [IsDomain R] :
    ((⊥ : Ideal R).ResidueField) ≃ₐ[R] FractionRing R := by
  let e : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) := (AlgEquiv.quotientBot R R).symm
  letI : IsFractionRing R ((⊥ : Ideal R).ResidueField) := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap R ((⊥ : Ideal R).ResidueField) x =
      algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    exact show
        algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField)
            (Ideal.Quotient.mk (⊥ : Ideal R) x) =
          algebraMap R ((⊥ : Ideal R).ResidueField) x by
      rfl
  -- The generic residue field is another fraction-field model of `R`.
  exact (FractionRing.algEquiv R ((⊥ : Ideal R).ResidueField)).symm

/-- Helper for Chap10 Lemma 10 120 18: the residue field of a prime localization at its maximal ideal is
the residue field of the original prime. -/
noncomputable abbrev localizationAtPrime_residueField_equiv
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ≃+* p.ResidueField := by
  -- The prime-local ring is local, so Lemma `10.106.4` identifies its maximal-ideal residue
  -- field with the ordinary local-ring residue field.
  change (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime p)
  exact maximalIdealResidueFieldEquiv (Localization.AtPrime p)

omit [IsDomain A] [IsNoetherianRing A] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L] in
/-- Helper for Chap10 Lemma 10 120 18: the closed-point residue-field map after localizing at a prime is
the original residue-field map after the canonical prime-local identifications. -/
lemma localizationAtPrime_residueField_map_compat
    (q : PrimeSpectrum B) :
    let p : Ideal A := (PrimeSpectrum.comap (algebraMap A B) q).asIdeal
    (localizationAtPrime_residueField_equiv (R := B) q.asIdeal).toRingHom.comp
        (Ideal.ResidueField.map
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
          (Localization.localRingHom p q.asIdeal (algebraMap A B) rfl)
          (IsLocalRing.maximalIdeal_comap
            (Localization.localRingHom p q.asIdeal (algebraMap A B) rfl)).symm) =
      (Ideal.ResidueField.map p q.asIdeal (algebraMap A B) rfl).comp
        (localizationAtPrime_residueField_equiv (R := A) p).toRingHom := by
  let p : Ideal A := (PrimeSpectrum.comap (algebraMap A B) q).asIdeal
  -- Both sides are the canonical residue-field map for the local hom on the prime localizations.
  simpa [localizationAtPrime_residueField_equiv, p] using
    (maximalIdealResidueFieldEquiv_comp_residueFieldMap
      (f := Localization.localRingHom p q.asIdeal (algebraMap A B) rfl))

omit [IsNoetherianRing A] in
/-- Helper for Chap10 Lemma 10 120 18: the generic residue-field extension is finite because it
is the given finite fraction-field extension after the canonical generic-point identifications. -/
lemma genericResidueField_moduleFinite
    [IsFractionRing B L]
    (hcomap : Ideal.comap (algebraMap A B) (⊥ : Ideal B) = (⊥ : Ideal A)) :
    let fκ : ((⊥ : Ideal A).ResidueField) →+* ((⊥ : Ideal B).ResidueField) :=
      Ideal.ResidueField.map (⊥ : Ideal A) (⊥ : Ideal B) (algebraMap A B) hcomap.symm
    letI : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := fκ.toAlgebra
    Module.Finite ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := by
  let fκ : ((⊥ : Ideal A).ResidueField) →+* ((⊥ : Ideal B).ResidueField) :=
    Ideal.ResidueField.map (⊥ : Ideal A) (⊥ : Ideal B) (algebraMap A B) hcomap.symm
  letI : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := fκ.toAlgebra
  have hTower :
      IsScalarTower A ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := by
    -- The residue-field map agrees with the original inclusion on elements of the base ring.
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    symm
    change fκ (algebraMap A ((⊥ : Ideal A).ResidueField) a) =
      algebraMap B ((⊥ : Ideal B).ResidueField) (algebraMap A B a)
    exact Ideal.ResidueField.map_algebraMap
      (⊥ : Ideal A) (⊥ : Ideal B) (algebraMap A B) hcomap.symm a
  letI : IsScalarTower A ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := hTower
  let eA : FractionRing A ≃+* ((⊥ : Ideal A).ResidueField) :=
    (bot_residueField_fractionRing_equiv (R := A)).symm.toRingEquiv
  let eBAlg : L ≃ₐ[B] ((⊥ : Ideal B).ResidueField) :=
    (FractionRing.algEquiv B L).symm.trans
      (bot_residueField_fractionRing_equiv (R := B)).symm
  let eB : L ≃+* ((⊥ : Ideal B).ResidueField) := eBAlg.toRingEquiv
  have hcompat :
      RingHom.comp
          (algebraMap ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField)) eA =
        RingHom.comp eB (algebraMap (FractionRing A) L) := by
    -- Fraction-field maps are determined by their values on the original domain.
    ext x
    exact IsFractionRing.algEquiv_commutes
      (bot_residueField_fractionRing_equiv (R := A)).symm eBAlg x
  -- Transport finite generation from `FractionRing A → L` to the two generic residue fields.
  exact Module.Finite.of_equiv_equiv eA eB hcompat

omit [IsNoetherianRing A] [FiniteDimensional (FractionRing A) L] in
/-- Helper for Chap10 Lemma 10 120 18: a nonzero prime of the integral closure has nonzero
contraction to the base domain. -/
lemma comap_ne_bot_of_integralClosure_prime_ne_bot
    (q : PrimeSpectrum B) (hq0 : q.asIdeal ≠ ⊥) :
    (PrimeSpectrum.comap (algebraMap A B) q).asIdeal ≠ (⊥ : Ideal A) := by
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr integralClosure_algebraMap_injective
  intro hp
  have hmem : q.asIdeal ∈ ((⊥ : Ideal A).primesOver B) := by
    -- If the contraction is zero, then `q` lies over the generic point of `Spec A`.
    refine ⟨q.isPrime, ?_⟩
    have hunder : (⊥ : Ideal A) = q.asIdeal.under A := by
      simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using hp.symm
    exact ⟨hunder⟩
  have hqbot : q.asIdeal = (⊥ : Ideal B) := by
    -- Torsion-freeness identifies the generic fiber of the integral closure with `{0}`.
    rw [Ideal.primesOver_bot A B] at hmem
    simpa using hmem
  exact hq0 hqbot

omit [IsNoetherianRing A] in
/-- Helper for Chap10 Lemma 10 120 18: localizing a one-dimensional domain at a nonzero prime
again gives a one-dimensional local domain. -/
lemma localizationAtPrime_ringKrullDim_eq_one_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (p : PrimeSpectrum A) (hp0 : p.asIdeal ≠ ⊥) :
    ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
  have hupper' : ((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    -- The global dimension-one hypothesis bounds the height of every prime by `1`.
    simpa [hdim] using (Ideal.primeHeight_le_ringKrullDim (I := p.asIdeal))
  have hupper : p.asIdeal.primeHeight ≤ 1 := by
    exact_mod_cast hupper'
  have hbot_height : (⊥ : Ideal A).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hlower : (1 : ℕ∞) ≤ p.asIdeal.primeHeight := by
    -- The strict inclusion `(0) < p` forces the localized prime to have positive height.
    simpa [hbot_height] using
      (Ideal.primeHeight_add_one_le_of_lt
        (I := (⊥ : Ideal A)) (J := p.asIdeal) (bot_lt_iff_ne_bot.mpr hp0))
  have hp_height : p.asIdeal.primeHeight = 1 := le_antisymm hupper hlower
  have hp_height' : ((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) = 1 := by
    simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp_height
  calc
    ringKrullDim (Localization.AtPrime p.asIdeal) = p.asIdeal.height := by
      exact IsLocalization.AtPrime.ringKrullDim_eq_height
        p.asIdeal (Localization.AtPrime p.asIdeal)
    _ = (p.asIdeal.primeHeight : WithBot ℕ∞) := by
      rw [Ideal.height_eq_primeHeight]
    _ = 1 := hp_height'

/-- Helper for Chap10 Lemma 10 120 18: if `S / q` is finite over `R`, then the residue-field
extension above maximal ideals `p` and `q` is finite. -/
lemma moduleFinite_residueField_of_moduleFinite_quotient
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : Ideal R} [p.IsMaximal] {q : Ideal S} [q.IsMaximal] [q.LiesOver p]
    (hfin : Module.Finite R (S ⧸ q)) :
    Module.Finite p.ResidueField q.ResidueField := by
  let eResidue : (S ⧸ q) ≃ₐ[S ⧸ q] q.ResidueField :=
    AlgEquiv.ofBijective
      (Algebra.ofId (S ⧸ q) q.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q)
  have hfinite_residue_R : Module.Finite R q.ResidueField := by
    letI : Module.Finite R (S ⧸ q) := hfin
    -- The quotient field `S / q` and the residue field `κ(q)` are the same finite `R`-module.
    exact Module.Finite.equiv (eResidue.toLinearEquiv.restrictScalars R)
  letI : Module.Finite R q.ResidueField := hfinite_residue_R
  -- Since the `R`-action on `κ(q)` factors through `κ(p)`, the same generators work over
  -- the larger scalar field `κ(p)`.
  exact Module.Finite.of_restrictScalars_finite R p.ResidueField q.ResidueField

/-- Helper for Chap10 Lemma 10 120 18: every nonzero quotient of the integral closure is finite
over the base ring in Krull dimension one. -/
lemma moduleFinite_integralClosure_quotient_of_nonzero_ideal
    (hdim : ringKrullDim A = 1) {I : Ideal B} (hI : I ≠ ⊥) :
    Module.Finite A (B ⧸ I) := by
  have hdimLE : ringKrullDim A ≤ 1 := by
    simp [hdim]
  letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdimLE
  obtain ⟨x, hx, hxI⟩ :=
    Subalgebra.exists_nonzero_base_mem_ideal (R := A) (L := L) B I hI
  let J : Ideal B := Ideal.span ({algebraMap A B x} : Set B)
  have hJI : J ≤ I := by
    -- The chosen nonzero base element lies in `I`, so its principal ideal maps into `I`.
    refine Ideal.span_le.2 ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxI
  have hJlen : IsFiniteLength A (B ⧸ J) := by
    -- Krull-Akizuki gives finite length for quotient by a nonzero base scalar.
    simpa [J] using
      Subalgebra.isFiniteLength_quotient_span_base_scalar (R := A) (L := L) B hx
  have hJnoeth : IsNoetherian A (B ⧸ J) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hJlen).1
  haveI : Module.Finite A (B ⧸ J) := by
    -- Finite length supplies the finite generating set for the principal quotient.
    rw [Module.finite_def]
    exact hJnoeth.noetherian _
  -- Push finite generation through the quotient map `B / J -> B / I`.
  exact Module.Finite.of_surjective
    ((Ideal.Quotient.factorₐ A hJI : B ⧸ J →ₐ[A] B ⧸ I).toLinearMap)
    (Ideal.Quotient.factor_surjective hJI)

omit [IsNoetherianRing A] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L] in
/-- Helper for Chap10 Lemma 10 120 18: in the integral closure over a one-dimensional base, every
nonzero prime is maximal. -/
lemma integralClosure_nonzeroPrime_isMaximal_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (q : PrimeSpectrum B) (hq0 : q.asIdeal ≠ ⊥) :
    q.asIdeal.IsMaximal := by
  letI : Ring.DimensionLEOne B :=
    integralClosure_dimensionLEOne_of_ringKrullDim_eq_one (A := A) (L := L) hdim
  -- Dimension `≤ 1` promotes any nonzero prime to a maximal ideal.
  exact Ring.DimensionLEOne.maximalOfPrime hq0 q.isPrime

omit [IsNoetherianRing A] in
/-- Helper for Chap10 Lemma 10 120 18: when `q` is the generic prime of the integral closure, the
residue-field extension should be identified with the ambient finite fraction-field extension. -/
lemma residueField_finite_of_zero_prime
    (hdim : ringKrullDim A = 1) (q : PrimeSpectrum B) (hq0 : q.asIdeal = ⊥) :
    Module.Finite (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := by
  letI : IsFractionRing B L :=
    integralClosure.isFractionRing_of_finite_extension
      (A := A) (K := FractionRing A) (L := L)
  have _hdim := hdim
  have hq_bot : q = (⊥ : PrimeSpectrum B) := by
    -- The source route starts by replacing the generic prime `q` with the unique zero prime.
    apply PrimeSpectrum.ext
    simpa using hq0
  subst q
  have hcomap_bot :
      Ideal.comap (algebraMap A B) (⊥ : Ideal B) = (⊥ : Ideal A) :=
    Ideal.comap_bot_of_injective _ integralClosure_algebraMap_injective
  let fκ : ((⊥ : Ideal A).ResidueField) →+* ((⊥ : Ideal B).ResidueField) :=
    Ideal.ResidueField.map (⊥ : Ideal A) (⊥ : Ideal B) (algebraMap A B) hcomap_bot.symm
  letI : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := fκ.toAlgebra
  -- Route correction: the zero-prime case is reduced to the generic residue-field extension
  -- `κ(0_A) → κ(0_B)`, matching the source proof's fraction-field step.
  -- Keep the actual contracted prime as a named ideal and identify it with `⊥` by residue maps,
  -- rather than dependent-eliminating the ideal equality.
  let pSpec : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) (⊥ : PrimeSpectrum B)
  let p : Ideal A := pSpec.asIdeal
  have hp : p = (⊥ : Ideal A) := by
    simpa [p, pSpec, PrimeSpectrum.comap_asIdeal] using hcomap_bot
  have hlies : (⊥ : Ideal B).LiesOver p := by
    refine ⟨?_⟩
    simpa [p, pSpec, Ideal.under_def, PrimeSpectrum.comap_asIdeal]
  letI : (⊥ : Ideal B).LiesOver p := hlies
  have hbot_comap_id : (⊥ : Ideal A) = Ideal.comap (RingHom.id A) p := by
    simpa [hp]
  have hp_comap_id : p = Ideal.comap (RingHom.id A) (⊥ : Ideal A) := by
    simpa [hp]
  let toMap : ((⊥ : Ideal A).ResidueField) →+* p.ResidueField :=
    Ideal.ResidueField.map (⊥ : Ideal A) p (RingHom.id A) hbot_comap_id
  let invMap : p.ResidueField →+* ((⊥ : Ideal A).ResidueField) :=
    Ideal.ResidueField.map p (⊥ : Ideal A) (RingHom.id A) hp_comap_id
  have h_to_inv : toMap.comp invMap = RingHom.id p.ResidueField := by
    -- The two residue maps induced by the identity are inverse by residue-field extensionality.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext a
    simp [toMap, invMap, Ideal.ResidueField.map_algebraMap]
  have h_inv_to : invMap.comp toMap = RingHom.id ((⊥ : Ideal A).ResidueField) := by
    -- The reverse composite is checked on elements coming from `A`.
    apply Ideal.ResidueField.ringHom_ext (I := (⊥ : Ideal A))
    ext a
    simp [toMap, invMap, Ideal.ResidueField.map_algebraMap]
  let eEq : ((⊥ : Ideal A).ResidueField) ≃+* p.ResidueField :=
    RingEquiv.ofRingHom toMap invMap h_to_inv h_inv_to
  have hfinite_bot :
      Module.Finite ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) :=
    genericResidueField_moduleFinite (A := A) (L := L) hcomap_bot
  have hcompatEq :
      (algebraMap p.ResidueField ((⊥ : Ideal B).ResidueField)).comp eEq.toRingHom =
        (RingEquiv.refl ((⊥ : Ideal B).ResidueField)).toRingHom.comp
          (algebraMap ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField)) := by
    -- Both scalar maps send a base element `a : A` to its image in `κ(0_B)`.
    apply Ideal.ResidueField.ringHom_ext (I := (⊥ : Ideal A))
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change algebraMap p.ResidueField ((⊥ : Ideal B).ResidueField)
        (toMap (algebraMap A ((⊥ : Ideal A).ResidueField) a)) =
      fκ (algebraMap A ((⊥ : Ideal A).ResidueField) a)
    rw [Ideal.ResidueField.map_algebraMap]
    rw [Ideal.ResidueField.map_algebraMap]
    simp only [RingHom.id_apply]
    rw [← IsScalarTower.algebraMap_apply A p.ResidueField ((⊥ : Ideal B).ResidueField) a]
    rw [IsScalarTower.algebraMap_apply A B ((⊥ : Ideal B).ResidueField) a]
  have hfinite_p : Module.Finite p.ResidueField ((⊥ : Ideal B).ResidueField) :=
    Module.Finite.of_equiv_equiv eEq (RingEquiv.refl _) hcompatEq
  -- Transport finite generation from the identified generic residue field back to the goal.
  simpa [p, pSpec] using hfinite_p

/-- Helper for Chap10 Lemma 10 120 18: for a nonzero prime `q`, the finite quotient `B / q` gives a
finite residue-field extension over the contraction. -/
lemma residueField_finite_of_nonzero_prime
    (hdim : ringKrullDim A = 1) (q : PrimeSpectrum B) (hq0 : q.asIdeal ≠ ⊥) :
    Module.Finite (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  have hp0 : p.asIdeal ≠ (⊥ : Ideal A) :=
    comap_ne_bot_of_integralClosure_prime_ne_bot (A := A) (L := L) q hq0
  have hpmax : p.asIdeal.IsMaximal := by
    letI : Ring.DimensionLEOne A := ringDimensionLEOne_of_ringKrullDim_eq_one (A := A) hdim
    -- The nonzero contraction is maximal because the base has Krull dimension one.
    exact Ring.DimensionLEOne.maximalOfPrime hp0 p.isPrime
  have hqmax : q.asIdeal.IsMaximal :=
    integralClosure_nonzeroPrime_isMaximal_of_ringKrullDim_eq_one (A := A) (L := L) hdim q hq0
  have hlies : q.asIdeal.LiesOver p.asIdeal := by
    -- The chosen base prime `p` is definitionally the contraction of `q`.
    have hover : p.asIdeal = q.asIdeal.under A := by
      simpa [p, Ideal.under_def, PrimeSpectrum.comap_asIdeal]
    exact ⟨hover⟩
  letI : p.asIdeal.IsMaximal := hpmax
  letI : q.asIdeal.IsMaximal := hqmax
  letI : q.asIdeal.LiesOver p.asIdeal := hlies
  have hquot : Module.Finite A (B ⧸ q.asIdeal) :=
    moduleFinite_integralClosure_quotient_of_nonzero_ideal (A := A) (L := L) hdim hq0
  -- Route correction: avoid the localized closed-fiber transport and use the finite quotient
  -- `B / q` directly to obtain the residue-field extension.
  simpa [p] using
    moduleFinite_residueField_of_moduleFinite_quotient
      (R := A) (S := B) (p := p.asIdeal) (q := q.asIdeal) hquot

-- Proof sketch: split off the generic point. At a nonzero prime `q`, use Krull-Akizuki to make
-- `B / q` finite over `A`, promote `q` and its contraction to maximal ideals, and pass from the
-- finite quotient to the residue-field extension.
/-- Chap10 Lemma 10 120 18: for each `q : Spec(integralClosure A L)`, the residue field extension
`κ(comap q) → κ(q)` is finite. -/
theorem integralClosure_residueField_finite_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (q : PrimeSpectrum B) :
    Module.Finite (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := by
  by_cases hq0 : q.asIdeal = ⊥
  · -- The generic-point fiber is the fraction-field extension.
    exact residueField_finite_of_zero_prime (A := A) (L := L) hdim q hq0
  · -- Nonzero primes use the finite quotient of the integral closure.
    exact residueField_finite_of_nonzero_prime (A := A) (L := L) hdim q hq0

end
