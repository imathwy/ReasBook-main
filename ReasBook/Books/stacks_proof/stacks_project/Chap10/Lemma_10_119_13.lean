import Mathlib
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import StacksProject_2024.Chap09.Lemma_9_26_11
import StacksProject_2024.Chap10.Lemma_10_42_3
import StacksProject_2024.Chap10.Lemma_10_119_1
import StacksProject_2024.Chap10.Lemma_10_119_12_Krull_Akizuki
import StacksProject_2024.Chap10.Lemma_10_119_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
variable [Algebra.EssFiniteType K L]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-
Domain triage:
* primary domain: valuation subrings of finitely generated field extensions dominating the image of
  a fixed Noetherian local domain;
* sampled owner declarations:
  - `LocalSubring.exists_le_valuationSubring` and `ValuationSubring.toLocalSubring` for the
    domination relation on local subrings of a field;
  - `ValuationSubring.comap` for contraction along `K → L`;
  - `exists_one_dimensional_dominating_essFiniteType_overring_of_not_isField` and
    `discreteValuationRing_iff_regularLocalRing_dim_one` for the chapter's one-dimensional and
    discrete-valuation owners.
* best owner abstraction:
  - `source-facing`: existence of a discrete valuation subring of `L` dominating the image of `R`;
  - `core/canonical`: domination as the order on `LocalSubring L`, together with the owner
    predicate `IsDiscreteValuationRing`.
* primitive vs. derived:
  - primitive data: the witness `V : ValuationSubring L` and the domination inequality
    `LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring`;
  - derived API: the local structure on `V.toLocalSubring`, the intermediate one-dimensional
    overring supplied by Lemma `10.119.1`, and the regular-local reformulation of the DVR
    condition from Lemma `10.119.7`.
-/

-- Proof sketch: if `L / K` is not finite, choose a finite transcendence basis and replace `R` by
-- the localization of the polynomial extension obtained by adjoining those generators, reducing to
-- the finite extension case. Then use Lemma `10.119.1` to replace `R` by a one-dimensional
-- dominating overring, take the integral closure in `L`, apply Krull-Akizuki to get Noetherianity,
-- choose a prime over the maximal ideal by lying over, and finally apply Lemma `10.119.7` to the
-- resulting localization.
/-- Helper for Lemma 10.119.13: a discrete valuation overring of `R` with fraction field `L`
packages canonically as a discrete valuation subring of `L` dominating the image of `R`. -/
lemma range_dominates_range_of_isLocalHom
    {A : Type*} [CommRing A] [IsLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Algebra A L] [IsScalarTower R A L] :
    LocalSubring.range (algebraMap R L) ≤ LocalSubring.range (algebraMap A L) := by
  let h :
      (LocalSubring.range (algebraMap R L)).toSubring ≤
        (LocalSubring.range (algebraMap A L)).toSubring := by
    intro z hz
    rcases hz with ⟨r, rfl⟩
    refine ⟨algebraMap R A r, ?_⟩
    change algebraMap A L (algebraMap R A r) = algebraMap R L r
    simpa using (IsScalarTower.algebraMap_apply R A L r).symm
  refine ⟨h, ?_⟩
  let i :
      (LocalSubring.range (algebraMap R L)).toSubring →+*
        (LocalSubring.range (algebraMap A L)).toSubring :=
    Subring.inclusion h
  letI : IsLocalHom ((algebraMap A L).rangeRestrict) :=
    IsLocalHom.of_surjective (algebraMap A L).rangeRestrict
      (algebraMap A L).rangeRestrict_surjective
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨r, rfl⟩ := (algebraMap R L).rangeRestrict_surjective x
  have hix :
      i ((algebraMap R L).rangeRestrict r) =
        (algebraMap A L).rangeRestrict (algebraMap R A r) := by
    ext
    simpa [i] using IsScalarTower.algebraMap_apply R A L r
  have hunitA : IsUnit (algebraMap R A r) :=
    isUnit_of_map_unit (algebraMap A L).rangeRestrict (algebraMap R A r) (hix ▸ hx)
  have hunitR : IsUnit r := isUnit_of_map_unit (algebraMap R A) r hunitA
  exact hunitR.map (algebraMap R L).rangeRestrict

/-- Helper for Lemma 10.119.13: a discrete valuation overring of `R` with fraction field `L`
packages canonically as a discrete valuation subring of `L` dominating the image of `R`. -/
lemma valuationSubring_of_dvr_dominating
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsDiscreteValuationRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Algebra A L] [IsScalarTower R A L] [IsFractionRing A L] :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  let V : ValuationSubring L :=
    ((IsDiscreteValuationRing.maximalIdeal A).valuation L).valuationSubring
  have hAV :
      LocalSubring.range (algebraMap A L) = V.toLocalSubring := by
    -- The canonical adic valuation identifies the image of `A` in `L` with the valuation subring.
    apply LocalSubring.toSubring_injective
    calc
      (LocalSubring.range (algebraMap A L)).toSubring = Subring.map (algebraMap A L) ⊤ := by
        ext z
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨a, by simp, rfl⟩
        · rintro ⟨a, ha, rfl⟩
          exact ⟨a, rfl⟩
      _ = V.toSubring := by
        simpa [V] using
          (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := A) (K := L))
  have hRA :
      LocalSubring.range (algebraMap R L) ≤ LocalSubring.range (algebraMap A L) :=
    range_dominates_range_of_isLocalHom (R := R) (A := A) (L := L)
  letI : IsDiscreteValuationRing V := by
    dsimp [V]
    infer_instance
  refine ⟨V, inferInstance, ?_⟩
  simpa [hAV] using hRA

/-- Helper for Lemma 10.119.13: a one-dimensional domain has no nonzero nonmaximal prime
ideals. -/
lemma ringDimensionLEOne_of_ringKrullDim_eq_one
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) :
    Ring.DimensionLEOne A := by
  classical
  refine ⟨fun {p} hp0 hpPrime ↦ ?_⟩
  -- The ambient dimension-one hypothesis bounds every prime height by `1`.
  have hupper' : ((p.primeHeight : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
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

/-- Helper for Lemma 10.119.13: a local domain of Krull dimension at most one which is not a
field has Krull dimension exactly `1`. -/
lemma ringKrullDim_eq_one_of_not_isField_of_dimensionLEOne
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [Ring.DimensionLEOne A]
    (hA : ¬ IsField A) :
    ringKrullDim A = 1 := by
  refine (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := A)).2 ⟨hA, ?_⟩
  intro x hx
  -- In a dimension-`≤ 1` local domain, every nonzero prime containing `x` is maximal.
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J ⟨hJ_span, hJ_prime⟩ ↦ ?_
  have hJ_ne_bot : J ≠ ⊥ := by
    intro hbot
    have hxJ : x ∈ J := hJ_span (Ideal.subset_span (by simp))
    exact hx (by simpa [hbot] using hxJ)
  have hJ_max : J.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hJ_ne_bot hJ_prime
  exact le_of_eq (IsLocalRing.eq_maximalIdeal hJ_max).symm

/-- Helper for Lemma 10.119.13: Krull-Akizuki applied to the normalization of a one-dimensional
domain gives Noetherianity of that normalization. -/
lemma normalization_isNoetherian_of_ringKrullDim_eq_one
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {L : Type*} [Field L] [Algebra A L] [FaithfulSMul A L]
    [FiniteDimensional (FractionRing A) L]
    (hdim : ringKrullDim A = 1) :
    IsNoetherianRing (integralClosure A L) := by
  letI : Algebra A (FractionRing A) := by
    infer_instance
  letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  letI : IsScalarTower A (FractionRing A) L := FractionRing.isScalarTower_liftAlgebra A L
  -- Apply the source-facing Krull-Akizuki theorem directly to the canonical normalization owner.
  exact
    Subalgebra.isNoetherianRing_of_ringKrullDim_eq_one
      (R := A) (L := L) (integralClosure A L) hdim

/-- Helper for Lemma 10.119.13: the normalization in a finite extension of the fraction field is
integrally closed. -/
lemma normalization_isIntegrallyClosed_of_finite_extension
    {A : Type*} [CommRing A] [IsDomain A]
    {L : Type*} [Field L] [Algebra A L] [FaithfulSMul A L]
    [FiniteDimensional (FractionRing A) L] :
    IsIntegrallyClosed (integralClosure A L) := by
  letI : Algebra A (FractionRing A) := by
    infer_instance
  letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  letI : IsScalarTower A (FractionRing A) L := FractionRing.isScalarTower_liftAlgebra A L
  exact
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := A) (K := FractionRing A) (L := L)

/-- Helper for Lemma 10.119.13: in a finite extension of the fraction field, the normalization has
the same ambient fraction field. -/
lemma normalization_isFractionRing_of_finite_extension
    {A : Type*} [CommRing A] [IsDomain A]
    {L : Type*} [Field L] [Algebra A L] [FaithfulSMul A L]
    [FiniteDimensional (FractionRing A) L] :
    IsFractionRing (integralClosure A L) L := by
  letI : Algebra A (FractionRing A) := by
    infer_instance
  letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  letI : IsScalarTower A (FractionRing A) L := FractionRing.isScalarTower_liftAlgebra A L
  exact
    integralClosure.isFractionRing_of_finite_extension
      (A := A) (K := FractionRing A) (L := L)

/-- Helper for Lemma 10.119.13: the inverse fraction-field equivalence sends a base-ring element
to its canonical image in `FractionRing A`. -/
lemma fractionRing_algEquiv_symm_algebraMap_apply
    (A : Subalgebra R K) (a : A) :
    (FractionRing.algEquiv A K).symm (algebraMap A K a) = algebraMap A (FractionRing A) a := by
  -- This is the base-ring computation needed for the later `ringHom_ext` transport argument.
  simpa using (FractionRing.algEquiv A K).symm.commutes a

/-- Helper for Lemma 10.119.13: the map `A → L` obtained from the tower `A → K → L` is injective. -/
lemma subalgebra_algebraMap_injective_to_extension
    (A : Subalgebra R K) :
    Function.Injective (algebraMap A L) := by
  -- Injectivity follows because `A → K` is the subtype map and `K → L` is injective for fields.
  intro x y hxy
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  simpa [IsScalarTower.algebraMap_apply A K L] using hxy

/-- Helper for Lemma 10.119.13: the pure ring-hom transport along
`K ≃+* FractionRing A` matches the original `K → L` action. -/
lemma fractionRing_transport_comp_eq_baseAction
    (A : Subalgebra R K) :
    let e : K ≃+* FractionRing A := (FractionRing.algEquiv A K).symm.toRingEquiv
    let f : FractionRing A →+* L := RingHom.comp (algebraMap K L) ↑e.symm
    RingHom.comp f ↑e = RingHom.comp (RingEquiv.refl L) (algebraMap K L) := by
  -- The transported action agrees with the original one because `e.symm` is the inverse of `e`.
  intro e f
  ext x
  change algebraMap K L (e.symm (e x)) = algebraMap K L x
  simp

/-- Helper for Lemma 10.119.13: the canonical `FractionRing.liftAlgebra` owner map from
`FractionRing A` to `L` agrees with the source proof's transport through `K`. -/
lemma fractionRing_liftAlgebra_algebraMap_eq_transport_comp
    (A : Subalgebra R K) :
    letI : FaithfulSMul A L :=
      (faithfulSMul_iff_algebraMap_injective A L).2
        (subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A)
    algebraMap (FractionRing A) L =
      RingHom.comp (algebraMap K L) ↑(FractionRing.algEquiv A K) := by
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2
      (subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A)
  -- The canonical lift is characterized by its values on the base ring `A`.
  rw [FractionRing.algebraMap_liftAlgebra]
  refine IsFractionRing.lift_unique
    (hg := subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A) ?_
  intro a
  -- On generators from `A`, the transported map is the original tower map `A → K → L`.
  change algebraMap K L ((FractionRing.algEquiv A K) (algebraMap A (FractionRing A) a)) =
    algebraMap A L a
  rw [AlgEquiv.commutes]
  simpa using (IsScalarTower.algebraMap_apply A K L a)

/-- Helper for Lemma 10.119.13: finite-dimensionality over `K` transports across the canonical
fraction-field identification `FractionRing A ≃ₐ[A] K` for a subalgebra `A ⊆ K`. -/
lemma fractionRing_finiteDimensional_of_subalgebra_fraction_field
    (A : Subalgebra R K) [FiniteDimensional K L] :
    FiniteDimensional (FractionRing A) L := by
  -- Route correction: the source-faithful transport is reduced to the owner-instance mismatch
  -- between the pure ring-hom model in `fractionRing_transport_comp_eq_baseAction` and the
  -- canonical `FractionRing.liftAlgebra A L` expected by `Module.Finite.of_equiv_equiv`.
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2
      (subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A)
  let e : K ≃+* FractionRing A := (FractionRing.algEquiv A K).symm.toRingEquiv
  have hcompat :
      RingHom.comp (algebraMap (FractionRing A) L) ↑e =
        RingHom.comp ↑(RingEquiv.refl L) (algebraMap K L) := by
    -- Rewrite the canonical owner map to the transport through `K`, then cancel `e.symm ≫ e`.
    calc
      RingHom.comp (algebraMap (FractionRing A) L) ↑e =
          RingHom.comp (RingHom.comp (algebraMap K L) ↑e.symm) ↑e := by
            rw [fractionRing_liftAlgebra_algebraMap_eq_transport_comp
              (R := R) (K := K) (L := L) A]
      _ = RingHom.comp ↑(RingEquiv.refl L) (algebraMap K L) := by
        simpa [e] using
          (fractionRing_transport_comp_eq_baseAction (R := R) (K := K) (L := L) A)
  -- `Module.Finite.of_equiv_equiv` transfers the finite-dimensional `K`-vector-space structure.
  exact Module.Finite.of_equiv_equiv e (RingEquiv.refl L) hcompat

/-- Helper for Lemma 10.119.13: a nonzero ideal of the normalization contracts to a nonzero ideal
of the base ring. -/
lemma integralClosure_comap_ne_bot_of_ne_bot_ideal
    (A : Subalgebra R K) [FiniteDimensional K L]
    (I : Ideal (integralClosure A L)) (hI : I ≠ ⊥) :
    Ideal.comap (algebraMap A (integralClosure A L)) I ≠ ⊥ := by
  -- Choose a nonzero element of `I` and use its algebraicity over the base ring `A`.
  obtain ⟨y, hyI, hy0⟩ := (Submodule.ne_bot_iff _).mp hI
  exact Ideal.comap_ne_bot_of_integral_mem hy0 hyI
    (Algebra.IsIntegral.isIntegral y)

/-- Helper for Lemma 10.119.13: the integral closure sits inside the ambient field extension, so
the base map into the normalization is injective. -/
lemma integralClosure_algebraMap_injective
    (A : Subalgebra R K) [FiniteDimensional K L] :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  -- Compare the map into the integral closure with the ambient inclusion into `L`.
  intro x y hxy
  apply Subtype.ext
  exact congrArg Subtype.val <|
    subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A <|
      by simpa using congrArg Subtype.val hxy

/-- Helper for Lemma 10.119.13: in a one-dimensional domain, every nonzero prime has height
exactly `1`. -/
lemma primeHeight_eq_one_of_dimensionLEOne_of_ne_bot
    {A : Type*} [CommRing A] [IsDomain A] [Ring.DimensionLEOne A]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    p.primeHeight = 1 := by
  -- The dimension-`≤ 1` condition bounds the height from above by `1`.
  have hdim : Ring.KrullDimLE 1 A := by
    refine Ring.KrullDimLE.mk₁' fun I hI hI_prime ↦ ?_
    exact Ring.DimensionLEOne.maximalOfPrime hI hI_prime
  have hupper' : ((p.primeHeight : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    exact (Ideal.primeHeight_le_ringKrullDim (I := p)).trans (Ring.krullDimLE_iff.mp hdim)
  have hupper : p.primeHeight ≤ 1 := by
    exact_mod_cast hupper'
  -- The chain `(0) < p` forces the height to be positive.
  have hbot_height : (⊥ : Ideal A).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hlower : (1 : ℕ∞) ≤ p.primeHeight := by
    simpa [hbot_height] using
      (Ideal.primeHeight_add_one_le_of_lt
        (I := (⊥ : Ideal A)) (J := p) (bot_lt_iff_ne_bot.mpr hp))
  exact le_antisymm hupper hlower

/-- Helper for Lemma 10.119.13: localizing a one-dimensional domain at a nonzero prime gives a
one-dimensional local domain. -/
lemma localizationAtPrime_ringKrullDim_eq_one_of_dimensionLEOne_of_ne_bot
    {A : Type*} [CommRing A] [IsDomain A] [Ring.DimensionLEOne A]
    (p : PrimeSpectrum A) (hp : p.asIdeal ≠ ⊥) :
    ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
  -- Compute the localized dimension as the height of the prime and use the height-one lemma.
  have hp_height : p.asIdeal.primeHeight = 1 :=
    primeHeight_eq_one_of_dimensionLEOne_of_ne_bot (p := p.asIdeal) hp
  calc
    ringKrullDim (Localization.AtPrime p.asIdeal) = p.asIdeal.height := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
        (Localization.AtPrime p.asIdeal)]
    _ = ((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) := by
      rw [Ideal.height_eq_primeHeight]
    _ = 1 := by
      exact_mod_cast hp_height

/-- Helper for Lemma 10.119.13: if a prime of an algebra contracts to the maximal ideal of a
local base ring, then the induced map to the prime localization is local. -/
lemma localizationAtPrime_isLocalHom_of_comap_maximalIdeal
    {A : Type*} {S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
    (q : PrimeSpectrum S)
    (hcomap : Ideal.comap (algebraMap A S) q.asIdeal = IsLocalRing.maximalIdeal A) :
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := by
  -- The local-hom criterion is exactly the pullback identity for the maximal ideal.
  have hmax :
      Ideal.comap (algebraMap A (Localization.AtPrime q.asIdeal))
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) =
      IsLocalRing.maximalIdeal A := by
    change
      Ideal.comap
          ((algebraMap S (Localization.AtPrime q.asIdeal)).comp (algebraMap A S))
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) =
        IsLocalRing.maximalIdeal A
    rw [← Ideal.comap_comap (algebraMap A S) (algebraMap S (Localization.AtPrime q.asIdeal))]
    simpa [Localization.AtPrime.comap_maximalIdeal] using hcomap
  exact ((IsLocalRing.local_hom_TFAE
    (algebraMap A (Localization.AtPrime q.asIdeal))).out 4 0).mp hmax

/-- Helper for Lemma 10.119.13: the normalization of a one-dimensional local domain inside a
finite extension still has Krull dimension at most one. -/
lemma normalization_dimensionLEOne_of_local_dim_one
    (A : Subalgebra R K) [FiniteDimensional K L] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) :
    Ring.DimensionLEOne (integralClosure A L) := by
  let B := integralClosure A L
  have hA_dim_le_one : Ring.DimensionLEOne A :=
    ringDimensionLEOne_of_ringKrullDim_eq_one (A := A) hdim
  refine ⟨fun {p} hp0 hpPrime ↦ ?_⟩
  -- Contract a nonzero prime of the normalization to a nonzero prime of the base ring.
  let pA : Ideal A := Ideal.comap (algebraMap A B) p
  have hpA_ne_bot : pA ≠ ⊥ :=
    integralClosure_comap_ne_bot_of_ne_bot_ideal (R := R) (K := K) (L := L) A p hp0
  have hpA_max : pA.IsMaximal := by
    exact hA_dim_le_one.maximalOfPrime hpA_ne_bot inferInstance
  -- Integrality of the normalization upgrades maximality from the contraction to the original
  -- prime.
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p hpA_max

/-- Helper for Lemma 10.119.13: the normalization of a one-dimensional local domain inside a
finite extension of its fraction field is Dedekind. -/
lemma normalization_isDedekindDomain_of_local_dim_one
    (A : Subalgebra R K) [FiniteDimensional K L] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) :
    IsDedekindDomain (integralClosure A L) := by
  let B := integralClosure A L
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2
      (subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A)
  letI : FiniteDimensional (FractionRing A) L :=
    fractionRing_finiteDimensional_of_subalgebra_fraction_field (R := R) (K := K) (L := L) A
  letI : IsIntegrallyClosed B :=
    normalization_isIntegrallyClosed_of_finite_extension (A := A) (L := L)
  letI : IsFractionRing B L :=
    normalization_isFractionRing_of_finite_extension (A := A) (L := L)
  -- Package the source normalization paragraph as the canonical Dedekind-domain owner.
  refine (isDedekindDomain_iff (A := B) L).2 ?_
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · -- Krull-Akizuki gives Noetherianity of the normalization in the finite extension.
    exact normalization_isNoetherian_of_ringKrullDim_eq_one (A := A) (L := L) hdim
  · -- One-dimensionality persists under normalization in a finite extension.
    exact normalization_dimensionLEOne_of_local_dim_one (R := R) (K := K) (L := L) A hdim
  · -- Integrally closedness is already available for the normalization owner.
    intro x hx
    exact (isIntegrallyClosed_iff L).mp inferInstance hx

/-- Helper for Lemma 10.119.13: the prime localization of the normalization maps canonically to
the ambient field extension. -/
noncomputable def normalization_prime_localization_to_field
    (A : Subalgebra R K) [FaithfulSMul A L] [FiniteDimensional (FractionRing A) L]
    [IsFractionRing (integralClosure A L) L]
    (q : PrimeSpectrum (integralClosure A L)) :
    Localization.AtPrime q.asIdeal →+* L :=
  IsLocalization.map (M := q.asIdeal.primeCompl)
    (S := Localization.AtPrime q.asIdeal)
    (T := nonZeroDivisors (integralClosure A L))
    L (RingHom.id _) q.asIdeal.primeCompl_le_nonZeroDivisors

/-- Helper for Lemma 10.119.13: if a prime of the normalization contracts to the closed point of
the one-dimensional local base, then the corresponding prime localization of the normalization is a
discrete valuation ring. -/
lemma normalization_prime_localization_isDiscreteValuationRing
    (A : Subalgebra R K) [FiniteDimensional K L] [IsLocalRing A] [IsNoetherianRing A]
    [IsFractionRing (integralClosure A L) L]
    (hdim : ringKrullDim A = 1)
    (q : PrimeSpectrum (integralClosure A L))
    (hcomap : Ideal.comap (algebraMap A (integralClosure A L)) q.asIdeal =
      IsLocalRing.maximalIdeal A) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2
      (subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A)
  letI : FiniteDimensional (FractionRing A) L :=
    fractionRing_finiteDimensional_of_subalgebra_fraction_field (R := R) (K := K) (L := L) A
  letI : IsDedekindDomain (integralClosure A L) :=
    normalization_isDedekindDomain_of_local_dim_one (R := R) (K := K) (L := L) A hdim
  have hA_not_field : ¬ IsField A :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := A)).mp hdim |>.1
  have hmax_ne_bot : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hA_not_field
  have hq_ne_bot : q.asIdeal ≠ ⊥ := by
    -- A prime above the closed point cannot be zero because its contraction is the nonzero maximal
    -- ideal of the one-dimensional local base.
    intro hq_bot
    have hcomap_bot :
        Ideal.comap (algebraMap A (integralClosure A L)) q.asIdeal = ⊥ := by
      rw [hq_bot]
      exact
        Ideal.comap_bot_of_injective (algebraMap A (integralClosure A L))
          (integralClosure_algebraMap_injective (R := R) (K := K) (L := L) A)
    exact hmax_ne_bot (hcomap.symm.trans hcomap_bot)
  -- The normalization is Dedekind, so every nonzero prime localization is a DVR.
  exact
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (integralClosure A L) hq_ne_bot (Localization.AtPrime q.asIdeal)

/-- Helper for Lemma 10.119.13: the canonical map from the raw prime localization of the
normalization to the ambient field extends the original map from the base subalgebra. -/
lemma normalization_prime_localization_to_field_comp_algebraMap
    (A : Subalgebra R K) [FaithfulSMul A L] [FiniteDimensional (FractionRing A) L]
    [IsFractionRing (integralClosure A L) L]
    (q : PrimeSpectrum (integralClosure A L)) :
    RingHom.comp
        (normalization_prime_localization_to_field (R := R) (K := K) (L := L) A q)
        (algebraMap A (Localization.AtPrime q.asIdeal)) =
      algebraMap A L := by
  -- The raw localization map is the universal localization map of the normalization into `L`.
  ext a
  change
    (normalization_prime_localization_to_field (R := R) (K := K) (L := L) A q)
        (algebraMap (integralClosure A L) (Localization.AtPrime q.asIdeal)
          (algebraMap A (integralClosure A L) a)) =
      algebraMap (integralClosure A L) L (algebraMap A (integralClosure A L) a)
  simp [normalization_prime_localization_to_field]

/-- Helper for Lemma 10.119.13: if a prime of the normalization contracts to the closed point of
the local overring `A`, then the canonical subalgebra-of-`L` model of the corresponding prime
localization receives a local map directly from the original base ring `R`. -/
lemma normalization_prime_localization_comap_closed_point_base
    (A : Subalgebra R K) [IsLocalRing A]
    (q : PrimeSpectrum (integralClosure A L))
    [IsLocalHom (algebraMap R A)]
    (hcomap : Ideal.comap (algebraMap A (integralClosure A L)) q.asIdeal =
      IsLocalRing.maximalIdeal A) :
    Ideal.comap (algebraMap R (integralClosure A L)) q.asIdeal =
      IsLocalRing.maximalIdeal R := by
  -- Compute the contraction to `R` through the intermediate local overring `A`.
  rw [show algebraMap R (integralClosure A L) =
      (algebraMap A (integralClosure A L)).comp (algebraMap R A) by
        ext x
        change algebraMap R L x = algebraMap A L ((algebraMap R A) x)
        simpa using (IsScalarTower.algebraMap_apply R A L x)]
  rw [← Ideal.comap_comap (algebraMap R A) (algebraMap A (integralClosure A L))]
  rw [hcomap]
  exact IsLocalRing.maximalIdeal_comap (algebraMap R A)

/-- Helper for Lemma 10.119.13: if a prime of the normalization contracts to the closed point of
the local overring `A`, then the raw prime localization already receives a local map from `R`. -/
lemma normalization_prime_localization_algebraMap_isLocalHom_base
    (A : Subalgebra R K) [IsLocalRing A]
    (q : PrimeSpectrum (integralClosure A L))
    [IsLocalHom (algebraMap R A)]
    (hcomap : Ideal.comap (algebraMap A (integralClosure A L)) q.asIdeal =
      IsLocalRing.maximalIdeal A) :
    IsLocalHom (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  have hRcomap :
      Ideal.comap (algebraMap R (integralClosure A L)) q.asIdeal =
        IsLocalRing.maximalIdeal R :=
    normalization_prime_localization_comap_closed_point_base
      (R := R) (K := K) (L := L) A q hcomap
  -- Route correction: the source proof only needs the raw localization `A_q`, so apply the
  -- local-hom criterion directly there after computing the contraction to `R`.
  exact
    localizationAtPrime_isLocalHom_of_comap_maximalIdeal
      (A := R) (S := integralClosure A L) q hRcomap

/-- Helper for Lemma 10.119.13: the map from the raw prime localization to `L` still extends the
original base action of `R`. -/
lemma normalization_prime_localization_to_field_comp_algebraMap_base
    (A : Subalgebra R K) [FaithfulSMul A L] [FiniteDimensional (FractionRing A) L]
    [IsFractionRing (integralClosure A L) L]
    (q : PrimeSpectrum (integralClosure A L)) :
    RingHom.comp
        (normalization_prime_localization_to_field (R := R) (K := K) (L := L) A q)
        (algebraMap R (Localization.AtPrime q.asIdeal)) =
      algebraMap R L := by
  ext r
  -- Evaluate both composites through the intermediate overring `A`.
  simpa [RingHom.comp_apply, IsScalarTower.algebraMap_apply R A (Localization.AtPrime q.asIdeal),
    IsScalarTower.algebraMap_apply R A L] using
    congrArg
      (fun f : A →+* L => f (algebraMap R A r))
      (normalization_prime_localization_to_field_comp_algebraMap
        (R := R) (K := K) (L := L) A q)

/-- Helper for Lemma 10.119.13: after normalizing a one-dimensional dominating overring in the
finite-extension case, one can choose a prime over the closed point whose localization is already
a discrete valuation ring dominating `R`. -/
lemma normalization_prime_localization_dominating_package
    (A : Subalgebra R K) [FiniteDimensional K L] [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalHom (algebraMap R A)] [IsFractionRing (integralClosure A L) L]
    (hdim : ringKrullDim A = 1) :
    ∃ q : PrimeSpectrum (integralClosure A L),
      Ideal.comap (algebraMap A (integralClosure A L)) q.asIdeal =
        IsLocalRing.maximalIdeal A ∧
        IsLocalHom (algebraMap R (Localization.AtPrime q.asIdeal)) ∧
        IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let pA : PrimeSpectrum A := ⟨IsLocalRing.maximalIdeal A, inferInstance⟩
  have hInt : (algebraMap A (integralClosure A L)).IsIntegral := by
    exact algebraMap_isIntegral_iff.mpr inferInstance
  -- Choose a prime of the normalization lying over the closed point of the local base `A`.
  obtain ⟨q, hq⟩ := RingHom.IsIntegral.comap_surjective hInt
    (integralClosure_algebraMap_injective (R := R) (K := K) (L := L) A) pA
  have hcomap :
      Ideal.comap (algebraMap A (integralClosure A L)) q.asIdeal =
        IsLocalRing.maximalIdeal A := by
    simpa [pA, PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
  refine ⟨q, hcomap, ?_, ?_⟩
  · -- The contraction computation gives the needed local map from `R` to the raw localization.
    exact
      normalization_prime_localization_algebraMap_isLocalHom_base
        (R := R) (K := K) (L := L) A q hcomap
  · -- The same closed-point prime localization is a DVR by the normalized one-dimensional case.
    exact
      normalization_prime_localization_isDiscreteValuationRing
        (R := R) (K := K) (L := L) A hdim q hcomap

/-- Helper for Lemma 10.119.13: once the raw normalization prime localization is mapped to `L`,
its localization structure identifies `L` as the fraction field. -/
lemma normalization_prime_localization_isFractionRing_to_field
    (A : Subalgebra R K) [FaithfulSMul A L] [FiniteDimensional (FractionRing A) L]
    [IsFractionRing (integralClosure A L) L]
    (q : PrimeSpectrum (integralClosure A L))
    [Algebra (Localization.AtPrime q.asIdeal) L]
    (hmap :
      algebraMap (Localization.AtPrime q.asIdeal) L =
        normalization_prime_localization_to_field (R := R) (K := K) (L := L) A q) :
    IsFractionRing (Localization.AtPrime q.asIdeal) L := by
  have hcomp :
      RingHom.comp
          (algebraMap (Localization.AtPrime q.asIdeal) L)
          (algebraMap (integralClosure A L) (Localization.AtPrime q.asIdeal)) =
        algebraMap (integralClosure A L) L := by
    -- The chosen `Bq → L` map is exactly the universal localization map of the normalization.
    ext b
    change
      algebraMap (Localization.AtPrime q.asIdeal) L
          (algebraMap (integralClosure A L) (Localization.AtPrime q.asIdeal) b) =
        algebraMap (integralClosure A L) L b
    rw [hmap]
    simp [normalization_prime_localization_to_field]
  letI : Algebra (integralClosure A L) (Localization.AtPrime q.asIdeal) := by
    infer_instance
  letI : SMul (integralClosure A L) (Localization.AtPrime q.asIdeal) :=
    (show Algebra (integralClosure A L) (Localization.AtPrime q.asIdeal) from inferInstance).toSMul
  letI : SMul (Localization.AtPrime q.asIdeal) L :=
    (show Algebra (Localization.AtPrime q.asIdeal) L from inferInstance).toSMul
  letI : SMul (integralClosure A L) L :=
    (show Algebra (integralClosure A L) L from inferInstance).toSMul
  letI :
      IsScalarTower (integralClosure A L) (Localization.AtPrime q.asIdeal) L :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  -- Once the normalization-localization tower is installed, `L` is the common fraction field.
  exact
    (show IsFractionRing (Localization.AtPrime q.asIdeal) L from
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        (R := integralClosure A L)
        (M := q.asIdeal.primeCompl)
        (S := Localization.AtPrime q.asIdeal)
        (T := L))

/-- Helper for Lemma 10.119.13: the closed-point kernel in the polynomial stage is prime because
its target is a field. -/
lemma closed_point_polynomial_ker_isPrime (r : ℕ) :
    (RingHom.ker (MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0))
      : Ideal (MvPolynomial (Fin r) R)).IsPrime := by
  -- The evaluation map lands in the residue field, so its kernel is prime.
  exact RingHom.ker_isPrime _

/-- Helper for Lemma 10.119.13: in the finite-extension case, the source proof produces a
height-one localization of the normalization of a one-dimensional dominating overring, and that
localization is a discrete valuation ring dominating `R`. -/
theorem exists_discreteValuationSubring_dominating_of_not_isField_of_finiteDimensional
    [FiniteDimensional K L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  obtain ⟨A, hdim, hA_local, hRA_local, hA_ess⟩ :=
    exists_one_dimensional_dominating_essFiniteType_overring_of_not_isField
      (R := R) (K := K) hR
  letI : IsLocalRing A := hA_local
  letI : IsLocalHom (algebraMap R A) := hRA_local
  letI : Algebra.EssFiniteType R A := hA_ess
  letI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing R A
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2
      (subalgebra_algebraMap_injective_to_extension (R := R) (K := K) (L := L) A)
  letI : FiniteDimensional (FractionRing A) L :=
    fractionRing_finiteDimensional_of_subalgebra_fraction_field
      (R := R) (K := K) (L := L) A
  letI : IsFractionRing (integralClosure A L) L :=
    normalization_isFractionRing_of_finite_extension (A := A) (L := L)
  obtain ⟨q, _, hRBq_local, hBq_dvr⟩ :=
    normalization_prime_localization_dominating_package
      (R := R) (K := K) (L := L) A hdim
  let Bq := Localization.AtPrime q.asIdeal
  letI : Algebra Bq L :=
    (normalization_prime_localization_to_field (R := R) (K := K) (L := L) A q).toAlgebra
  have hBq_map :
      algebraMap Bq L =
        normalization_prime_localization_to_field (R := R) (K := K) (L := L) A q := by
    rw [RingHom.algebraMap_toAlgebra]
  have hRBq_comp :
      RingHom.comp (algebraMap Bq L) (algebraMap R Bq) = algebraMap R L := by
    -- The chosen localization map to `L` is exactly the normalized prime-localization map.
    calc
      RingHom.comp (algebraMap Bq L) (algebraMap R Bq) =
          RingHom.comp
            (normalization_prime_localization_to_field (R := R) (K := K) (L := L) A q)
            (algebraMap R Bq) := by
              rw [hBq_map]
      _ = algebraMap R L := by
        simpa [Bq] using
          normalization_prime_localization_to_field_comp_algebraMap_base
            (R := R) (K := K) (L := L) A q
  letI : IsScalarTower R Bq L := IsScalarTower.of_algebraMap_eq' hRBq_comp.symm
  letI : IsFractionRing Bq L :=
    normalization_prime_localization_isFractionRing_to_field
      (R := R) (K := K) (L := L) A q hBq_map
  letI : IsLocalHom (algebraMap R Bq) := hRBq_local
  letI : IsDiscreteValuationRing Bq := hBq_dvr
  -- The finite-dimensional branch now matches the DVR-to-valuation-subring packaging lemma.
  exact valuationSubring_of_dvr_dominating (R := R) (A := Bq) (L := L)

/-- Helper for Lemma 10.119.13: adjoining the closed point of `R` and all variables in the
polynomial ring still gives a proper ideal. -/
lemma closed_point_variables_ideal_ne_top (r : ℕ) :
    let Iclosed : Ideal (MvPolynomial (Fin r) R) :=
      Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal R) ⊔
        Ideal.span (Set.range fun i : Fin r ↦ MvPolynomial.X i)
    Iclosed ≠ ⊤ := by
  intro Iclosed
  let φ : MvPolynomial (Fin r) R →+* IsLocalRing.ResidueField R :=
    MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0)
  have hClosedPoint :
      Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal R) ≤ Ideal.comap φ ⊥ := by
    -- Constants from the maximal ideal vanish in the residue field.
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change φ (MvPolynomial.C x) = 0
    simpa [φ] using (IsLocalRing.residue_eq_zero_iff x).2 hx
  have hVariables :
      Ideal.span (Set.range fun i : Fin r ↦ MvPolynomial.X i) ≤ Ideal.comap φ ⊥ := by
    -- Every variable is sent to `0` by the specialization map.
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change φ (MvPolynomial.X i) = 0
    simp [φ]
  have hIclosed : Iclosed ≤ Ideal.comap φ ⊥ := sup_le hClosedPoint hVariables
  intro htop
  have hOneTop : (1 : MvPolynomial (Fin r) R) ∈ Iclosed := by simpa [htop]
  have hOneZero : φ 1 = 0 := hIclosed hOneTop
  simpa [φ] using hOneZero

/-- Helper for Lemma 10.119.13: the kernel of evaluation at the closed point of the polynomial
stage contracts to the maximal ideal of the base local ring. -/
lemma closed_point_polynomial_ker_comap_maximalIdeal (r : ℕ) :
    let φ : MvPolynomial (Fin r) R →+* IsLocalRing.ResidueField R :=
      MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0)
    Ideal.comap (algebraMap R (MvPolynomial (Fin r) R)) (RingHom.ker φ) =
      IsLocalRing.maximalIdeal R := by
  intro φ
  ext x
  -- Evaluating a constant polynomial at the closed point is exactly the residue map on `R`.
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change φ (MvPolynomial.C x) = 0 ↔ x ∈ IsLocalRing.maximalIdeal R
  rw [show φ (MvPolynomial.C x) = IsLocalRing.residue R x by simp [φ]]
  exact IsLocalRing.residue_eq_zero_iff x

/-- Helper for Lemma 10.119.13: localizing the polynomial stage at the closed-point kernel prime
produces a local overring of `R`. -/
lemma closed_point_polynomial_localization_isLocalHom (r : ℕ)
    (q : PrimeSpectrum (MvPolynomial (Fin r) R))
    (hq : q.asIdeal =
      RingHom.ker (MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0))) :
    IsLocalHom (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  -- The source proof localizes at the closed point, so the earlier local-hom criterion applies
  -- once the contraction of the kernel prime is identified.
  refine localizationAtPrime_isLocalHom_of_comap_maximalIdeal (A := R) (S := MvPolynomial (Fin r) R) q ?_
  simpa [hq] using closed_point_polynomial_ker_comap_maximalIdeal (R := R) r

/-- Helper for Lemma 10.119.13: the closed-point localization of the polynomial stage is still
not a field, because its maximal ideal contracts to the nonzero closed-point prime. -/
lemma closed_point_polynomial_localization_not_isField (r : ℕ)
    (q : PrimeSpectrum (MvPolynomial (Fin r) R))
    (hq : q.asIdeal =
      RingHom.ker (MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0)))
    (hR : ¬ IsField R) :
    ¬ IsField (Localization.AtPrime q.asIdeal) := by
  have hmaxR_ne_bot : IsLocalRing.maximalIdeal R ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hR
  have hpoly_injective : Function.Injective (algebraMap R (MvPolynomial (Fin r) R)) := by
    -- The polynomial-ring coefficient inclusion is the canonical injective closed-point map.
    simpa [MvPolynomial.algebraMap_eq] using (MvPolynomial.C_injective (σ := Fin r) (R := R))
  have hq_comap :
      Ideal.comap (algebraMap R (MvPolynomial (Fin r) R)) q.asIdeal =
        IsLocalRing.maximalIdeal R := by
    -- The chosen prime is exactly the kernel of evaluation at the closed point.
    simpa [hq] using closed_point_polynomial_ker_comap_maximalIdeal (R := R) r
  have hq_ne_bot : q.asIdeal ≠ ⊥ := by
    -- If the closed-point prime were zero, its contraction would force the maximal ideal of `R`
    -- to vanish, contradicting `R` not being a field.
    intro hq_bot
    have hcomap_bot :
        Ideal.comap (algebraMap R (MvPolynomial (Fin r) R)) q.asIdeal = ⊥ := by
      rw [hq_bot]
      exact Ideal.comap_bot_of_injective _ hpoly_injective
    exact hmaxR_ne_bot (hq_comap.symm.trans hcomap_bot)
  intro hfield
  have hmaxS_bot :
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  have hq_bot : q.asIdeal = ⊥ := by
    -- In a prime localization, the maximal ideal is the image of the localized prime.
    simpa [hmaxS_bot] using
      (Localization.AtPrime.comap_maximalIdeal
        (R := MvPolynomial (Fin r) R) (I := q.asIdeal)).symm
  exact hq_ne_bot hq_bot

/-- Helper for Lemma 10.119.13: the coefficient field `K = Frac(R)` maps into the fraction field
of the multivariable polynomial ring over `R` via constant polynomials. -/
noncomputable def fractionRing_to_mvPolynomial_fractionRing_coeffLift (r : ℕ) :
    K →+* FractionRing (MvPolynomial (Fin r) R) :=
  IsFractionRing.lift
    (K := K) (L := FractionRing (MvPolynomial (Fin r) R))
    (g := algebraMap R (FractionRing (MvPolynomial (Fin r) R)))
    (FaithfulSMul.algebraMap_injective R (FractionRing (MvPolynomial (Fin r) R)))

/-- Helper for Lemma 10.119.13: the coefficient lift sends a base element of `R` to the matching
constant polynomial inside `Frac(R[Fin r])`. -/
lemma fractionRing_to_mvPolynomial_fractionRing_coeffLift_base
    (r : ℕ) (a : R) :
    fractionRing_to_mvPolynomial_fractionRing_coeffLift (R := R) (K := K) r
        (algebraMap R K a) =
      algebraMap (MvPolynomial (Fin r) R) (FractionRing (MvPolynomial (Fin r) R))
        (MvPolynomial.C a) := by
  -- First evaluate the fraction-field lift on `R`, then rewrite the scalar action through `C`.
  have hcoeff :
      fractionRing_to_mvPolynomial_fractionRing_coeffLift (R := R) (K := K) r
          (algebraMap R K a) =
        algebraMap R (FractionRing (MvPolynomial (Fin r) R)) a := by
    simpa [fractionRing_to_mvPolynomial_fractionRing_coeffLift] using
      (IsFractionRing.lift_algebraMap
        (A := R) (K := K) (L := FractionRing (MvPolynomial (Fin r) R))
        (g := algebraMap R (FractionRing (MvPolynomial (Fin r) R)))
        (hg := FaithfulSMul.algebraMap_injective R
          (FractionRing (MvPolynomial (Fin r) R))) a)
  rw [hcoeff]
  simpa using
    congrArg
      (fun g : R →+* FractionRing (MvPolynomial (Fin r) R) => g a)
      (IsScalarTower.algebraMap_eq R (MvPolynomial (Fin r) R)
        (FractionRing (MvPolynomial (Fin r) R)))

/-- Helper for Lemma 10.119.13: evaluating `K[Fin r]` with coefficients lifted to
`Frac(R[Fin r])` and variables fixed gives the backward polynomial map in the source fraction-field
bridge. -/
noncomputable def mvPolynomial_fractionRing_baseChangeBackward (r : ℕ) :
    MvPolynomial (Fin r) K →+* FractionRing (MvPolynomial (Fin r) R) :=
  MvPolynomial.eval₂Hom
    (fractionRing_to_mvPolynomial_fractionRing_coeffLift (R := R) (K := K) r)
    (fun i ↦
      algebraMap (MvPolynomial (Fin r) R) (FractionRing (MvPolynomial (Fin r) R))
        (MvPolynomial.X i))

/-- Helper for Lemma 10.119.13: localizing the coefficient-extension map
`R[Fin r] → K[Fin r]` gives the forward map `Frac(R[Fin r]) → Frac(K[Fin r])`. -/
noncomputable def mvPolynomial_fractionRing_baseChangeForward (r : ℕ) :
    FractionRing (MvPolynomial (Fin r) R) →+* FractionRing (MvPolynomial (Fin r) K) :=
  IsFractionRing.map
    (K := FractionRing (MvPolynomial (Fin r) R))
    (L := FractionRing (MvPolynomial (Fin r) K))
    (j := MvPolynomial.map (algebraMap R K))
    (MvPolynomial.map_injective (σ := Fin r) (f := algebraMap R K)
      (IsFractionRing.injective R K))

/-- Helper for Lemma 10.119.13: on polynomial numerators, the forward fraction-field map is the
localized coefficient-extension map. -/
lemma mvPolynomial_fractionRing_baseChangeForward_algebraMap
    (r : ℕ) (p : MvPolynomial (Fin r) R) :
    mvPolynomial_fractionRing_baseChangeForward (R := R) (K := K) r
        (algebraMap (MvPolynomial (Fin r) R) (FractionRing (MvPolynomial (Fin r) R)) p) =
      algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
        (MvPolynomial.map (algebraMap R K) p) := by
  -- Unfold the localization map once so the target is exactly the canonical numerator transport.
  delta mvPolynomial_fractionRing_baseChangeForward IsFractionRing.map
  simp only [IsLocalization.map_eq]

/-- Helper for Lemma 10.119.13: after extending coefficients from `R` to `K` and then applying
the backward polynomial map, one recovers the original numerator in `Frac(R[Fin r])`. -/
lemma mvPolynomial_fractionRing_baseChange_backward_comp_map_eq_algebraMap
    (r : ℕ) :
    (mvPolynomial_fractionRing_baseChangeBackward (R := R) (K := K) r).comp
        (MvPolynomial.map (algebraMap R K)) =
      algebraMap (MvPolynomial (Fin r) R) (FractionRing (MvPolynomial (Fin r) R)) := by
  -- `MvPolynomial.ringHom_ext` reduces the comparison to base coefficients and variables.
  apply MvPolynomial.ringHom_ext
  · intro a
    -- On constants from `R`, the backward map is exactly the coefficient lift.
    simpa [RingHom.comp_apply, mvPolynomial_fractionRing_baseChangeBackward] using
      fractionRing_to_mvPolynomial_fractionRing_coeffLift_base (R := R) (K := K) r a
  · intro i
    simp [mvPolynomial_fractionRing_baseChangeBackward]

/-- Helper for Lemma 10.119.13: applying the forward fraction-field map after the backward
polynomial lift gives the standard inclusion `K[Fin r] → Frac(K[Fin r])`. -/
lemma mvPolynomial_fractionRing_baseChange_forward_comp_backward_eq_algebraMap
    (r : ℕ) :
    (mvPolynomial_fractionRing_baseChangeForward (R := R) (K := K) r).comp
        (mvPolynomial_fractionRing_baseChangeBackward (R := R) (K := K) r) =
      algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) := by
  have hcoeff :
      (mvPolynomial_fractionRing_baseChangeForward (R := R) (K := K) r).comp
          (fractionRing_to_mvPolynomial_fractionRing_coeffLift (R := R) (K := K) r) =
        algebraMap K (FractionRing (MvPolynomial (Fin r) K)) := by
    -- Compare the two maps out of `K = Frac(R)` only on `R`.
    apply IsFractionRing.ringHom_ext (A := R)
    intro a
    rw [RingHom.comp_apply]
    rw [fractionRing_to_mvPolynomial_fractionRing_coeffLift_base (R := R) (K := K) r a]
    rw [mvPolynomial_fractionRing_baseChangeForward_algebraMap (R := R) (K := K) r
      (MvPolynomial.C a)]
    calc
      algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
          (MvPolynomial.map (algebraMap R K) (MvPolynomial.C a)) =
        algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
          (MvPolynomial.C (algebraMap R K a)) := by
            simp
      _ = algebraMap K (FractionRing (MvPolynomial (Fin r) K)) (algebraMap R K a) := by
            symm
            simpa using
              congrArg
                (fun g : K →+* FractionRing (MvPolynomial (Fin r) K) =>
                  g (algebraMap R K a))
                (IsScalarTower.algebraMap_eq K (MvPolynomial (Fin r) K)
                  (FractionRing (MvPolynomial (Fin r) K)))
  -- Route correction: the source bridge is proved by checking the composite on constants and
  -- variables, not by coefficient-clearing inside the fraction field.
  apply MvPolynomial.ringHom_ext
  · intro a
    have hcoeff_apply :
        (mvPolynomial_fractionRing_baseChangeForward (R := R) (K := K) r).comp
            (fractionRing_to_mvPolynomial_fractionRing_coeffLift (R := R) (K := K) r) a =
          algebraMap K (FractionRing (MvPolynomial (Fin r) K)) a :=
      congrArg
        (fun f : K →+* FractionRing (MvPolynomial (Fin r) K) => f a) hcoeff
    have hconst :
        algebraMap K (FractionRing (MvPolynomial (Fin r) K)) a =
          algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
            (MvPolynomial.C a) := by
      simpa using
        congrArg
          (fun g : K →+* FractionRing (MvPolynomial (Fin r) K) => g a)
          (IsScalarTower.algebraMap_eq K (MvPolynomial (Fin r) K)
            (FractionRing (MvPolynomial (Fin r) K)))
    -- The constant polynomial `C a` is sent to the lifted coefficient `a`.
    simpa [RingHom.comp_apply, mvPolynomial_fractionRing_baseChangeBackward] using
      hcoeff_apply.trans hconst
  · intro i
    have hX :
        mvPolynomial_fractionRing_baseChangeForward (R := R) (K := K) r
            (algebraMap (MvPolynomial (Fin r) R) (FractionRing (MvPolynomial (Fin r) R))
              (MvPolynomial.X i)) =
          algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
            (MvPolynomial.X i) := by
      rw [mvPolynomial_fractionRing_baseChangeForward_algebraMap (R := R) (K := K) r
        (MvPolynomial.X i)]
      simp
    -- Both maps keep the polynomial variables unchanged.
    simpa [RingHom.comp_apply, mvPolynomial_fractionRing_baseChangeBackward] using hX

/-- Helper for Lemma 10.119.13: the fraction fields of `R[Fin r]` and `K[Fin r]` are canonically
identified by extending coefficients to `K = Frac(R)` and then inverting the explicit backward
polynomial lift. -/
noncomputable def mvPolynomial_fractionRing_baseChange_algEquiv
    (r : ℕ) :
    FractionRing (MvPolynomial (Fin r) R) ≃ₐ[R] FractionRing (MvPolynomial (Fin r) K) := by
  let fwd := mvPolynomial_fractionRing_baseChangeForward (R := R) (K := K) r
  let ψpoly := mvPolynomial_fractionRing_baseChangeBackward (R := R) (K := K) r
  have hψpoly_injective : Function.Injective ψpoly := by
    intro p q hpq
    have hmap : fwd (ψpoly p) = fwd (ψpoly q) := congrArg fwd hpq
    have hp :
        algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) p =
          algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) q := by
      calc
        algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) p =
          fwd (ψpoly p) := by
            symm
            exact congrArg
              (fun g : MvPolynomial (Fin r) K →+* FractionRing (MvPolynomial (Fin r) K) => g p)
              (mvPolynomial_fractionRing_baseChange_forward_comp_backward_eq_algebraMap
                (R := R) (K := K) r)
        _ = fwd (ψpoly q) := hmap
        _ =
          algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) q := by
            exact congrArg
              (fun g : MvPolynomial (Fin r) K →+* FractionRing (MvPolynomial (Fin r) K) => g q)
              (mvPolynomial_fractionRing_baseChange_forward_comp_backward_eq_algebraMap
                (R := R) (K := K) r)
    exact
      (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin r) K)
        (FractionRing (MvPolynomial (Fin r) K))) hp
  let back :
      FractionRing (MvPolynomial (Fin r) K) →+* FractionRing (MvPolynomial (Fin r) R) :=
    IsFractionRing.map
      (K := FractionRing (MvPolynomial (Fin r) K))
      (L := FractionRing (MvPolynomial (Fin r) R))
      (j := ψpoly) hψpoly_injective
  have hback_algebraMap (p : MvPolynomial (Fin r) K) :
      back (algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) p) =
        ψpoly p := by
    -- On polynomial numerators, the inverse localization map is just the defining polynomial map.
    change
      IsFractionRing.map
          (K := FractionRing (MvPolynomial (Fin r) K))
          (L := FractionRing (MvPolynomial (Fin r) R))
          (j := ψpoly) hψpoly_injective
          (algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) p) =
        ψpoly p
    delta IsFractionRing.map
    simpa only [IsLocalization.map_eq, RingHom.comp_apply] using
      (show
        algebraMap (FractionRing (MvPolynomial (Fin r) R))
            (FractionRing (MvPolynomial (Fin r) R)) (ψpoly p) = ψpoly p by
        simp)
  have hleft :
      back.comp fwd = RingHom.id (FractionRing (MvPolynomial (Fin r) R)) := by
    -- Compare both fraction-field endomorphisms on polynomial numerators from `R[Fin r]`.
    apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin r) R)
    intro p
    rw [RingHom.comp_apply, mvPolynomial_fractionRing_baseChangeForward_algebraMap
      (R := R) (K := K) r p, hback_algebraMap]
    exact congrArg
      (fun g : MvPolynomial (Fin r) R →+* FractionRing (MvPolynomial (Fin r) R) => g p)
      (mvPolynomial_fractionRing_baseChange_backward_comp_map_eq_algebraMap
        (R := R) (K := K) r)
  have hright :
      fwd.comp back = RingHom.id (FractionRing (MvPolynomial (Fin r) K)) := by
    -- The other composite is checked on polynomial numerators from `K[Fin r]`.
    apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin r) K)
    intro p
    rw [RingHom.comp_apply, hback_algebraMap]
    exact congrArg
      (fun g : MvPolynomial (Fin r) K →+* FractionRing (MvPolynomial (Fin r) K) => g p)
      (mvPolynomial_fractionRing_baseChange_forward_comp_backward_eq_algebraMap
        (R := R) (K := K) r)
  let eRing :
      FractionRing (MvPolynomial (Fin r) R) ≃+* FractionRing (MvPolynomial (Fin r) K) :=
    RingEquiv.ofRingHom fwd back hright hleft
  -- The ring equivalence is already `R`-linear because the forward map respects base constants.
  exact AlgEquiv.ofRingEquiv (f := eRing) fun a ↦ by
    change
      fwd (algebraMap (MvPolynomial (Fin r) R) (FractionRing (MvPolynomial (Fin r) R))
        (MvPolynomial.C a)) =
      algebraMap R (FractionRing (MvPolynomial (Fin r) K)) a
    rw [mvPolynomial_fractionRing_baseChangeForward_algebraMap (R := R) (K := K) r
      (MvPolynomial.C a)]
    calc
      algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
          (MvPolynomial.map (algebraMap R K) (MvPolynomial.C a)) =
        algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
          (MvPolynomial.C (algebraMap R K a)) := by
            simp
      _ = algebraMap K (FractionRing (MvPolynomial (Fin r) K)) (algebraMap R K a) := by
            symm
            simpa using
              congrArg
                (fun g : K →+* FractionRing (MvPolynomial (Fin r) K) =>
                  g (algebraMap R K a))
                (IsScalarTower.algebraMap_eq K (MvPolynomial (Fin r) K)
                  (FractionRing (MvPolynomial (Fin r) K)))
      _ = algebraMap R (FractionRing (MvPolynomial (Fin r) K)) a := by
            simpa using
              congrArg
                (fun g : R →+* FractionRing (MvPolynomial (Fin r) K) => g a)
                (IsScalarTower.algebraMap_eq R K
                  (FractionRing (MvPolynomial (Fin r) K)))

/-- Helper for Lemma 10.119.13: the fraction field of the closed-point localization of the
polynomial stage is canonically the same as the fraction field of the whole polynomial ring. -/
noncomputable def closed_point_polynomial_localization_fractionRing_algEquiv_polynomialFractionRing
    (r : ℕ) (q : PrimeSpectrum (MvPolynomial (Fin r) R)) :
    FractionRing (Localization.AtPrime q.asIdeal) ≃ₐ[R]
      FractionRing (MvPolynomial (Fin r) R) :=
  let P := MvPolynomial (Fin r) R
  let A := Localization.AtPrime q.asIdeal
  letI : Algebra A (Localization (nonZeroDivisors A)) := OreLocalization.instAlgebra
  letI : Algebra A (FractionRing P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      A (FractionRing P) q.asIdeal.primeCompl (nonZeroDivisors P)
      q.asIdeal.primeCompl_le_nonZeroDivisors
  letI : SMul A (FractionRing P) :=
    (show Algebra A (FractionRing P) from inferInstance).toSMul
  letI : IsScalarTower P A (FractionRing P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      A (FractionRing P) q.asIdeal.primeCompl (nonZeroDivisors P)
      q.asIdeal.primeCompl_le_nonZeroDivisors
  letI :
      IsFractionRing A
        (FractionRing P) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      q.asIdeal.primeCompl A (FractionRing P)
  letI : IsScalarTower R A (FractionRing P) :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      calc
        algebraMap R (FractionRing P) x =
            algebraMap P (FractionRing P) (algebraMap R P x) := by
              exact IsScalarTower.algebraMap_apply R P (FractionRing P) x
        _ =
            algebraMap A (FractionRing P) (algebraMap P A (algebraMap R P x)) := by
              exact IsScalarTower.algebraMap_apply P A (FractionRing P) (algebraMap R P x)
  let e :
      Localization (nonZeroDivisors A) ≃ₐ[A]
        FractionRing P :=
    IsLocalization.algEquiv (nonZeroDivisors A) _ _
  -- The first leg of the closed-point bridge is exactly the canonical fraction-ring equivalence,
  -- viewed over `R` through the existing localization tower.
  e.restrictScalars R

/-- Helper for Lemma 10.119.13: the fraction field of the closed-point localization of the
polynomial stage identifies with the basis field generated by the chosen transcendence basis. -/
noncomputable def closed_point_polynomial_localization_fractionField_algEquiv_basisField
    (r : ℕ) (x : Fin r → L) (hx : IsTranscendenceBasis K x)
    (q : PrimeSpectrum (MvPolynomial (Fin r) R))
    (_hq : q.asIdeal =
      RingHom.ker (MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0))) :
    FractionRing (Localization.AtPrime q.asIdeal) ≃ₐ[R]
      IntermediateField.adjoin K (Set.range x) :=
  -- The closed-point source proof factors through the common fraction field of the polynomial
  -- stage, then base-changes from `R` to `K`, and finally evaluates at the transcendence basis.
  (closed_point_polynomial_localization_fractionRing_algEquiv_polynomialFractionRing
      (R := R) r q).trans <|
    (mvPolynomial_fractionRing_baseChange_algEquiv (R := R) (K := K) r).trans <|
      (hx.1.aevalEquivField.restrictScalars R)

/-- Helper for Lemma 10.119.13: transporting the closed-point fraction field to `L` through the
generated basis field gives the compatibility needed for finite-dimensionality transfer. -/
lemma closed_point_polynomial_fractionField_to_L_compat
    (r : ℕ) (x : Fin r → L) (hx : IsTranscendenceBasis K x)
    (q : PrimeSpectrum (MvPolynomial (Fin r) R))
    (hq : q.asIdeal =
      RingHom.ker (MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0)))
    [Algebra (FractionRing (Localization.AtPrime q.asIdeal)) L]
    (hmap :
      algebraMap (FractionRing (Localization.AtPrime q.asIdeal)) L =
        RingHom.comp
          (algebraMap (IntermediateField.adjoin K (Set.range x)) L)
          ↑((closed_point_polynomial_localization_fractionField_algEquiv_basisField
            (R := R) (K := K) (L := L) r x hx q hq).toRingEquiv)) :
    RingHom.comp (algebraMap (FractionRing (Localization.AtPrime q.asIdeal)) L)
        ↑((closed_point_polynomial_localization_fractionField_algEquiv_basisField
          (R := R) (K := K) (L := L) r x hx q hq).symm.toRingEquiv) =
      RingHom.comp (RingEquiv.refl L)
        (algebraMap (IntermediateField.adjoin K (Set.range x)) L) := by
  -- Composing the transported map with the inverse equivalence recovers the original basis-field
  -- action on `L`.
  ext y
  change
    algebraMap (FractionRing (Localization.AtPrime q.asIdeal)) L
        (((closed_point_polynomial_localization_fractionField_algEquiv_basisField
          (R := R) (K := K) (L := L) r x hx q hq).symm) y) =
      algebraMap (IntermediateField.adjoin K (Set.range x)) L y
  rw [hmap]
  simp

/-- Helper for Lemma 10.119.13: the closed-point localization has fraction field finite over `L`
exactly when the basis field generated by the transcendence basis does. -/
lemma closed_point_polynomial_localization_fractionField_finiteDimensional
    (r : ℕ) (x : Fin r → L) (hx : IsTranscendenceBasis K x)
    (q : PrimeSpectrum (MvPolynomial (Fin r) R))
    (hq : q.asIdeal =
      RingHom.ker (MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0)))
    [Algebra (FractionRing (Localization.AtPrime q.asIdeal)) L]
    (hcompat :
      RingHom.comp (algebraMap (FractionRing (Localization.AtPrime q.asIdeal)) L)
          ↑((closed_point_polynomial_localization_fractionField_algEquiv_basisField
            (R := R) (K := K) (L := L) r x hx q hq).symm.toRingEquiv) =
        RingHom.comp (RingEquiv.refl L)
          (algebraMap (IntermediateField.adjoin K (Set.range x)) L))
    [FiniteDimensional (IntermediateField.adjoin K (Set.range x)) L] :
    FiniteDimensional (FractionRing (Localization.AtPrime q.asIdeal)) L := by
  -- Transport finite-dimensionality across the closed-point fraction-field identification.
  exact
    Module.Finite.of_equiv_equiv
      ((closed_point_polynomial_localization_fractionField_algEquiv_basisField
        (R := R) (K := K) (L := L) r x hx q hq).symm.toRingEquiv)
      (RingEquiv.refl L) hcompat

/-- Helper for Lemma 10.119.13: the essentially-finite-type case reduces to the finite-dimensional
case by adjoining a finite transcendence basis and localizing at the closed point. -/
theorem exists_discreteValuationSubring_dominating_from_essFiniteType_fraction_field_extension
    {R : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.EssFiniteType K L]
    (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  obtain ⟨r, x, hx, hfin⟩ :=
    exists_finTranscendenceBasis_finiteDimensional_over_adjoin (k := K) (K := L)
  let φ : MvPolynomial (Fin r) R →+* IsLocalRing.ResidueField R :=
    MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0)
  let q : PrimeSpectrum (MvPolynomial (Fin r) R) :=
    ⟨RingHom.ker φ, by
      simpa [φ] using closed_point_polynomial_ker_isPrime (R := R) r⟩
  have hq :
      q.asIdeal =
        RingHom.ker (MvPolynomial.eval₂Hom (IsLocalRing.residue R) (fun _ ↦ 0)) := by
    rfl
  letI : q.asIdeal.IsPrime := q.isPrime
  let S := Localization.AtPrime q.asIdeal
  letI : CommRing S := by infer_instance
  letI : IsDomain S := by infer_instance
  letI : IsLocalHom (algebraMap R S) :=
    closed_point_polynomial_localization_isLocalHom (R := R) r q hq
  have hS_not_field : ¬ IsField S :=
    closed_point_polynomial_localization_not_isField (R := R) r q hq hR
  let e : FractionRing S ≃ₐ[R] IntermediateField.adjoin K (Set.range x) :=
    closed_point_polynomial_localization_fractionField_algEquiv_basisField
      (R := R) (K := K) (L := L) r x hx q hq
  let eRing : FractionRing S ≃+* IntermediateField.adjoin K (Set.range x) := e.toRingEquiv
  letI : Algebra S (FractionRing S) := OreLocalization.instAlgebra
  letI : IsFractionRing S (FractionRing S) := by infer_instance
  letI : IsScalarTower R S (FractionRing S) := by infer_instance
  letI : Algebra K (IntermediateField.adjoin K (Set.range x)) := by infer_instance
  letI : Algebra (IntermediateField.adjoin K (Set.range x)) L := by infer_instance
  letI : Algebra (FractionRing S) L :=
    (RingHom.comp
      (algebraMap (IntermediateField.adjoin K (Set.range x)) L)
      (eRing : FractionRing S →+* IntermediateField.adjoin K (Set.range x))).toAlgebra
  have hFracL_map :
      algebraMap (FractionRing S) L =
        RingHom.comp
          (algebraMap (IntermediateField.adjoin K (Set.range x)) L)
          (eRing : FractionRing S →+* IntermediateField.adjoin K (Set.range x)) := by
    rw [RingHom.algebraMap_toAlgebra]
  have hcompat :
      RingHom.comp (algebraMap (FractionRing S) L)
          (eRing.symm : IntermediateField.adjoin K (Set.range x) →+* FractionRing S) =
        RingHom.comp (RingEquiv.refl L)
          (algebraMap (IntermediateField.adjoin K (Set.range x)) L) :=
    closed_point_polynomial_fractionField_to_L_compat
      (R := R) (K := K) (L := L) r x hx q hq hFracL_map
  letI : FiniteDimensional (FractionRing S) L :=
    closed_point_polynomial_localization_fractionField_finiteDimensional
      (R := R) (K := K) (L := L) r x hx q hq hcompat
  letI : Algebra S L :=
    (RingHom.comp (algebraMap (FractionRing S) L) (algebraMap S (FractionRing S))).toAlgebra
  letI : IsScalarTower S (FractionRing S) L := IsScalarTower.of_algebraMap_eq' rfl
  have hRFracL :
      RingHom.comp (algebraMap (FractionRing S) L) (algebraMap R (FractionRing S)) =
        algebraMap R L := by
    -- The transported fraction-field action still extends the original `R → K → L` map.
    ext a
    rw [hFracL_map]
    change
      algebraMap (IntermediateField.adjoin K (Set.range x)) L
          (e (algebraMap R (FractionRing S) a)) =
        algebraMap R L a
    rw [AlgEquiv.commutes]
    calc
      algebraMap (IntermediateField.adjoin K (Set.range x)) L
          (algebraMap R (IntermediateField.adjoin K (Set.range x)) a) =
        algebraMap (IntermediateField.adjoin K (Set.range x)) L
          (algebraMap K (IntermediateField.adjoin K (Set.range x)) (algebraMap R K a)) := by
            rw [IsScalarTower.algebraMap_apply R K (IntermediateField.adjoin K (Set.range x)) a]
      _ = algebraMap K L (algebraMap R K a) := by
            exact
              IsScalarTower.algebraMap_apply K
                (IntermediateField.adjoin K (Set.range x)) L (algebraMap R K a)
      _ = algebraMap R L a := by
            exact (IsScalarTower.algebraMap_apply R K L a).symm
  have hRSL :
      RingHom.comp (algebraMap S L) (algebraMap R S) = algebraMap R L := by
    -- The closed-point localization acts on `L` through its fraction field.
    ext a
    change
      algebraMap (FractionRing S) L (algebraMap S (FractionRing S) (algebraMap R S a)) =
        algebraMap R L a
    rw [show algebraMap S (FractionRing S) (algebraMap R S a) =
        algebraMap R (FractionRing S) a by
          exact IsScalarTower.algebraMap_apply R S (FractionRing S) a]
    exact congrArg (fun f : R →+* L => f a) hRFracL
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' hRSL.symm
  obtain ⟨V, hV_dvr, hSV⟩ :=
    exists_discreteValuationSubring_dominating_of_not_isField_of_finiteDimensional
      (R := S) (K := FractionRing S) (L := L) hS_not_field
  -- The source proof ends by composing domination along the local map `R → S`.
  refine ⟨V, hV_dvr, ?_⟩
  exact
    le_trans
      (range_dominates_range_of_isLocalHom (R := R) (A := S) (L := L))
      hSV

/-- Helper for Lemma 10.119.13: an explicit finitely generated extension `L / K` induces the
canonical essentially-finite-type structure on `L / FractionRing R`. -/
lemma fractionRing_extension_essFiniteType_from_wrapper
    {R : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R K L] [IsScalarTower R (FractionRing R) L]
    [Algebra.EssFiniteType K L] :
    Algebra.EssFiniteType (FractionRing R) L := by
  -- The source proof first passes from `R` to its fraction field and then peels that localization
  -- back off the composite essentially-finite-type map.
  letI : Algebra.EssFiniteType R K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  letI : Algebra.EssFiniteType R (FractionRing R) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing R) (nonZeroDivisors R)
  letI : Algebra.EssFiniteType R L := Algebra.EssFiniteType.comp R K L
  exact Algebra.EssFiniteType.of_comp R (FractionRing R) L

/-- Helper for Lemma 10.119.13: once `L` is viewed over the canonical fraction field of `R`, the
explicit essentially-finite-type theorem gives the desired dominating valuation subring. -/
lemma exists_discreteValuationSubring_dominating_via_canonical_fractionRing
    {R : Type u} {K : Type v} {L : Type w}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.EssFiniteType K L]
    (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  letI : FaithfulSMul R L :=
    FaithfulSMul.of_field_isFractionRing (R := R) (S := L) (K := K) (L := L)
  letI : Algebra (FractionRing R) L := FractionRing.liftAlgebra R L
  letI : IsScalarTower R (FractionRing R) L := FractionRing.isScalarTower_liftAlgebra R L
  letI : Algebra.EssFiniteType (FractionRing R) L :=
    fractionRing_extension_essFiniteType_from_wrapper (R := R) (K := K) (L := L)
  -- The final source step is now exactly the already-proved explicit theorem over `FractionRing R`.
  simpa using
    exists_discreteValuationSubring_dominating_from_essFiniteType_fraction_field_extension
      (R := R) (K := FractionRing R) (L := L) hR

/-- Lemma 10.119.13: if `R` is a Noetherian local domain with fraction field `K`, `R` is not a
field, and `L / K` is a finitely generated field extension, then there exists a discrete valuation
subring of `L` whose associated local subring dominates the image of `R` in `L`. -/
@[stacks 00PH]
theorem exists_discreteValuationSubring_dominating_of_not_isField_of_essFiniteType
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [IsScalarTower R K L] [Algebra.EssFiniteType K L]
    (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  -- Route correction: the source-faithful closing step is the canonical `FractionRing R` bridge
  -- proved immediately above, with the explicit `K`-data supplied by the theorem hypotheses.
  simpa using
    exists_discreteValuationSubring_dominating_via_canonical_fractionRing
      (R := R) (K := K) (L := L) hR

end
