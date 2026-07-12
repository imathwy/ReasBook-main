import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing IsLocalization IsFractionRing

/- Domain triage:
* `source-facing`: the example identifies the localization of `ℤ_(2)` away from `2` with `ℚ`
  and describes the induced map on spectra.
* `core/canonical`: the owner abstractions are `Localization.AtPrime`, `Localization.Away`,
  `PrimeSpectrum.basicOpen`, `IsLocalization`, and `IsFractionRing`.
* `bridge/view`: identify `D(2)` in `Spec(ℤ_(2))` with the singleton generic point, so
  localizing away from `2` is the same as localizing at `(0)`, hence the fraction ring. -/

private abbrev twoIdeal : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)

local instance : twoIdeal.IsPrime := by
  simpa [twoIdeal] using
    (Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 by norm_num)).2 Int.prime_two

local notation "ZLocalTwo" => Localization.AtPrime twoIdeal
local notation "twoInZLocalTwo" => (algebraMap ℤ ZLocalTwo (2 : ℤ))
local notation "ZLocalTwoAwayTwo" => Localization.Away twoInZLocalTwo
local notation "ZLocalTwoFrac" => Localization.AtPrime (⊥ : Ideal ZLocalTwo)
local notation "ZFrac" => Localization.AtPrime (⊥ : Ideal ℤ)
private lemma twoInZLocalTwo_ne_zero : twoInZLocalTwo ≠ 0 := by
  exact (map_ne_zero_iff (algebraMap ℤ ZLocalTwo)
    (IsLocalization.injective ZLocalTwo twoIdeal.primeCompl_le_nonZeroDivisors)).2 (by norm_num)

private lemma primeComap_eq_bot_of_two_not_mem (p : PrimeSpectrum ZLocalTwo)
    (hp : twoInZLocalTwo ∉ p.asIdeal) :
    Ideal.comap (algebraMap ℤ ZLocalTwo) p.asIdeal = ⊥ := by
  let J : Ideal ℤ := Ideal.comap (algebraMap ℤ ZLocalTwo) p.asIdeal
  have hJprime : J.IsPrime := by
    dsimp [J]
    exact Ideal.comap_isPrime (algebraMap ℤ ZLocalTwo) p.asIdeal
  have hJle : J ≤ twoIdeal := by
    simpa [J] using
      ((IsLocalization.AtPrime.orderIsoOfPrime ZLocalTwo twoIdeal
        ⟨p.asIdeal, p.isPrime⟩).2.2)
  have h2not : (2 : ℤ) ∉ J := by
    simpa [J] using hp
  by_cases hbot : J = ⊥
  · simpa [J] using hbot
  · letI : J.IsPrime := hJprime
    letI : NeZero J := ⟨hbot⟩
    have hnormPrime : Nat.Prime (Ideal.absNorm J) := by
      simpa [Ideal.under_def] using Nat.absNorm_under_prime J
    have habsNorm_mem : (Ideal.absNorm J : ℤ) ∈ twoIdeal :=
      hJle (by simpa [Ideal.under_def] using Int.absNorm_under_mem J)
    have htwo_dvd_absNorm_int : (2 : ℤ) ∣ (Ideal.absNorm J : ℤ) := by
      simpa [twoIdeal, Ideal.mem_span_singleton] using habsNorm_mem
    have htwo_dvd_absNorm : 2 ∣ Ideal.absNorm J := by
      exact_mod_cast htwo_dvd_absNorm_int
    have hnorm_eq_two : Ideal.absNorm J = 2 := by
      exact (Nat.prime_dvd_prime_iff_eq Nat.prime_two hnormPrime).mp htwo_dvd_absNorm |>.symm
    have htwo_mem : (2 : ℤ) ∈ J :=
      (Int.cast_mem_ideal_iff : (2 : ℤ) ∈ J ↔ _).2 (by simp [Ideal.under_def, hnorm_eq_two])
    exact (h2not htwo_mem).elim

private lemma prime_eq_bot_of_two_not_mem (p : PrimeSpectrum ZLocalTwo)
    (hp : twoInZLocalTwo ∉ p.asIdeal) : p = ⊥ := by
  have hcomap : Ideal.comap (algebraMap ℤ ZLocalTwo) p.asIdeal = ⊥ :=
    primeComap_eq_bot_of_two_not_mem p hp
  let e := IsLocalization.orderIsoOfPrime twoIdeal.primeCompl ZLocalTwo
  have hEq :
      e ⟨p.asIdeal, p.isPrime⟩ = e ⟨(⊥ : Ideal ZLocalTwo), Ideal.isPrime_bot⟩ := by
    apply Subtype.ext
    simp [e, hcomap]
  exact PrimeSpectrum.ext (congrArg Subtype.val (e.injective hEq))

private lemma basicOpen_twoInZLocalTwo_eq_singleton_genericPoint :
    (PrimeSpectrum.basicOpen twoInZLocalTwo : Set (PrimeSpectrum ZLocalTwo)) = {⊥} := by
  ext p
  constructor
  · exact fun hp ↦ prime_eq_bot_of_two_not_mem p hp
  · rintro rfl
    simpa [Ideal.mem_bot] using twoInZLocalTwo_ne_zero

private instance : IsFractionRing ZLocalTwo ZLocalTwoFrac := by
  convert (inferInstance :
    IsLocalization (⊥ : Ideal ZLocalTwo).primeCompl ZLocalTwoFrac)
  ext x
  simp [Ideal.primeCompl]

private instance : IsFractionRing ℤ ZFrac := by
  convert (inferInstance :
    IsLocalization (⊥ : Ideal ℤ).primeCompl ZFrac)
  ext x
  simp [Ideal.primeCompl]

private theorem isLocalizationAwayTwoToFrac : IsLocalization.Away twoInZLocalTwo ZLocalTwoFrac := by
  exact
    (PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton
      basicOpen_twoInZLocalTwo_eq_singleton_genericPoint).2 inferInstance

private noncomputable def awayTwoToFrac : ZLocalTwoAwayTwo ≃ₐ[ZLocalTwo] ZLocalTwoFrac := by
  letI := isLocalizationAwayTwoToFrac
  exact IsLocalization.algEquiv (Submonoid.powers twoInZLocalTwo) ZLocalTwoAwayTwo ZLocalTwoFrac

/-- Localizing `ℤ_(2)` at the image of `2` gives its fraction ring. -/
instance : IsFractionRing ZLocalTwo ZLocalTwoAwayTwo := by
  letI := isLocalizationAwayTwoToFrac
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors ZLocalTwo) awayTwoToFrac.symm

/-- Auxiliary equivalence for Chap10 Example 10 35 15: localizing `R = ℤ_(2)` at the image
of `2` canonically identifies `R[1 / 2]` with `ℚ`. -/
noncomputable def zLocalTwoAwayTwoAlgEquivRat : ZLocalTwoAwayTwo ≃ₐ[ℤ] ℚ :=
  letI := isLocalizationAwayTwoToFrac
  let eFrac :
      ZLocalTwoFrac ≃ₐ[ℤ] FractionRing ℤ :=
    let hbot :
        Ideal.comap (algebraMap ℤ ZLocalTwo) (⊥ : Ideal ZLocalTwo) = (⊥ : Ideal ℤ) :=
      Ideal.comap_bot_of_injective (algebraMap ℤ ZLocalTwo)
        (IsLocalization.injective ZLocalTwo twoIdeal.primeCompl_le_nonZeroDivisors)
    let eRaw :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization twoIdeal.primeCompl
        (⊥ : Ideal ZLocalTwo)
    let eBot :
        ZFrac ≃ₐ[ℤ] ZLocalTwoFrac := by
      change Localization (Ideal.primeCompl (⊥ : Ideal ℤ)) ≃ₐ[ℤ] ZLocalTwoFrac
      have hprimeCompl :
          (Ideal.comap (algebraMap ℤ ZLocalTwo) (⊥ : Ideal ZLocalTwo)).primeCompl =
            (⊥ : Ideal ℤ).primeCompl := by
        simp [hbot]
      exact hprimeCompl ▸ eRaw
    (FractionRing.algEquiv ℤ ZFrac).trans eBot |>.symm
  ((awayTwoToFrac.restrictScalars ℤ).trans eFrac).trans (FractionRing.algEquiv ℤ ℚ)

-- Proof sketch: This is the standard `AlgEquiv.commutes` property for the canonical
-- `ℤ`-algebra equivalence `zLocalTwoAwayTwoAlgEquivRat`.
/-- Chap10 Example 10 35 15: the canonical equivalence `R[1 / 2] ≃ₐ[ℤ] ℚ` is compatible
with the `ℤ`-algebra structure maps. -/
@[stacks 00G7]
theorem zLocalTwoAwayTwoAlgEquivRat_commutes (n : ℤ) :
    zLocalTwoAwayTwoAlgEquivRat (algebraMap ℤ ZLocalTwoAwayTwo n) = algebraMap ℤ ℚ n := by
  -- Use the commutation field carried by the bundled `ℤ`-algebra equivalence.
  exact AlgEquiv.commutes zLocalTwoAwayTwoAlgEquivRat n

noncomputable instance : Field ZLocalTwoAwayTwo :=
  IsFractionRing.toField ZLocalTwo

-- Proof sketch: `R[1 / 2]` is a field by the preceding fraction-ring instance, so its unique
-- point is `(0)`. Contracting `(0)` along the injective localization map `R → R[1 / 2]` gives
-- `(0)`, the generic point of `Spec(R)`.
/-- In Example 10.35.15, the unique point of `Spec(R[1 / 2])` maps to the generic point of
`Spec(R)` for `R = ℤ_(2)`. -/
theorem zLocalTwo_comap_closedPoint_eq_genericPoint :
    comap (algebraMap ZLocalTwo ZLocalTwoAwayTwo) (closedPoint ZLocalTwoAwayTwo) =
      (⊥ : PrimeSpectrum ZLocalTwo) := by
  rw [show closedPoint ZLocalTwoAwayTwo = (⊥ : PrimeSpectrum ZLocalTwoAwayTwo) by
    ext x
    simp [IsLocalRing.closedPoint]]
  ext x
  simp [Ideal.comap_bot_of_injective, IsFractionRing.injective ZLocalTwo ZLocalTwoAwayTwo]
