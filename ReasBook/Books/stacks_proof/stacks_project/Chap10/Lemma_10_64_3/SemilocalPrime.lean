import Mathlib
import StacksProject_2024.Chap10.Definition_10_64_1

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open scoped TensorProduct

namespace Ideal

variable (𝔭 : Ideal R) [𝔭.IsPrime]
variable [(𝔭.map (algebraMap R S)).IsPrime]

local notation "𝔭S" => 𝔭.map (algebraMap R S)
local notation "Rₚ" => Localization.AtPrime 𝔭
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭))
local notation "S𝔮" => Localization.AtPrime 𝔭S

/-- Helper for Lemma 10.64.3: under flat base change, the extended prime `𝔭S` contracts back to
`𝔭`. -/
lemma map_prime_lies_over_of_flat : Ideal.LiesOver 𝔭S 𝔭 := by
  let 𝔭' : Ideal R := Ideal.comap (algebraMap R S) 𝔭S
  letI : 𝔭'.IsPrime := by
    dsimp [𝔭']
    infer_instance
  letI : Ideal.LiesOver 𝔭S 𝔭' := ⟨rfl⟩
  -- Going down for flat maps finds a prime below `𝔭S` lying over the original `𝔭`.
  have hle : 𝔭 ≤ 𝔭' := Ideal.le_comap_map
  obtain ⟨Q, hQle, hQprime, hQover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := R) (S := S) (p := 𝔭) (q := 𝔭') 𝔭S hle
  letI : Q.IsPrime := hQprime
  -- The intermediate prime must already be `𝔭S`.
  have hmapleQ : 𝔭S ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hQover.over
  have hQeq : Q = 𝔭S := le_antisymm hQle hmapleQ
  exact ⟨by simpa [hQeq] using hQover.over⟩

/-- Helper for Lemma 10.64.3: localizing `S` away from the image of `𝔭.primeCompl` keeps those
denominators disjoint from the extended prime `𝔭S`. -/
lemma semilocal_denominators_disjoint_map_prime :
    Disjoint ((Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭)) : Set S) (𝔭S : Set S) := by
  -- Any denominator from `R \ 𝔭` cannot lie in `𝔭S`, since `𝔭S` still contracts to `𝔭`.
  rw [Set.disjoint_left]
  intro x hxden hxmem
  obtain ⟨r, hr, rfl⟩ : ∃ r : R, r ∈ Ideal.primeCompl 𝔭 ∧ algebraMap R S r = x := by
    simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map] using hxden
  have hover : Ideal.comap (algebraMap R S) (𝔭.map (algebraMap R S)) = 𝔭 := by
    simpa [Ideal.under_def] using
      (show Ideal.under R (𝔭.map (algebraMap R S)) = 𝔭 from
        (map_prime_lies_over_of_flat (𝔭 := 𝔭)).over.symm)
  have hrmem : r ∈ Ideal.comap (algebraMap R S) (𝔭.map (algebraMap R S)) := by
    simpa [Ideal.mem_comap] using hxmem
  exact hr <| by simpa [hover] using hrmem

/-- Helper for Lemma 10.64.3: after semilocalizing `S` away from `𝔭`, the extended prime `𝔭S`
remains prime. -/
lemma semilocal_map_prime_isPrime :
    (map (algebraMap S Sₚ) 𝔭S).IsPrime := by
  -- The localization criterion for prime ideals applies because the denominators avoid `𝔭S`.
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭)) Sₚ 𝔭S
    (show (𝔭.map (algebraMap R S)).IsPrime from inferInstance)
    (semilocal_denominators_disjoint_map_prime (𝔭 := 𝔭))

attribute [local instance] semilocal_map_prime_isPrime

/-- Helper for Lemma 10.64.3: semilocalizing `S` away from `𝔭` and then contracting the image of
`𝔭S` recovers `𝔭S` itself. -/
lemma semilocal_comap_map_prime :
    comap (algebraMap S Sₚ) (map (algebraMap S Sₚ) 𝔭S) = 𝔭S := by
  -- This is the standard contraction formula for a prime ideal disjoint from the denominators.
  exact IsLocalization.comap_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭)) Sₚ
    (show (𝔭.map (algebraMap R S)).IsPrime from inferInstance)
    (semilocal_denominators_disjoint_map_prime (𝔭 := 𝔭))

/-- Helper for Lemma 10.64.3: in the semilocal prime quotient `Sₚ / 𝔭Sₚ`, the class of any
element outside the localized prime is a nonzerodivisor. This is the base layer of the source
filtration argument for higher powers. -/
lemma semilocal_prime_quotient_mk_mem_nonZeroDivisors
    {z : Sₚ} (hz : z ∉ map (algebraMap S Sₚ) 𝔭S) :
    Ideal.Quotient.mk (map (algebraMap S Sₚ) 𝔭S) z ∈
      nonZeroDivisors (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) := by
  -- The quotient by a prime ideal is a domain, so it suffices to show the class is nonzero.
  letI : (map (algebraMap S Sₚ) 𝔭S).IsPrime := semilocal_map_prime_isPrime (𝔭 := 𝔭)
  letI : IsDomain (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) := by infer_instance
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzzero
  exact hz <| by simpa [Ideal.Quotient.eq_zero_iff_mem] using hzzero

/-- Helper for Lemma 10.64.3: on the first semilocal quotient `Sₚ / 𝔭Sₚ`, an element coming from
`S` and lying outside `𝔭S` already acts as a nonzerodivisor. -/
lemma semilocal_quotient_map_prime_mk_mem_nonZeroDivisors {x : S} (hx : x ∉ 𝔭S) :
    Ideal.Quotient.mk (map (algebraMap S Sₚ) 𝔭S) (algebraMap S Sₚ x) ∈
      nonZeroDivisors (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) := by
  -- Reduce the source-level element to the semilocal quotient statement just proved.
  apply semilocal_prime_quotient_mk_mem_nonZeroDivisors (𝔭 := 𝔭)
  intro hxmem
  have hxcomap : x ∈ comap (algebraMap S Sₚ) (map (algebraMap S Sₚ) 𝔭S) := by
    simpa [Ideal.mem_comap] using hxmem
  exact hx <| by simpa [semilocal_comap_map_prime (𝔭 := 𝔭)] using hxcomap

/-- Helper for Lemma 10.64.3: every denominator outside the semilocalized prime ideal acts as a
nonzerodivisor on the prime quotient `Sₚ / 𝔭Sₚ`. -/
lemma semilocal_denominator_nonZeroDivisors_prime_quotient :
    Algebra.algebraMapSubmonoid (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S)
      (Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S)) ≤
        nonZeroDivisors (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) := by
  intro y hy
  rcases (show ∃ z : Sₚ,
      z ∈ Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S) ∧
        algebraMap Sₚ (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) z = y by
      simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map] using hy) with ⟨z, hz, rfl⟩
  exact semilocal_prime_quotient_mk_mem_nonZeroDivisors (𝔭 := 𝔭) hz

/-- Helper for Lemma 10.64.3: every denominator used to define the semilocal ring `Sₚ` stays
outside the extended prime `𝔭S`. -/
lemma semilocal_denominator_le_primeCompl_map :
    Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭) ≤ Ideal.primeCompl 𝔭S := by
  -- This is the set-theoretic disjointness already recorded for the semilocal denominator set.
  intro x hxden
  have hdisj := semilocal_denominators_disjoint_map_prime (R := R) (S := S) (𝔭 := 𝔭)
  rw [Set.disjoint_left] at hdisj
  exact fun hxmem ↦ hdisj hxden hxmem

/-- Helper for Lemma 10.64.3: the canonical comparison map from the semilocal ring `Sₚ` to the
prime localization `S𝔮`. -/
noncomputable def semilocalToLocal : Sₚ →+* S𝔮 :=
  IsLocalization.map
    (R := S)
    (P := S)
    (S := Sₚ)
    (Q := S𝔮)
    (M := Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭))
    (T := Ideal.primeCompl 𝔭S)
    (g := RingHom.id S)
    (semilocal_denominator_le_primeCompl_map (𝔭 := 𝔭))

/-- Helper for Lemma 10.64.3: the semilocal-to-local comparison agrees with the original
localization map on elements of `S`. -/
@[simp] lemma semilocalToLocal_to_map (x : S) :
    semilocalToLocal (𝔭 := 𝔭) (algebraMap S Sₚ x) = algebraMap S S𝔮 x := by
  -- `IsLocalization.map` is characterized by its action on the source ring.
  simp [semilocalToLocal]

/-- Helper for Lemma 10.64.3: after identifying the contracted semilocal prime with `𝔭S`, the
iterated-localization equivalence compares the prime localization of `Sₚ` with `S𝔮`. -/
noncomputable abbrev semilocalLocalizationAtMapPrimeAlgEquivOfComapEq
    {I : Ideal S} [I.IsPrime]
    (hI : I = comap (algebraMap S Sₚ) (map (algebraMap S Sₚ) 𝔭S)) :
    Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S) ≃ₐ[S] Localization.AtPrime I := by
  -- Substitute the contracted prime into the standard localization-of-a-localization equivalence.
  subst hI
  exact
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭))
      (p := map (algebraMap S Sₚ) 𝔭S)).symm

/-- Helper for Lemma 10.64.3: localizing the semilocal ring `Sₚ` at the image of `𝔭S` recovers
the prime localization `S𝔮`. -/
noncomputable def semilocalLocalizationAtMapPrimeAlgEquiv :
    Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S) ≃ₐ[S] S𝔮 := by
  -- The previous helper packages the only dependent-type transport needed here.
  exact semilocalLocalizationAtMapPrimeAlgEquivOfComapEq
    (𝔭 := 𝔭) (I := 𝔭S) (semilocal_comap_map_prime (𝔭 := 𝔭)).symm

/-- Helper for Lemma 10.64.3: the iterated-localization equivalence sends the canonical map out of
`Sₚ` to the comparison map `Sₚ → S𝔮`. -/
lemma semilocalLocalizationAtMapPrimeAlgEquiv_comp_algebraMap :
    ((semilocalLocalizationAtMapPrimeAlgEquiv (𝔭 := 𝔭)).toRingHom).comp
        (algebraMap Sₚ (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S))) =
      semilocalToLocal (𝔭 := 𝔭) := by
  -- Compare the two maps on the source ring `S`, then use localization extensionality on `Sₚ`.
  apply IsLocalization.ringHom_ext (M := Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭))
  ext x
  calc
    (semilocalLocalizationAtMapPrimeAlgEquiv (𝔭 := 𝔭))
        (algebraMap Sₚ (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S))
          (algebraMap S Sₚ x))
        = (semilocalLocalizationAtMapPrimeAlgEquiv (𝔭 := 𝔭))
            (algebraMap S (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S)) x) := by
              rfl
    _ = algebraMap S S𝔮 x := by
          exact (semilocalLocalizationAtMapPrimeAlgEquiv (𝔭 := 𝔭)).commutes x
    _ = semilocalToLocal (𝔭 := 𝔭) (algebraMap S Sₚ x) := by
          symm
          exact semilocalToLocal_to_map (𝔭 := 𝔭) x

/-- Helper for Lemma 10.64.3: the semilocal-to-local comparison intertwines the two algebra maps
out of `S`. -/
@[simp] lemma semilocalToLocal_comp_algebraMap :
    (semilocalToLocal (𝔭 := 𝔭)).comp (algebraMap S Sₚ) = algebraMap S S𝔮 := by
  -- Equality of ring maps is checked on the original ring `S`.
  ext x
  simp [semilocalToLocal]

/-- Helper for Lemma 10.64.3: view the prime localization `S𝔮` as an `Sₚ`-algebra through the
comparison map `Sₚ → S𝔮`. -/
noncomputable local instance semilocalToLocalAlgebra : Algebra Sₚ S𝔮 :=
  (semilocalToLocal (𝔭 := 𝔭)).toAlgebra

/-- Helper for Lemma 10.64.3: the comparison `Sₚ → S𝔮` is the ordinary algebra map between the
two localization rings. -/
@[simp] lemma semilocalToLocal_eq_algebraMap :
    semilocalToLocal (𝔭 := 𝔭) = algebraMap Sₚ S𝔮 :=
  rfl

/-- Helper for Lemma 10.64.3: under the semilocal-to-local comparison, the semilocalized prime
maps to the maximal ideal of `S𝔮`. -/
lemma semilocalToLocal_map_map_prime :
    map (semilocalToLocal (𝔭 := 𝔭)) (map (algebraMap S Sₚ) 𝔭S) =
      IsLocalRing.maximalIdeal S𝔮 := by
  -- Push the prime across the comparison and identify the target image by the prime-localization
  -- formula for maximal ideals.
  calc
    map (semilocalToLocal (𝔭 := 𝔭)) (map (algebraMap S Sₚ) 𝔭S)
        = map ((semilocalToLocal (𝔭 := 𝔭)).comp (algebraMap S Sₚ)) 𝔭S := by
            rw [Ideal.map_map]
    _ = map (algebraMap S S𝔮) 𝔭S := by
          rw [semilocalToLocal_comp_algebraMap (𝔭 := 𝔭)]
    _ = IsLocalRing.maximalIdeal S𝔮 := by
          simpa using (Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭S))

/-- Helper for Lemma 10.64.3: the induced comparison on quotient rings
`Sₚ / J^n → S𝔮 / maximalIdeal(S𝔮)^n`. -/
noncomputable def semilocalPowQuotientToLocalPowQuotient (n : ℕ) :
    Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n →+*
      S𝔮 ⧸ (IsLocalRing.maximalIdeal S𝔮) ^ n := by
  let hbase :
      map (algebraMap S Sₚ) 𝔭S ≤
        comap (semilocalToLocal (𝔭 := 𝔭)) (IsLocalRing.maximalIdeal S𝔮) := by
    -- The semilocalized prime lands inside the maximal ideal after passing to `S𝔮`.
    exact Ideal.map_le_iff_le_comap.mp <|
      le_of_eq (semilocalToLocal_map_map_prime (𝔭 := 𝔭))
  let hpow :
      (map (algebraMap S Sₚ) 𝔭S) ^ n ≤
        comap (semilocalToLocal (𝔭 := 𝔭)) ((IsLocalRing.maximalIdeal S𝔮) ^ n) := by
    -- Power the containment and then use the canonical comparison of powers under comap.
    have hpow_base :
        (map (algebraMap S Sₚ) 𝔭S) ^ n ≤
          (comap (semilocalToLocal (𝔭 := 𝔭)) (IsLocalRing.maximalIdeal S𝔮)) ^ n :=
      Ideal.pow_right_mono hbase n
    exact hpow_base.trans
      (Ideal.le_comap_pow (f := semilocalToLocal (𝔭 := 𝔭))
        (K := IsLocalRing.maximalIdeal S𝔮) n)
  exact Ideal.quotientMap ((IsLocalRing.maximalIdeal S𝔮) ^ n)
    (semilocalToLocal (𝔭 := 𝔭)) hpow

/-- Helper for Lemma 10.64.3: the quotient comparison fits into the expected commutative square
with the quotient maps out of `S`. -/
lemma semilocalPowQuotientToLocalPowQuotient_comp_quotient (n : ℕ) :
    (semilocalPowQuotientToLocalPowQuotient (𝔭 := 𝔭) n).comp
        (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
          (algebraMap S Sₚ)) =
      (((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S𝔮) ^ n))).comp
        (algebraMap S S𝔮)) := by
  -- Both composites are determined by their value on the original ring `S`.
  ext x
  simp [semilocalPowQuotientToLocalPowQuotient, semilocalToLocal]

/-- Helper for Lemma 10.64.3: composing a ring map with an injective comparison map does not
change its kernel. -/
lemma ker_comp_eq_of_injective {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hg : Function.Injective g) :
    RingHom.ker (g.comp f) = RingHom.ker f := by
  -- Kernel membership is the same equality after canceling the injective comparison map.
  ext x
  simp only [RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · intro hx
    exact hg (by simpa using hx)
  · intro hx
    simpa using congrArg g hx

/-- Helper for Lemma 10.64.3: any injective comparison out of the semilocal power quotient
preserves the kernel of the quotient map `S → Sₚ / J^n`, where
`J = map (algebraMap S Sₚ) 𝔭S`. -/
lemma ker_semilocal_quotient_eq_ker_of_injective_comparison
    (n : ℕ) {T : Type*} [CommRing T]
    (g : Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n →+* T)
    (hg : Function.Injective g) :
    RingHom.ker
        (g.comp ((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n)).comp
          (algebraMap S Sₚ))) =
      RingHom.ker
        ((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n)).comp
          (algebraMap S Sₚ)) := by
  -- Once the semilocal-to-local comparison is injective, kernel descent is immediate.
  ext x
  simp only [RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · intro hx
    exact hg (by simpa using hx)
  · intro hx
    simpa using congrArg g hx

/-- Helper for Lemma 10.64.3: the symbolic power `𝔭S^(n)` is the kernel of the local quotient map
to `S𝔮 / maximalIdeal(S𝔮)^n`. -/
lemma symbolicPower_map_eq_ker_local_pow_quotient (n : ℕ) :
    symbolicPower 𝔭S n =
      RingHom.ker
        (((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S𝔮) ^ n))).comp
          (algebraMap S S𝔮)) := by
  -- Rewrite the symbolic power through its defining quotient-kernel description.
  rw [Ideal.symbolicPower_eq_ker_quotient_map_pow]
  -- Then identify the localized image of `𝔭S` with the maximal ideal of `S𝔮`.
  rw [Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭S)]

/-- Helper for Lemma 10.64.3: injectivity of the semilocal-to-local quotient comparison identifies
the two quotient kernels. -/
lemma ker_local_pow_quotient_eq_ker_semilocal_pow_quotient_of_injective
    (n : ℕ)
    (hinj :
      Function.Injective
        (semilocalPowQuotientToLocalPowQuotient (R := R) (S := S) (𝔭 := 𝔭) n)) :
    RingHom.ker
        (((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S𝔮) ^ n))).comp
          (algebraMap S S𝔮)) =
      RingHom.ker
        (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
          (algebraMap S Sₚ)) := by
  -- The square above rewrites the local quotient map as an injective postcomposition of the
  -- semilocal quotient map.
  rw [← semilocalPowQuotientToLocalPowQuotient_comp_quotient (𝔭 := 𝔭) n]
  exact ker_semilocal_quotient_eq_ker_of_injective_comparison
    (𝔭 := 𝔭) n (semilocalPowQuotientToLocalPowQuotient (𝔭 := 𝔭) n) hinj

end Ideal

end
