import Mathlib
import stacks_project.Chap10.Definition_10_64_1

-- Declarations for this item will be appended below by the statement pipeline.

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

/-
Domain triage: this file stays in commutative algebra of prime ideals, flatness, and localization.
The owner abstraction is the source-facing `Ideal.symbolicPower` from `Definition_10_64_1`; this
lemma is a derived base-change statement for that owner, not a new wrapper notion.

Relevant upstream owner-side declarations inspected before refinement:
* `Ideal.symbolicPower` and `Ideal.symbolicPower_eq_ker_quotient_map_pow`
* `RingHom.Flat.generalizingMap_comap` / `Ideal.exists_ideal_le_liesOver_of_le`
* `IsLocalization.AtPrime.map_eq_maximalIdeal` and `IsLocalization.AtPrime.comap_maximalIdeal`
-/

-- Proof sketch: rewrite both symbolic powers through the owner declaration
-- `Ideal.symbolicPower`; flatness identifies the extension of the kernel
-- `R → R_𝔭 / 𝔭^n R_𝔭` with the kernel of the base-changed map
-- `S → S_𝔮 / 𝔭^n S_𝔮`, and the primeness of `𝔭S` lets one compare this with the defining kernel
-- of the symbolic power of `𝔭S`.
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

/-- Helper for Lemma 10.64.3: the tensor-side inclusion of the localized base ring `Rₚ` into
`S ⊗[R] Rₚ`. -/
noncomputable abbrev tensorLocalizedBaseIncludeRight : Rₚ →+* (S ⊗[R] Rₚ) :=
  (Algebra.TensorProduct.includeRight : Rₚ →ₐ[R] S ⊗[R] Rₚ).toRingHom

/-- Helper for Lemma 10.64.3: under the tensor-localization equivalence
`S ⊗[R] Rₚ ≃ Sₚ`, the tensor-side image of the `n`th power of the localized prime ideal is the
`n`th power of the semilocalized prime. -/
lemma localized_prime_map_eq_semilocalized_prime :
    map (algebraMap Rₚ Sₚ) (map (algebraMap R Rₚ) 𝔭) =
      map (algebraMap S Sₚ) 𝔭S := by
  -- Compare the two ideal maps by identifying the underlying composite ring homomorphisms.
  have hbase :
      (algebraMap Rₚ Sₚ).comp (algebraMap R Rₚ) =
        (algebraMap S Sₚ).comp (algebraMap R S) := by
    calc
      (algebraMap Rₚ Sₚ).comp (algebraMap R Rₚ) = algebraMap R Sₚ := by
        symm
        exact IsScalarTower.algebraMap_eq R Rₚ Sₚ
      _ = (algebraMap S Sₚ).comp (algebraMap R S) := by
        exact IsScalarTower.algebraMap_eq R S Sₚ
  calc
    map (algebraMap Rₚ Sₚ) (map (algebraMap R Rₚ) 𝔭)
        = map (((algebraMap Rₚ Sₚ).comp (algebraMap R Rₚ))) 𝔭 := by
            rw [Ideal.map_map]
    _ = map (((algebraMap S Sₚ).comp (algebraMap R S))) 𝔭 := by
          rw [hbase]
    _ = map (algebraMap S Sₚ) 𝔭S := by
          rw [← Ideal.map_map]

/-- Helper for Lemma 10.64.3: under the tensor-localization equivalence
`S ⊗[R] Rₚ ≃ Sₚ`, the tensor-side image of the `n`th power of the localized prime ideal is the
`n`th power of the semilocalized prime. -/
lemma tensorLeftAlgEquiv_map_localized_prime_pow (n : ℕ) :
    map (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S).toRingHom
        (((map (algebraMap R Rₚ) 𝔭) ^ n).map (tensorLocalizedBaseIncludeRight (R := R) (S := S)
          (𝔭 := 𝔭))) =
      (map (algebraMap S Sₚ) 𝔭S) ^ n := by
  -- The base-change equivalence sends the tensor-side copy `1 ⊗ x` of `Rₚ` to its image in `Sₚ`.
  have hcomp :
      ((Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S).toRingHom).comp
          (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭)) =
        algebraMap Rₚ Sₚ := by
    ext x
    simpa using
      (Localization.tensorLeftAlgEquiv_apply_one_tmul (M := Ideal.primeCompl 𝔭) (S := S) x)
  -- Then the ideal transport is just functoriality of `Ideal.map`, together with `Ideal.map_pow`.
  calc
    map (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S).toRingHom
        (((map (algebraMap R Rₚ) 𝔭) ^ n).map (tensorLocalizedBaseIncludeRight (R := R) (S := S)
          (𝔭 := 𝔭)))
        = map (algebraMap Rₚ Sₚ) ((map (algebraMap R Rₚ) 𝔭) ^ n) := by
            rw [Ideal.map_map]
            rw [hcomp]
    _ = (map (algebraMap Rₚ Sₚ) (map (algebraMap R Rₚ) 𝔭)) ^ n := by
          rw [Ideal.map_pow]
    _ = (map (algebraMap S Sₚ) 𝔭S) ^ n := by
          exact congrArg (fun K : Ideal Sₚ ↦ K ^ n)
            (localized_prime_map_eq_semilocalized_prime
              (R := R) (S := S) (𝔭 := 𝔭))

/-- Helper for Lemma 10.64.3: the right-unit tensor equivalence sends the tensor-side copy of the
base ring back to the original `R → S` algebra map. -/
lemma tensor_rid_comp_includeRight :
    (Algebra.TensorProduct.rid R S S).toRingHom.comp
        (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom =
      algebraMap R S := by
  -- The right tensor unit identifies `1 ⊗ r` with the scalar action of `r` on `S`.
  ext x
  simpa [Algebra.smul_def]

/-- Helper for Lemma 10.64.3: extending an ideal to `S ⊗[R] R` along `includeRight` and then
pushing it across the right-unit equivalence recovers the usual extension to `S`. -/
lemma tensor_rid_map_includeRight_eq_map (I : Ideal R) :
    map (Algebra.TensorProduct.rid R S S).toRingHom
        (map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) I) =
      map (algebraMap R S) I := by
  -- Functoriality of `Ideal.map` along the composite `rid ∘ includeRight = algebraMap`.
  calc
    map (Algebra.TensorProduct.rid R S S).toRingHom
        (map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) I)
        =
          map ((Algebra.TensorProduct.rid R S S).toRingHom.comp
            (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom) I := by
            simpa using
              (Ideal.map_map
                (I := I)
                ((Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom)
                ((Algebra.TensorProduct.rid R S S).toRingHom))
    _ = map (algebraMap R S) I := by
          rw [tensor_rid_comp_includeRight (R := R) (S := S)]

/-- Helper for Lemma 10.64.3: after precomposing with the right-unit tensor equivalence
`S ⊗[R] R ≃ S`, the map `includeLeft : S → S ⊗[R] (Rₚ / 𝔭ₚ^n)` becomes the tensorization of the
canonical algebra map `R → Rₚ / 𝔭ₚ^n`. -/
lemma tensor_map_eq_includeLeft_comp_rid (n : ℕ) :
    ((Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n))).toRingHom) =
      (((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
          Algebra.TensorProduct.includeLeft).toRingHom).comp
        (Algebra.TensorProduct.rid R S S).toRingHom) := by
  -- This is exactly the right-unit identity used in mathlib's `includeLeft_bijective` proof.
  -- Reprove it locally so the later kernel transport can cite a named lemma in this file.
  have h :
      ((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
          Algebra.TensorProduct.includeLeft).comp
        (Algebra.TensorProduct.rid R S S).toAlgHom) =
        Algebra.TensorProduct.map (.id S S)
          (Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) := by
    ext <;> simp
  simpa using congrArg AlgHom.toRingHom h.symm

/-- Helper for Lemma 10.64.3: transporting the tensorized quotient kernel across the right-unit
equivalence identifies it with the image of the kernel of `includeLeft`. -/
lemma ker_tensor_map_eq_map_rid_symm_ker_includeLeft (n : ℕ) :
    RingHom.ker
        ((Algebra.TensorProduct.map (AlgHom.id R S)
          (Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n))).toRingHom) =
      Ideal.map (Algebra.TensorProduct.rid R S S).symm.toRingHom
        (RingHom.ker
          ((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
            Algebra.TensorProduct.includeLeft).toRingHom)) := by
  -- Rewrite the tensorized quotient map through `rid`, then convert the resulting kernel-comap
  -- into an ideal map along the inverse equivalence.
  rw [tensor_map_eq_includeLeft_comp_rid (R := R) (S := S) (𝔭 := 𝔭) n]
  rw [RingHom.ker_eq_comap_bot, RingHom.ker_eq_comap_bot, ← Ideal.comap_comap]
  let J : Ideal S :=
    RingHom.ker
      ((show S →ₐ[S] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) from
        Algebra.TensorProduct.includeLeft).toRingHom)
  change Ideal.comap (Algebra.TensorProduct.rid R S S).toRingHom J =
    Ideal.map (Algebra.TensorProduct.rid R S S).symm.toRingHom J
  exact (Ideal.map_symm (f := (Algebra.TensorProduct.rid R S S).toRingEquiv) (I := J)).symm

/-- Helper for Lemma 10.64.3: flat base change turns the defining kernel of `𝔭^(n)` into the
kernel of the tensor-side quotient map before localization transport. -/
lemma tensor_quotient_kernel_eq_map_symbolicPower (n : ℕ) :
    RingHom.ker
      ((Algebra.TensorProduct.includeLeft :
          S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) =
      map (algebraMap R S) (𝔭.symbolicPower n) := by
  let g : R →ₐ[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) :=
    Algebra.ofId R (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)
  have hkernel_tensor :
      RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom) =
        Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
          (RingHom.ker g.toRingHom) := by
    -- Flatness computes the tensor kernel as the range of tensoring the defining kernel subtype.
    rw [← Submodule.restrictScalars_inj R]
    change
      (TensorProduct.AlgebraTensorModule.lTensor R S g.toLinearMap).ker =
        Submodule.restrictScalars R
          (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
            (RingHom.ker g.toRingHom))
    rw [Module.Flat.ker_lTensor_eq (S := R) (M := S) (f := g.toLinearMap)]
    -- Then the tensor range is exactly the ideal generated by the tensor-side copy of the kernel.
    simpa using
      (TensorProduct.AlgebraTensorModule.range_lTensor_idealMap
        (R := R) (A := S) (B := R) (S := R) (I := RingHom.ker g.toRingHom))
  have hkernel_source : RingHom.ker g.toRingHom = 𝔭.symbolicPower n := by
    -- The source kernel is the defining kernel of the `n`th symbolic power.
    change
      RingHom.ker
          (((Ideal.Quotient.mk ((map (algebraMap R Rₚ) 𝔭) ^ n))).comp
            (algebraMap R Rₚ)) =
        𝔭.symbolicPower n
    exact (Ideal.symbolicPower_eq_ker_quotient_map_pow (𝔭 := 𝔭) n).symm
  have htransport :
      RingHom.ker
          ((Algebra.TensorProduct.includeLeft :
              S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) =
        Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
          (RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom)) := by
    have hbridge :=
      ker_tensor_map_eq_map_rid_symm_ker_includeLeft (R := R) (S := S) (𝔭 := 𝔭) n
    have hrid_comp :
        (Algebra.TensorProduct.rid R S S).toRingHom.comp
            (Algebra.TensorProduct.rid R S S).symm.toRingHom =
          RingHom.id S := by
      ext x
      exact (Algebra.TensorProduct.rid R S S).apply_symm_apply x
    -- Mapping across `rid` cancels the earlier transport through `rid.symm`.
    calc
      RingHom.ker
          ((Algebra.TensorProduct.includeLeft :
              S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom)
          =
            Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
              (Ideal.map (Algebra.TensorProduct.rid R S S).symm.toRingHom
                (RingHom.ker
                  ((Algebra.TensorProduct.includeLeft :
                      S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom))) := by
              symm
              rw [Ideal.map_map, hrid_comp, Ideal.map_id]
      _ = Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
            (RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom)) := by
              simpa [g] using congrArg
                (Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom) hbridge.symm
  -- The existing `rid` transport turns the tensor-side kernel computation into the public kernel.
  calc
    RingHom.ker
        ((Algebra.TensorProduct.includeLeft :
            S →ₐ[R] S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom)
        =
          Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
            (RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom)) := by
              exact htransport
    _ = Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
          (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
            (RingHom.ker g.toRingHom)) := by
            rw [hkernel_tensor]
    _ = Ideal.map (Algebra.TensorProduct.rid R S S).toRingHom
          (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R)
            (𝔭.symbolicPower n)) := by
            rw [hkernel_source]
    _ = map (algebraMap R S) (𝔭.symbolicPower n) := by
          simpa using tensor_rid_map_includeRight_eq_map
            (R := R) (S := S) (I := 𝔭.symbolicPower n)

/-- Helper for Lemma 10.64.3: the tensor quotient `S ⊗[R] (Rₚ / 𝔭ₚ^n)` identifies with the
semilocal quotient `Sₚ / J^n`, where `J = map (algebraMap S Sₚ) 𝔭S`. -/
noncomputable def tensorQuotientToSemilocalPowQuotientAlgEquiv (n : ℕ) :
    S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n) ≃ₐ[S]
      Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n := by
  -- First rewrite the tensor quotient as a quotient of `S ⊗[R] Rₚ`.
  let e₁ :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := R) S Rₚ S
      ((map (algebraMap R Rₚ) 𝔭) ^ n)
  -- Then transport that quotient across the tensor-localization equivalence.
  let e₂ :
      ((S ⊗[R] Rₚ) ⧸
          (((map (algebraMap R Rₚ) 𝔭) ^ n).map
            (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭)))) ≃ₐ[S]
        (Sₚ ⧸ ((map (algebraMap S Sₚ) 𝔭S) ^ n)) :=
    Ideal.quotientEquivAlg
      ((((map (algebraMap R Rₚ) 𝔭) ^ n).map
        (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭))))
      (((map (algebraMap S Sₚ) 𝔭S) ^ n))
      (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
      (tensorLeftAlgEquiv_map_localized_prime_pow (R := R) (S := S) (𝔭 := 𝔭) n).symm
  exact e₁.trans e₂

/-- Helper for Lemma 10.64.3: the tensor-to-semilocal quotient equivalence sends `includeLeft s`
to the class of `algebraMap S Sₚ s`. -/
@[simp] lemma tensorQuotientToSemilocalPowQuotientAlgEquiv_apply_includeLeft
    (n : ℕ) (s : S) :
    tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n
      ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
          S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) s) =
      Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n) (algebraMap S Sₚ s) := by
  -- The tensor quotient equivalence sends `includeLeft s = s ⊗ 1` to the quotient class of
  -- `s ⊗ 1`, and the tensor-localization equivalence identifies that tensor with `algebraMap s`.
  change
    Ideal.quotientEquivAlg _ _ (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
        (tensorLeftAlgEquiv_map_localized_prime_pow (R := R) (S := S) (𝔭 := 𝔭) n).symm
      ((Algebra.TensorProduct.tensorQuotientEquiv (R := R) S Rₚ S
        ((map (algebraMap R Rₚ) 𝔭) ^ n))
        (s ⊗ₜ[R] (Ideal.Quotient.mk ((map (algebraMap R Rₚ) 𝔭) ^ n) (1 : Rₚ)))) =
    Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n) (algebraMap S Sₚ s)
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  calc
    Ideal.quotientEquivAlg _ _ (Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
        (tensorLeftAlgEquiv_map_localized_prime_pow (R := R) (S := S) (𝔭 := 𝔭) n).symm
          (Ideal.Quotient.mk
            (((map (algebraMap R Rₚ) 𝔭) ^ n).map
              (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭)))
            (s ⊗ₜ[R] (1 : Rₚ)))
        =
          Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n)
            ((Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S) (s ⊗ₜ[R] (1 : Rₚ))) := by
              simpa using
                (Ideal.quotientEquivAlg_mk
                  (I := (((map (algebraMap R Rₚ) 𝔭) ^ n).map
                    (tensorLocalizedBaseIncludeRight (R := R) (S := S) (𝔭 := 𝔭))))
                  (J := ((map (algebraMap S Sₚ) 𝔭S) ^ n))
                  (f := Localization.tensorLeftAlgEquiv (Ideal.primeCompl 𝔭) S)
                  (tensorLeftAlgEquiv_map_localized_prime_pow
                    (R := R) (S := S) (𝔭 := 𝔭) n).symm
                  (s ⊗ₜ[R] (1 : Rₚ)))
    _ = Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n) (algebraMap S Sₚ s) := by
          exact congrArg (Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))
            (Localization.tensorLeftAlgEquiv_apply_tmul_one
              (M := Ideal.primeCompl 𝔭) (S := S) s)

/-- Helper for Lemma 10.64.3: after transporting the tensor quotient to the semilocal quotient,
the source map `includeLeft : S → S ⊗[R] (Rₚ / 𝔭ₚ^n)` becomes the semilocal quotient map. -/
lemma tensorQuotientToSemilocalPowQuotientAlgEquiv_comp_includeLeft (n : ℕ) :
    ((tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n).toRingHom).comp
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
          S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) =
      (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
        (algebraMap S Sₚ)) := by
  -- Equality of ring maps is checked on the source ring `S`.
  ext s
  simpa using
    (tensorQuotientToSemilocalPowQuotientAlgEquiv_apply_includeLeft
      (R := R) (S := S) (𝔭 := 𝔭) n s)

/-- Helper for Lemma 10.64.3: flat base change turns the defining kernel of `𝔭^(n)` into the
kernel of the semilocal quotient map. -/
lemma map_symbolicPower_eq_ker_semilocal_pow_quotient (n : ℕ) :
    map (algebraMap R S) (𝔭.symbolicPower n) =
      RingHom.ker
        (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
          (algebraMap S Sₚ)) := by
  -- Rewrite the semilocal quotient map as the tensor quotient map followed by the explicit
  -- quotient equivalence constructed above.
  calc
    map (algebraMap R S) (𝔭.symbolicPower n)
        = RingHom.ker
            ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
              S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom) := by
            symm
            exact tensor_quotient_kernel_eq_map_symbolicPower (R := R) (S := S) (𝔭 := 𝔭) n
    _ = RingHom.ker
          (((tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n).toRingHom).comp
            ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
              S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)).toRingHom)) := by
            ext s
            constructor
            · intro hs
              change
                tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n
                  ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
                    S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) s) = 0
              simpa [hs]
            · intro hs
              change
                tensorQuotientToSemilocalPowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n
                  ((Algebra.TensorProduct.includeLeft : S →ₐ[R]
                    S ⊗[R] (Rₚ ⧸ (map (algebraMap R Rₚ) 𝔭) ^ n)) s) = 0 at hs
              exact (tensorQuotientToSemilocalPowQuotientAlgEquiv
                (R := R) (S := S) (𝔭 := 𝔭) n).injective <| by
                  simpa using hs
    _ = RingHom.ker
          (((Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n))).comp
            (algebraMap S Sₚ)) := by
            rw [tensorQuotientToSemilocalPowQuotientAlgEquiv_comp_includeLeft
              (R := R) (S := S) (𝔭 := 𝔭) n]

/-- Helper for Lemma 10.64.3: the iterated-localization equivalence is compatible with the
semilocal `Sₚ`-algebra structure. -/
noncomputable def semilocalLocalizationAtMapPrimeAlgEquiv_overSemilocalRing :
    Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S) ≃ₐ[Sₚ] S𝔮 where
  toRingEquiv := (semilocalLocalizationAtMapPrimeAlgEquiv (𝔭 := 𝔭)).toRingEquiv
  commutes' x := by
    -- The `Sₚ`-algebra structure is exactly the semilocal-to-local comparison map.
    have hcomp := DFunLike.congr_fun
      (semilocalLocalizationAtMapPrimeAlgEquiv_comp_algebraMap (𝔭 := 𝔭)) x
    simpa [semilocalToLocal_eq_algebraMap (R := R) (S := S) (𝔭 := 𝔭)] using hcomp

/-- Helper for Lemma 10.64.3: quotienting the iterated-localization equivalence identifies the
localized `n`th power quotient with the local power quotient. -/
noncomputable def semilocalLocalizationAtMapPrimePowQuotientAlgEquiv (n : ℕ) :
    (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S) ⧸
        map (algebraMap Sₚ (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S)))
          ((map (algebraMap S Sₚ) 𝔭S) ^ n)) ≃ₐ[Sₚ]
      (S𝔮 ⧸ (IsLocalRing.maximalIdeal S𝔮) ^ n) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  let e := semilocalLocalizationAtMapPrimeAlgEquiv_overSemilocalRing
    (R := R) (S := S) (𝔭 := 𝔭)
  -- First identify the image of the localized prime under the iterated-localization equivalence.
  have hmapJ :
      map e.toRingHom (map (algebraMap Sₚ (Localization.AtPrime J)) J) =
        IsLocalRing.maximalIdeal S𝔮 := by
    have hcomp :
        e.toRingHom.comp (algebraMap Sₚ (Localization.AtPrime J)) =
          semilocalToLocal (R := R) (S := S) (𝔭 := 𝔭) := by
      simpa [e, J] using
        (semilocalLocalizationAtMapPrimeAlgEquiv_comp_algebraMap
          (R := R) (S := S) (𝔭 := 𝔭))
    -- Compare the ideal after composing the algebra map with the existing semilocal-to-local map.
    calc
      map e.toRingHom (map (algebraMap Sₚ (Localization.AtPrime J)) J)
          = map (e.toRingHom.comp (algebraMap Sₚ (Localization.AtPrime J))) J := by
              rw [Ideal.map_map]
      _ = map (semilocalToLocal (R := R) (S := S) (𝔭 := 𝔭)) J := by
            rw [hcomp]
      _ = IsLocalRing.maximalIdeal S𝔮 := by
            simpa [J] using semilocalToLocal_map_map_prime (R := R) (S := S) (𝔭 := 𝔭)
  have hmapJpow :
      (IsLocalRing.maximalIdeal S𝔮) ^ n =
        map e.toRingHom
          (map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n)) := by
    -- Transport powers of the localized prime across the quotient equivalence.
    calc
      (IsLocalRing.maximalIdeal S𝔮) ^ n
          = (map e.toRingHom (map (algebraMap Sₚ (Localization.AtPrime J)) J)) ^ n := by
              rw [hmapJ]
      _ = map e.toRingHom
            ((map (algebraMap Sₚ (Localization.AtPrime J)) J) ^ n) := by
            rw [Ideal.map_pow]
      _ = map e.toRingHom
            (map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n)) := by
            simpa [Ideal.map_pow]
  -- Then quotient the equivalence by the identified image ideal.
  exact Ideal.quotientEquivAlg
    (map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n))
    ((IsLocalRing.maximalIdeal S𝔮) ^ n) e hmapJpow

/-- Helper for Lemma 10.64.3: the canonical map from the semilocal power quotient to the
iterated-local power quotient. -/
noncomputable def semilocalPowQuotientToIteratedLocalPowQuotient (n : ℕ) :
    Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n →+*
      Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S) ⧸
        map (algebraMap Sₚ (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S)))
          ((map (algebraMap S Sₚ) 𝔭S) ^ n) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  -- This is the quotient map induced by localizing `Sₚ` further at `J`.
  exact Ideal.quotientMap
    (map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n))
    (algebraMap Sₚ (Localization.AtPrime J))
    Ideal.le_comap_map

/-- Helper for Lemma 10.64.3: the public quotient comparison factors through the quotient of the
iterated-localization equivalence. -/
lemma semilocalLocalizationAtMapPrimePowQuotient_factorization (n : ℕ) :
    ((semilocalLocalizationAtMapPrimePowQuotientAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n).toRingHom).comp
        (semilocalPowQuotientToIteratedLocalPowQuotient
          (R := R) (S := S) (𝔭 := 𝔭) n) =
      semilocalPowQuotientToLocalPowQuotient (R := R) (S := S) (𝔭 := 𝔭) n := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  let T :=
    Localization.AtPrime J ⧸
      map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n)
  let _ : CommRing T := inferInstance
  -- Check the factorization on quotient representatives from `Sₚ`.
  ext y
  -- The quotient equivalence acts by the iterated-localization equivalence on representatives.
  simp [semilocalLocalizationAtMapPrimePowQuotientAlgEquiv,
    semilocalPowQuotientToIteratedLocalPowQuotient,
    semilocalPowQuotientToLocalPowQuotient,
    semilocalToLocal_eq_algebraMap, J, T]

/-- Helper for Lemma 10.64.3: Proposition 10.9.14 identifies the iterated-local power quotient
with the localization of the semilocal power quotient `Sₚ / J^n` at the image of `J.primeCompl`,
where `J = map (algebraMap S Sₚ) 𝔭S`. -/
noncomputable def semilocalPowQuotientLocalizationAlgEquiv (n : ℕ) :
    Localization
        (Algebra.algebraMapSubmonoid
          (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n)
          (Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S))) ≃ₐ[
        Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n]
      (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S) ⧸
        map (algebraMap Sₚ (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S)))
          ((map (algebraMap S Sₚ) 𝔭S) ^ n)) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  let T :=
    Localization.AtPrime J ⧸
      map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n)
  let _ : CommRing T := inferInstance
  let hAlg : Algebra (Sₚ ⧸ J ^ n) T := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Sₚ ⧸ J ^ n) T := hAlg
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid (Sₚ ⧸ J ^ n) (Ideal.primeCompl J))
        T := by
    infer_instance
  -- Proposition 10.9.14 is exactly the quotient-localization identification needed here.
  simpa [J, T] using
    (Localization.algEquiv
      (Algebra.algebraMapSubmonoid (Sₚ ⧸ J ^ n) (Ideal.primeCompl J))
      T)

/-- Helper for Lemma 10.64.3: on quotient representatives, the semilocal quotient-localization
equivalence sends the class of `x : Sₚ` to the class of its image in the iterated localization. -/
@[simp] lemma semilocalPowQuotientLocalizationAlgEquiv_apply_mk
    (n : ℕ) (x : Sₚ) :
    semilocalPowQuotientLocalizationAlgEquiv (R := R) (S := S) (𝔭 := 𝔭) n
      (algebraMap
        (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n)
        (Localization
          (Algebra.algebraMapSubmonoid
            (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n)
            (Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S))))
        (Ideal.Quotient.mk ((map (algebraMap S Sₚ) 𝔭S) ^ n) x)) =
      Ideal.Quotient.mk
        (map (algebraMap Sₚ (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S)))
          ((map (algebraMap S Sₚ) 𝔭S) ^ n))
        (algebraMap Sₚ (Localization.AtPrime (map (algebraMap S Sₚ) 𝔭S)) x) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  let T :=
    Localization.AtPrime J ⧸
      map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n)
  let _ : CommRing T := inferInstance
  let hAlg : Algebra (Sₚ ⧸ J ^ n) T := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Sₚ ⧸ J ^ n) T := hAlg
  let Mq := Algebra.algebraMapSubmonoid (Sₚ ⧸ J ^ n) (Ideal.primeCompl J)
  letI : IsLocalization Mq T := by
    infer_instance
  -- Rewrite the source generator as `x / 1` in the abstract localization and then evaluate the
  -- quotient-localization equivalence on that generator.
  change (Localization.algEquiv Mq T)
      (algebraMap (Sₚ ⧸ J ^ n) (Localization Mq) (Ideal.Quotient.mk (J ^ n) x)) =
    Ideal.Quotient.mk
      (map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n))
      (algebraMap Sₚ (Localization.AtPrime J) x)
  rw [← IsLocalization.mk'_one (M := Mq) (S := Localization Mq) (x := Ideal.Quotient.mk (J ^ n) x)]
  rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
  simpa [J, T] using
    (Ideal.Quotient.algebraMap_quotient_map_quotient
      (R := Sₚ)
      (S := Localization.AtPrime J)
      (p := J ^ n)
      x)

/-- Helper for Lemma 10.64.3: the canonical semilocal-to-iterated-local quotient map factors as
the algebra map into the localization of `Sₚ / J^n`, followed by the quotient-localization
equivalence above. -/
lemma semilocalPowQuotientToIteratedLocalPowQuotient_factorization_via_localization (n : ℕ) :
    semilocalPowQuotientToIteratedLocalPowQuotient (R := R) (S := S) (𝔭 := 𝔭) n =
      ((semilocalPowQuotientLocalizationAlgEquiv
        (R := R) (S := S) (𝔭 := 𝔭) n).toRingHom).comp
        (algebraMap
          (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n)
          (Localization
            (Algebra.algebraMapSubmonoid
              (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n)
              (Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S))))) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  let T :=
    Localization.AtPrime J ⧸
      map (algebraMap Sₚ (Localization.AtPrime J)) (J ^ n)
  let _ : CommRing T := inferInstance
  -- Compare the two maps on quotient representatives coming from `Sₚ`.
  ext y
  simp [semilocalPowQuotientToIteratedLocalPowQuotient,
    semilocalPowQuotientLocalizationAlgEquiv_apply_mk, J, T]

/-- Helper for Lemma 10.64.3: over a domain, any nonzero scalar acts regularly on a finitely
supported family of copies of that domain. -/
lemma isSMulRegular_finsupp_of_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} {g : A} (hg : g ≠ 0) :
    IsSMulRegular (ι →₀ A) g := by
  -- Check regularity coordinatewise, where cancellation reduces to the domain structure on `A`.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro f hf
  ext i
  have hcoord := congrArg (fun h : ι →₀ A => h i) hf
  simp only [Finsupp.smul_apply, smul_eq_mul] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left hg

/-- Helper for Lemma 10.64.3: over a domain, any nonzero scalar acts regularly on the tensor of
that domain with a vector space over the base field. -/
lemma isSMulRegular_tensor_vectorSpace_of_ne_zero
    {κ : Type*} [Field κ]
    {A : Type*} [CommRing A] [Algebra κ A] [IsDomain A]
    {V : Type*} [AddCommGroup V] [Module κ V]
    {g : A} (hg : g ≠ 0) :
    IsSMulRegular (A ⊗[κ] V) g := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex κ V) κ V :=
    Module.Basis.ofVectorSpace κ V
  let e :
      A ⊗[κ] V ≃ₗ[A] (Module.Basis.ofVectorSpaceIndex κ V →₀ A) :=
    Algebra.TensorProduct.equivFinsuppOfBasis (R := κ) (A := A) (V := V) b
  have hregular_finsupp :
      IsSMulRegular (Module.Basis.ofVectorSpaceIndex κ V →₀ A) g :=
    isSMulRegular_finsupp_of_ne_zero
      (A := A) (ι := Module.Basis.ofVectorSpaceIndex κ V) hg
  -- Transport the coordinatewise regularity back through the tensor/finsupp linear equivalence.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  apply e.injective
  have hz' : g • e z = 0 := by
    simpa using congrArg e hz
  exact hregular_finsupp.right_eq_zero_of_smul hz'

/-- Helper for Lemma 10.64.3: each denominator outside the semilocalized prime already acts
regularly on the first quotient `Sₚ / J`, where `J = map (algebraMap S Sₚ) 𝔭S`. -/
lemma semilocal_denominator_class_ne_zero
    (c : Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S)) :
    Ideal.Quotient.mk (map (algebraMap S Sₚ) 𝔭S) (c : Sₚ) ≠ 0 := by
  -- The quotient class is zero exactly when the denominator lies in the prime, which is excluded
  -- by the defining property of `primeCompl`.
  intro hc
  exact c.2 <| by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hc

/-- Helper for Lemma 10.64.3: each denominator outside the semilocalized prime already acts
regularly on the first quotient `Sₚ / J`, where `J = map (algebraMap S Sₚ) 𝔭S`. -/
lemma semilocal_denominator_isSMulRegular_prime_quotient
    (c : Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S)) :
    IsSMulRegular (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) (c : Sₚ) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  have hc :
      algebraMap Sₚ (Sₚ ⧸ J) c ∈ nonZeroDivisors (Sₚ ⧸ J) := by
    -- The quotient class of `c` is literally the image of an element of `J.primeCompl`.
    have hc_map :
        algebraMap Sₚ (Sₚ ⧸ J) c ∈
          Algebra.algebraMapSubmonoid (Sₚ ⧸ J) (Ideal.primeCompl J) := by
      change algebraMap Sₚ (Sₚ ⧸ J) c ∈ Submonoid.map (algebraMap Sₚ (Sₚ ⧸ J))
        (Ideal.primeCompl J)
      exact ⟨c, c.2, rfl⟩
    exact semilocal_denominator_nonZeroDivisors_prime_quotient
      (R := R) (S := S) (𝔭 := 𝔭) hc_map
  -- Read the quotient-ring nonzerodivisor statement as injectivity of multiplication by `c`.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
  have hx' : algebraMap Sₚ (Sₚ ⧸ J) c * x = 0 := by
    change algebraMap Sₚ (Sₚ ⧸ J) c * x = 0 at hx
    exact hx
  exact (mem_nonZeroDivisors_iff_left.mp hc) x hx'

/-- Helper for Lemma 10.64.3: the literal next-power submodule inside `I ^ m` is the ideal-smul
submodule `I • ⊤`. -/
lemma pow_succ_submoduleOf_eq_ideal_smul_top
    {A : Type*} [CommRing A] (I : Ideal A) (m : ℕ) :
    ((I ^ (m + 1) : Ideal A).submoduleOf (I ^ m)) =
      I • (⊤ : Submodule A (I ^ m : Ideal A)) := by
  -- Rewrite `I ^ (m + 1)` as `I * I ^ m`, then use the standard membership test for `I • ⊤`.
  ext x
  simp [Submodule.submoduleOf, Submodule.mem_smul_top_iff, pow_succ']

/-- Helper for Lemma 10.64.3: the semilocal prime quotient inherits the expected algebra
structure over the localized residue ring `Rₚ / 𝔭Rₚ`. -/
noncomputable local instance semilocal_prime_quotient_residue_algebra :
    Algebra (Rₚ ⧸ map (algebraMap R Rₚ) 𝔭)
      (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) := by
  let J₀ : Ideal Rₚ := map (algebraMap R Rₚ) 𝔭
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  have hle : J₀ ≤ Ideal.comap (algebraMap Rₚ Sₚ) J := by
    exact Ideal.map_le_iff_le_comap.mp <|
      le_of_eq (localized_prime_map_eq_semilocalized_prime
        (R := R) (S := S) (𝔭 := 𝔭))
  exact Ideal.Quotient.algebraQuotientOfLEComap hle

/-- Helper for Lemma 10.64.3: after applying the right tensor-unit equivalence
`Sₚ ⊗[Rₚ] Rₚ ≃ Sₚ`, the base change of the localized prime power becomes the corresponding
semilocal prime power. -/
lemma semilocal_power_ideal_baseChange_map_eq
    (m : ℕ) :
    Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
      (((map (algebraMap R Rₚ) 𝔭) ^ m : Ideal Rₚ).baseChange Sₚ) =
        ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) := by
  let J₀m : Ideal Rₚ := (map (algebraMap R Rₚ) 𝔭) ^ m
  calc
    Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
        (J₀m.baseChange Sₚ)
        =
          Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
            (Submodule.span Sₚ (⇑(TensorProduct.mk Rₚ Sₚ Rₚ 1) '' ↑J₀m)) := by
              rw [Submodule.baseChange_eq_span, Submodule.map_coe]
    _ = Submodule.span Sₚ (((J₀m : Set Rₚ).image (algebraMap Rₚ Sₚ))) := by
          -- Proof comment: `rid` sends the generator `1 ⊗ x` to the localization image of `x`.
          rw [Submodule.map_span]
          congr 1
          ext x
          constructor <;> intro hx
          · rcases hx with ⟨y, hy, rfl⟩
            rcases hy with ⟨z, hz, rfl⟩
            refine ⟨z, hz, ?_⟩
            simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
          · rcases hx with ⟨y, hy, rfl⟩
            refine ⟨1 ⊗ₜ[Rₚ] y, ?_, ?_⟩
            · exact ⟨y, hy, rfl⟩
            · simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
    _ = map (algebraMap Rₚ Sₚ) J₀m := by
          rw [Ideal.map, Ideal.submodule_span_eq]
    _ = ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) := by
          rw [Ideal.map_pow, localized_prime_map_eq_semilocalized_prime]

/-- Helper for Lemma 10.64.3: the semilocal power ideal is the flat base change of the localized
base prime power. -/
noncomputable def semilocal_power_ideal_baseChange_linearEquiv
    (m : ℕ) :
    Sₚ ⊗[Rₚ] ((map (algebraMap R Rₚ) 𝔭) ^ m : Ideal Rₚ) ≃ₗ[Sₚ]
      ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) := by
  let _ : Module.Flat Rₚ Sₚ :=
    (Module.flat_iff_of_isLocalization
      (R := R) (S := Rₚ) (p := Ideal.primeCompl 𝔭) (M := Sₚ)).mpr inferInstance
  let J₀m : Ideal Rₚ := (map (algebraMap R Rₚ) 𝔭) ^ m
  let e₁ :
      Sₚ ⊗[Rₚ] J₀m ≃ₗ[Sₚ] J₀m.baseChange Sₚ :=
    Submodule.toBaseChange.toLinearEquiv Sₚ J₀m
  let e₂ :
      J₀m.baseChange Sₚ ≃ₗ[Sₚ]
        Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
          (J₀m.baseChange Sₚ) :=
    J₀m.baseChange Sₚ |>.equivMapOfInjective
      (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
      (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).injective
  let e₃ :
      Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
          (J₀m.baseChange Sₚ) ≃ₗ[Sₚ]
        ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) :=
    LinearEquiv.ofEq _ _ <| by
      simpa [J₀m] using
        semilocal_power_ideal_baseChange_map_eq (R := R) (S := S) (𝔭 := 𝔭) m
  -- Proof comment: first identify the tensor with the literal base-change submodule, then push
  -- that submodule across the tensor-unit map to the semilocal power ideal.
  exact e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 10.64.3: the tensor-side denominator `J₀Sₚ • ⊤` appearing in the localized
power-layer comparison. -/
noncomputable def semilocal_power_ideal_baseChange_sourceDenominator (m : ℕ) :
    Submodule Sₚ (Sₚ ⊗[Rₚ] ((map (algebraMap R Rₚ) 𝔭) ^ m : Ideal Rₚ)) :=
  -- TODO: identify the source denominator as the image-ideal smul-top submodule
  -- appearing in `TensorProduct.tensorQuotMapSMulEquivTensorQuot`.
  sorry

/-- Helper for Lemma 10.64.3: the semilocal power-ideal denominator `JSₚ • ⊤` after transporting
across the tensor-unit equivalence. -/
noncomputable def semilocal_power_ideal_baseChange_targetDenominator (m : ℕ) :
    Submodule Sₚ (((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ)) :=
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  J • (⊤ : Submodule Sₚ (J ^ m : Ideal Sₚ))

/-- Helper for Lemma 10.64.3: the raw base-change equivalence carries the tensor-side denominator
`J₀Sₚ • ⊤` to the literal denominator `JSₚ • ⊤` on the semilocal power ideal. -/
lemma semilocal_power_ideal_baseChange_smul_top
    (m : ℕ) :
    Submodule.map
        (semilocal_power_ideal_baseChange_linearEquiv
          (R := R) (S := S) (𝔭 := 𝔭) m).toLinearMap
        (semilocal_power_ideal_baseChange_sourceDenominator
        (R := R) (S := S) (𝔭 := 𝔭) m) =
      semilocal_power_ideal_baseChange_targetDenominator
        (R := R) (S := S) (𝔭 := 𝔭) m := by
  -- TODO: once the source denominator is expressed as `map (algebraMap Rₚ Sₚ) J₀ • ⊤`,
  -- this follows from `Submodule.map_smul''`, `Submodule.map_top`, and
  -- `localized_prime_map_eq_semilocalized_prime`.
  sorry

/-- Helper for Lemma 10.64.3: the graded layer `J^m / J^(m + 1)` is the flat base change of the
corresponding layer for the localized base prime. -/
noncomputable def semilocal_power_layer_baseChange_equiv
    (m : ℕ) :
    ((((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ)) ⧸
        (((map (algebraMap S Sₚ) 𝔭S) ^ (m + 1) : Ideal Sₚ).submoduleOf
          (((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ)))) ≃ₗ[Sₚ]
      Sₚ ⊗[Rₚ]
        (((map (algebraMap R Rₚ) 𝔭) ^ m : Ideal Rₚ) ⧸
          ((map (algebraMap R Rₚ) 𝔭) •
            (⊤ : Submodule Rₚ ((map (algebraMap R Rₚ) 𝔭) ^ m : Ideal Rₚ)))) := by
  -- TODO: rewrite `J^(m + 1)` as `J • ⊤`, quotient
  -- `semilocal_power_ideal_baseChange_linearEquiv`, and finish with
  -- `TensorProduct.tensorQuotMapSMulEquivTensorQuot`.
  sorry

/-- Helper for Lemma 10.64.3: the localized power layer quotient is already annihilated by the
localized prime ideal, so it is naturally a module over the residue field `Rₚ / J₀`. -/
lemma pow_layer_ideal_smul_top_eq_bot
    (m : ℕ) :
    let J₀ : Ideal Rₚ := map (algebraMap R Rₚ) 𝔭
    let V :=
      (((J₀ ^ m : Ideal Rₚ) ⧸
        (J₀ • (⊤ : Submodule Rₚ (J₀ ^ m : Ideal Rₚ)))))
    J₀ • (⊤ : Submodule Rₚ V) = ⊥ := by
  let J₀ : Ideal Rₚ := map (algebraMap R Rₚ) 𝔭
  let V :=
    (((J₀ ^ m : Ideal Rₚ) ⧸
      (J₀ • (⊤ : Submodule Rₚ (J₀ ^ m : Ideal Rₚ)))))
  -- Proof comment: every scalar from `J₀` maps to zero in `Rₚ / J₀`, so it acts trivially on the
  -- quotient layer, which collapses the whole `J₀ • ⊤` submodule.
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
  intro r hr
  exact Module.mem_annihilator.mpr fun x ↦ by
    rw [← algebraMap_smul (A := Rₚ ⧸ J₀) r x]
    simp [J₀, Ideal.Quotient.eq_zero_iff_mem.mpr hr]

/-- Helper for Lemma 10.64.3: each graded piece `J^m / J^(m + 1)` is a tensor module over the
semilocal prime quotient, so denominators outside `J` act regularly on it. -/
lemma semilocal_denominator_layer_isSMulRegular_via_tensor_layer
    (m : ℕ) (c : Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S)) :
    IsSMulRegular
      ((((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ)) ⧸
        (((map (algebraMap S Sₚ) 𝔭S) ^ (m + 1) : Ideal Sₚ).submoduleOf
          (((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ))))
      (c : Sₚ) := by
  -- TODO: transport the layer through `semilocal_power_layer_baseChange_equiv`, then rewrite the
  -- tensor model over the residue field and apply regularity of the denominator class on the
  -- semilocal prime quotient.
  sorry

/-- Helper for Lemma 10.64.3: regularity on `Sₚ / J^m` and on the next graded layer propagates to
regularity on `Sₚ / J^(m + 1)`. -/
lemma semilocal_denominator_isSMulRegular_pow_quotient_succ
    (m : ℕ) (c : Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S))
    (hprev :
      IsSMulRegular (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ m) (c : Sₚ))
    (hlayer :
      IsSMulRegular
        ((((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ)) ⧸
          (((map (algebraMap S Sₚ) 𝔭S) ^ (m + 1) : Ideal Sₚ).submoduleOf
            (((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ))))
        (c : Sₚ)) :
    IsSMulRegular (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ (m + 1)) (c : Sₚ) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  -- Route correction: use the quotient membership criterion directly instead of repackaging the
  -- layer sequence as a separate short exact object.
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro x hx
  have hx_mem_pow :
      x ∈ J ^ m := by
    -- First descend one step in the filtration using regularity on the previous quotient.
    have hsmul_mem_pow : (c : Sₚ) • x ∈ (J ^ m : Ideal Sₚ) := by
      exact (Ideal.pow_le_pow_right (Nat.le_succ m)) hx
    exact (isSMulRegular_quotient_iff_mem_of_smul_mem (J ^ m) (c : Sₚ)).mp
      hprev x <| by
        simpa [smul_eq_mul, J] using hsmul_mem_pow
  let x' : (J ^ m : Ideal Sₚ) := ⟨x, hx_mem_pow⟩
  have hsmul_mem_layer :
      (c : Sₚ) • x' ∈ ((J ^ (m + 1)).submoduleOf (J ^ m)) := by
    -- The hypothesis already says the scalar multiple lands in the next power.
    change ((c : Sₚ) * x) ∈ J ^ (m + 1)
    simpa [smul_eq_mul, J] using hx
  have hx_mem_layer :
      x' ∈ ((J ^ (m + 1)).submoduleOf (J ^ m)) := by
    -- Then kill the class of `x` in the layer quotient.
    exact (isSMulRegular_quotient_iff_mem_of_smul_mem
      ((J ^ (m + 1)).submoduleOf (J ^ m)) (c : Sₚ)).mp
        hlayer x' hsmul_mem_layer
  -- Membership in the `submoduleOf` is exactly membership in the ambient next power.
  simpa [Submodule.submoduleOf, J] using hx_mem_layer

/-- Helper for Lemma 10.64.3: every denominator outside the semilocalized prime acts regularly on
the positive semilocal power quotients `Sₚ / J^n`, where `J = map (algebraMap S Sₚ) 𝔭S`. -/
lemma semilocal_denominator_isSMulRegular_pow_quotient
    {n : ℕ} (hn : 0 < n) :
    ∀ c : Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S),
      IsSMulRegular (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n) (c : Sₚ) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  intro c
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hpow :
      ∀ k : ℕ, ∀ d : Ideal.primeCompl J, IsSMulRegular (Sₚ ⧸ J ^ (k + 1)) (d : Sₚ) := by
    intro k
    induction k with
    | zero =>
        intro d
        -- The base case is the prime quotient, where every denominator class is already regular.
        exact ((Submodule.quotEquivOfEq (J ^ (0 + 1)) J (by simp [pow_one])).isSMulRegular_congr
          (d : Sₚ)).mpr <|
          semilocal_denominator_isSMulRegular_prime_quotient
            (R := R) (S := S) (𝔭 := 𝔭) d
    | succ k ih =>
        intro d
        -- Once the previous quotient and the next graded layer are regular, the quotient
        -- criterion upgrades regularity to the next power quotient.
        exact semilocal_denominator_isSMulRegular_pow_quotient_succ
          (R := R) (S := S) (𝔭 := 𝔭) (m := k + 1) d (ih d)
          (semilocal_denominator_layer_isSMulRegular_via_tensor_layer
            (R := R) (S := S) (𝔭 := 𝔭) (m := k + 1) d)
  exact hpow m c

/-- Helper for Lemma 10.64.3: every denominator inverted in the iterated localization is already a
nonzerodivisor on the positive semilocal power quotient `Sₚ / J^n`. -/
lemma semilocal_denominator_nonZeroDivisors_pow_quotient
    {n : ℕ} (hn : 0 < n) :
    Algebra.algebraMapSubmonoid
        (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n)
        (Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S)) ≤
      nonZeroDivisors (Sₚ ⧸ (map (algebraMap S Sₚ) 𝔭S) ^ n) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  intro y hy
  rcases (show ∃ c : Ideal.primeCompl J, algebraMap Sₚ (Sₚ ⧸ J ^ n) c = y by
      simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map, J] using hy) with ⟨c, rfl⟩
  -- Read quotient regularity as left-cancellation for multiplication by the quotient class of `c`.
  refine mem_nonZeroDivisors_iff_left.mpr ?_
  intro x hx
  have hx' : (c : Sₚ) • x = 0 := by
    rw [Algebra.smul_def]
    exact hx
  exact (semilocal_denominator_isSMulRegular_pow_quotient
    (R := R) (S := S) (𝔭 := 𝔭) hn c).right_eq_zero_of_smul hx'

/-- Helper for Lemma 10.64.3: once denominators are regular on the semilocal power quotient, the
public comparison `Sₚ / J^n → S𝔮 / maximalIdeal(S𝔮)^n` is injective. -/
lemma semilocalPowQuotientToLocalPowQuotient_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective
      (semilocalPowQuotientToLocalPowQuotient (R := R) (S := S) (𝔭 := 𝔭) n) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  -- Route correction: the public quotient map now factors through the quotient of the explicit
  -- iterated-localization equivalence, so only the injectivity of the canonical localization
  -- quotient map remains.
  rw [← semilocalLocalizationAtMapPrimePowQuotient_factorization
    (R := R) (S := S) (𝔭 := 𝔭) n]
  refine (semilocalLocalizationAtMapPrimePowQuotientAlgEquiv
    (R := R) (S := S) (𝔭 := 𝔭) n).injective.comp ?_
  rw [semilocalPowQuotientToIteratedLocalPowQuotient_factorization_via_localization
    (R := R) (S := S) (𝔭 := 𝔭) n]
  refine (semilocalPowQuotientLocalizationAlgEquiv
    (R := R) (S := S) (𝔭 := 𝔭) n).injective.comp ?_
  -- Route correction: the remaining input is exactly the source-proof regularity statement saying
  -- denominators outside `J` are nonzerodivisors on `Sₚ / J^n`.
  exact IsLocalization.injective
    (M := Algebra.algebraMapSubmonoid
      (Sₚ ⧸ J ^ n)
      (Ideal.primeCompl J))
    (S := Localization
      (Algebra.algebraMapSubmonoid
        (Sₚ ⧸ J ^ n)
        (Ideal.primeCompl J)))
    (semilocal_denominator_nonZeroDivisors_pow_quotient
      (R := R) (S := S) (𝔭 := 𝔭) hn)

/-- Helper for Lemma 10.64.3: once the semilocal-to-local quotient comparison is injective, the
reverse inclusion reduces to the two kernel descriptions already isolated above. -/
lemma symbolicPower_map_le_map_symbolicPower_of_semilocal_comparison_injective
    (n : ℕ)
    (hinj :
      Function.Injective
        (semilocalPowQuotientToLocalPowQuotient (R := R) (S := S) (𝔭 := 𝔭) n)) :
    symbolicPower 𝔭S n ≤ map (algebraMap R S) (𝔭.symbolicPower n) := by
  -- Rewrite the target symbolic power as the local quotient kernel.
  rw [symbolicPower_map_eq_ker_local_pow_quotient (𝔭 := 𝔭) n]
  -- Then descend that kernel across the injective semilocal-to-local comparison.
  rw [ker_local_pow_quotient_eq_ker_semilocal_pow_quotient_of_injective
    (𝔭 := 𝔭) n hinj]
  -- The remaining semilocal kernel is the flat base change of the defining kernel of `𝔭^(n)`.
  rw [← map_symbolicPower_eq_ker_semilocal_pow_quotient (𝔭 := 𝔭) n]

/-- Helper for Lemma 10.64.3: the first symbolic power of a prime ideal is the prime ideal
itself. -/
lemma symbolicPower_one_eq_self : symbolicPower 𝔭 1 = 𝔭 := by
  -- Contracting the localized prime back to the original ring recovers the prime.
  simpa [Ideal.symbolicPower, pow_one] using
    (IsLocalization.comap_map_of_isPrime_disjoint (Ideal.primeCompl 𝔭) Rₚ
      (show 𝔭.IsPrime from inferInstance) <| by
        rw [Set.disjoint_left]
        intro x hxcompl hxmem
        exact hxcompl hxmem)

/-- Helper for Lemma 10.64.3: the first symbolic power of the extended prime `𝔭S` is `𝔭S`
itself. -/
lemma symbolicPower_map_one_eq_self : symbolicPower 𝔭S 1 = 𝔭S := by
  -- The same contraction argument applies after passing to the prime `𝔭S` of `S`.
  simpa [Ideal.symbolicPower, pow_one] using
    (IsLocalization.comap_map_of_isPrime_disjoint (Ideal.primeCompl 𝔭S) S𝔮
      (show (𝔭.map (algebraMap R S)).IsPrime from inferInstance) <| by
        rw [Set.disjoint_left]
        intro x hxcompl hxmem
        exact hxcompl hxmem)

/-- Helper for Lemma 10.64.3: after localizing at `𝔭S`, the symbolic power of `𝔭S` becomes the
ordinary power of the maximal ideal. -/
lemma symbolicPower_map_localized_eq_pow_maximalIdeal (n : ℕ) :
    map (algebraMap S S𝔮) (symbolicPower 𝔭S n) = IsLocalRing.maximalIdeal S𝔮 ^ n := by
  -- This is the defining contraction formula for symbolic powers, pushed to the local ring.
  simpa [Ideal.symbolicPower, Localization.AtPrime.map_eq_maximalIdeal] using
    (IsLocalization.map_comap (Ideal.primeCompl 𝔭S) S𝔮
      ((map (algebraMap S S𝔮) 𝔭S) ^ n))

/-- Helper for Lemma 10.64.3: after localizing at `𝔭S`, the extension of `𝔭^(n)` becomes the
same `n`th power of the maximal ideal. -/
lemma map_symbolicPower_localized_eq_pow_maximalIdeal (n : ℕ) :
    map (algebraMap S S𝔮) (map (algebraMap R S) (𝔭.symbolicPower n)) =
      IsLocalRing.maximalIdeal S𝔮 ^ n := by
  let h𝔮 : Ideal.LiesOver 𝔭S 𝔭 := map_prime_lies_over_of_flat (𝔭 := 𝔭)
  let f : Rₚ →+* S𝔮 := Localization.localRingHom 𝔭 𝔭S (algebraMap R S) h𝔮.over
  have hcomp : f.comp (algebraMap R Rₚ) = algebraMap R S𝔮 := by
    ext x
    exact Localization.localRingHom_to_map 𝔭 𝔭S (algebraMap R S) h𝔮.over x
  have hsource : map (algebraMap R Rₚ) (𝔭.symbolicPower n) = IsLocalRing.maximalIdeal Rₚ ^ n := by
    -- Localizing the defining contraction of `𝔭^(n)` recovers the ordinary power in `R_𝔭`.
    simpa [Ideal.symbolicPower, Localization.AtPrime.map_eq_maximalIdeal] using
      (IsLocalization.map_comap (Ideal.primeCompl 𝔭) Rₚ
        ((map (algebraMap R Rₚ) 𝔭) ^ n))
  have hmax : map f (IsLocalRing.maximalIdeal Rₚ) = IsLocalRing.maximalIdeal S𝔮 := by
    -- The local-ring map sends the maximal ideal of `R_𝔭` to the maximal ideal of `S_𝔮`.
    calc
      map f (IsLocalRing.maximalIdeal Rₚ)
          = map (algebraMap R S𝔮) 𝔭 := by
              rw [← Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭), Ideal.map_map, hcomp]
      _ = map (algebraMap S S𝔮) 𝔭S := by
            rw [IsScalarTower.algebraMap_eq R S S𝔮, Ideal.map_map]
      _ = IsLocalRing.maximalIdeal S𝔮 := by
            simpa using (Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭S))
  calc
    map (algebraMap S S𝔮) (map (algebraMap R S) (𝔭.symbolicPower n))
        = map (algebraMap R S𝔮) (𝔭.symbolicPower n) := by
            rw [IsScalarTower.algebraMap_eq R S S𝔮, Ideal.map_map]
    _ = map f (map (algebraMap R Rₚ) (𝔭.symbolicPower n)) := by
          rw [← hcomp, Ideal.map_map]
    _ = map f (IsLocalRing.maximalIdeal Rₚ ^ n) := by rw [hsource]
    _ = (map f (IsLocalRing.maximalIdeal Rₚ)) ^ n := by rw [Ideal.map_pow]
    _ = IsLocalRing.maximalIdeal S𝔮 ^ n := by rw [hmax]

/-- Helper for Lemma 10.64.3: in a local ring, the symbolic powers of the maximal ideal agree
with its ordinary powers. -/
lemma symbolicPower_maximalIdeal_eq_pow_of_local
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    symbolicPower (IsLocalRing.maximalIdeal A) n = IsLocalRing.maximalIdeal A ^ n := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  letI : m.IsPrime := by
    simpa [m] using (show (IsLocalRing.maximalIdeal A).IsPrime from inferInstance)
  let e : Localization.AtPrime m ≃ₐ[A] A := by
    have h_units : m.primeCompl ≤ IsUnit.submonoid A := by
      intro x hx
      -- Outside the maximal ideal, a local-ring element is a unit.
      simpa [m, Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hx
    letI : IsLocalization m.primeCompl A := IsLocalization.self h_units
    exact IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m) A
  have hsymm : e.symm.toRingHom = algebraMap A (Localization.AtPrime m) := by
    ext x
    simpa [m] using (AlgEquiv.commutes e.symm x)
  have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id A := by
    -- The algebra equivalence is inverse to its symmetry on the nose.
    ext x
    exact e.apply_symm_apply x
  have hmap_pow : map e.symm.toRingHom (m ^ n) = comap e.toRingHom (m ^ n) := by
    simpa using (Ideal.map_comap_of_equiv (I := m ^ n) e.symm.toRingEquiv)
  -- Transport the defining symbolic-power ideal through the self-localization equivalence.
  calc
    symbolicPower m n
        = comap (algebraMap A (Localization.AtPrime m))
            (map (algebraMap A (Localization.AtPrime m)) (m ^ n)) := by
              simp [Ideal.symbolicPower, Ideal.map_pow]
    _ = comap e.symm.toRingHom (map e.symm.toRingHom (m ^ n)) := by
          rw [hsymm]
    _ = comap e.symm.toRingHom (comap e.toRingHom (m ^ n)) := by
          rw [hmap_pow]
    _ = comap (e.toRingHom.comp e.symm.toRingHom) (m ^ n) := by
          rw [Ideal.comap_comap]
    _ = m ^ n := by
          rw [hcomp]
          rfl

/-- Helper for Lemma 10.64.3: the `n`th ordinary power of the extended prime is contained in the
extension of the `n`th symbolic power. -/
lemma map_prime_pow_le_map_symbolicPower (n : ℕ) :
    𝔭S ^ n ≤ map (algebraMap R S) (𝔭.symbolicPower n) := by
  -- First compare the ordinary power with the symbolic power in `R`, then extend to `S`.
  calc
    𝔭S ^ n = map (algebraMap R S) (𝔭 ^ n) := by
      rw [Ideal.map_pow]
    _ ≤ map (algebraMap R S) (𝔭.symbolicPower n) := by
      exact Ideal.map_mono <| by
        -- The symbolic power is the contraction of `(𝔭Rₚ)^n`, so it contains `𝔭^n`.
        simpa [Ideal.symbolicPower, Ideal.map_pow] using
          (Ideal.le_comap_map : 𝔭 ^ n ≤ comap (algebraMap R Rₚ) (map (algebraMap R Rₚ) (𝔭 ^ n)))

/-- Helper for Lemma 10.64.3: for positive `n`, the extended symbolic power `𝔭^(n)S` is
contained in the symbolic power of the extended prime `𝔭S`. -/
lemma map_symbolicPower_le_symbolicPower_map {n : ℕ} (hn : 0 < n) :
    map (algebraMap R S) (𝔭.symbolicPower n) ≤ symbolicPower 𝔭S n := by
  have hloc :
      map (algebraMap S S𝔮) (map (algebraMap R S) (𝔭.symbolicPower n)) =
        map (algebraMap S S𝔮) (symbolicPower 𝔭S n) := by
    -- Both ideals become the same maximal-ideal power after localizing at `𝔭S`.
    rw [map_symbolicPower_localized_eq_pow_maximalIdeal (𝔭 := 𝔭),
      symbolicPower_map_localized_eq_pow_maximalIdeal (𝔭 := 𝔭)]
  have hdisj : Disjoint ((Ideal.primeCompl 𝔭S) : Set S) (symbolicPower 𝔭S n) := by
    -- A positive symbolic power is contained in its prime radical, so it misses `𝔭S.primeCompl`.
    rw [Set.disjoint_left]
    intro x hxcompl hxmem
    have hxrad : x ∈ radical (symbolicPower 𝔭S n) := Ideal.le_radical hxmem
    have hxprime : x ∈ 𝔭S := by
      simpa [Ideal.radical_symbolicPower (𝔭 := 𝔭S) hn] using hxrad
    exact hxcompl hxprime
  have hcomap :
      comap (algebraMap S S𝔮) (map (algebraMap S S𝔮) (symbolicPower 𝔭S n)) =
        symbolicPower 𝔭S n := by
    -- The right-hand symbolic power is `𝔭S`-primary, so localization away from `𝔭S` does not
    -- change its contraction back to `S`.
    simpa using
      (IsLocalization.comap_map_of_isPrimary_disjoint (Ideal.primeCompl 𝔭S) S𝔮
        (Ideal.symbolicPower_isPrimary (𝔭 := 𝔭S) hn) hdisj)
  rw [← hcomap]
  exact (Ideal.map_le_iff_le_comap).mp (le_of_eq hloc)

/-- Lemma 10.64.3: for a flat ring map `R → S`, if the extension `𝔭S` of a prime ideal `𝔭 ⊂ R`
is prime in `S`, then extending the `n`th symbolic power of `𝔭` to `S` gives the `n`th symbolic
power of `𝔭S`. -/
theorem map_symbolicPower_eq_symbolicPower_map (n : ℕ)
    : map (algebraMap R S) (𝔭.symbolicPower n) = symbolicPower 𝔭S n := by
  by_cases hn : n = 0
  · -- At level `0`, both symbolic powers are the unit ideal by definition.
    subst hn
    calc
      map (algebraMap R S) (𝔭.symbolicPower 0) = map (algebraMap R S) ⊤ := by
        simp [Ideal.symbolicPower]
      _ = ⊤ := by simpa using (Ideal.map_top (f := algebraMap R S))
      _ = symbolicPower 𝔭S 0 := by
        simp [Ideal.symbolicPower]
  · by_cases h1 : n = 1
    · -- At level `1`, symbolic powers are just the prime ideals themselves.
      subst h1
      rw [symbolicPower_one_eq_self (𝔭 := 𝔭),
        symbolicPower_map_one_eq_self (R := R) (S := S) (𝔭 := 𝔭)]
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      apply le_antisymm
      · -- The easy direction already descends from localization because the right-hand side is
        -- primary away from `𝔭S`.
        exact map_symbolicPower_le_symbolicPower_map (𝔭 := 𝔭) hn'
      · -- Route correction: the remaining direction is the source-proof injectivity step for
        -- `S / 𝔭^(n)S → S_𝔮 / 𝔭^n S_𝔮`, now factored through the explicit semilocal comparison
        -- `Sₚ ⧸ J^n → S𝔮 ⧸ maximalIdeal(S𝔮)^n`.
        have hinj :
            Function.Injective
              (semilocalPowQuotientToLocalPowQuotient (R := R) (S := S) (𝔭 := 𝔭) n) := by
          -- The localization packaging is now explicit; the only remaining source-faithful input
          -- is regularity of denominators on the semilocal power quotient.
          exact semilocalPowQuotientToLocalPowQuotient_injective
            (R := R) (S := S) (𝔭 := 𝔭) hn'
        exact symbolicPower_map_le_map_symbolicPower_of_semilocal_comparison_injective
          (𝔭 := 𝔭) n hinj

end Ideal

end
