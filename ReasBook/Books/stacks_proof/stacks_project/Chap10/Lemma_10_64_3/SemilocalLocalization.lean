import stacks_proof.stacks_project.Chap10.Lemma_10_64_3.SemilocalPrime

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

attribute [local instance] semilocal_map_prime_isPrime
attribute [local instance] semilocalToLocalAlgebra

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


end Ideal

end
