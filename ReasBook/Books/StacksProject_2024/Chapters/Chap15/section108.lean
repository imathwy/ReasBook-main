import Mathlib
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Flat

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_108_1 (from Chap15) -/
universe u v

open PrimeSpectrum

/- Domain triage:
* primary domain: commutative algebra on fibers of `Spec B → Spec A`;
* sampled owner abstractions: `Algebra.Etale`, `Algebra.Unramified`,
  `Algebra.QuasiFinite`, `Algebra.IsIntegral`, the quasi-finite fiber theorem
  `Algebra.QuasiFinite.eq_of_le_of_under_eq`, `Ideal.primesOver`, and the Chapter 10 bridge
  `ringHom_injective_tfae_of_image_contains_dense_set`;
* source-facing layer: the theorem `ideal_comap_ne_bot_of_cases`, whose hypothesis is the direct
  seven-way disjunction from Stacks Lemma `15.108.1`, expressed on the owner predicates for
  intermediate algebras together with the fiberwise specialization condition on
  `p.asIdeal.primesOver B` and the proposition-valued unique generic-fiber condition
  `Nonempty ((⊥ : Ideal A).primesOver B) ∧ Subsingleton ((⊥ : Ideal A).primesOver B)`;
* core/canonical layer: the owner predicates `Algebra.Etale`, `Algebra.Unramified`,
  `Algebra.QuasiFinite`, `Algebra.IsIntegral`, and the owner fiber sets `p.asIdeal.primesOver B`.

Primitive data vs. derived API:
* primitive data in the localization clauses: an intermediate `A`-algebra `C`, a localization
  `C → B`, and one of the canonical owner predicates on `C`;
* derived API: the fiberwise antisymmetry consequence of quasi-finiteness and the generic-point
  image criterion over `Spec A`.
-/

variable {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
variable [Algebra A B]

-- Proof sketch: reduce cases (1) through (6) to the unique-generic-fiber case as in the Stacks
-- proof. In that case a nonzero element of `J` becomes a unit over the generic fiber and hence in
-- some localization `B_f`, producing a nonzero element of `A ∩ J`.
/-- Lemma 15.108.1: under any of the seven stated hypotheses on the domain map `A → B`, every
nonzero ideal of `B` has nonzero contraction to `A`. -/
theorem ideal_comap_ne_bot_of_cases
    (hAB :
      (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
          (_ : IsScalarTower A C B) (M : Submonoid C), Algebra.Etale A C ∧ IsLocalization M B) ∨
        (Module.Flat A B ∧
          ((∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.Unramified A C ∧ IsLocalization M B) ∨
            (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.QuasiFinite A C ∧ IsLocalization M B) ∨
            (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.IsIntegral A C ∧ IsLocalization M B) ∨
            ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q')) ∨
        (Nonempty ((⊥ : Ideal A).primesOver B) ∧
          ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q') ∨
      Nonempty ((⊥ : Ideal A).primesOver B) ∧ Subsingleton ((⊥ : Ideal A).primesOver B))
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry

/-! ### Lemma_15_108_2 (from Chap15) -/
universe u v

section

/-
Domain-style sampling for Lemma 15.108.2:
- primary domain: local commutative algebra at a prime, with localized maps and local étaleness;
- sampled owner declarations:
  `Algebra.UnramifiedAt`,
  `Algebra.unramifiedAt_iff_isUnramifiedAt`,
  `Localization.localRingHom`,
  `IsGeometricallyUnibranch`,
  `Algebra.Etale`;
- best owner abstraction: the source prime should be carried by `q : PrimeSpectrum B`, and the
  base prime is then canonically its contraction `q.asIdeal.under A`; keeping a separate
  parameter `p` together with `[q.asIdeal.LiesOver p]` is redundant public data.

Primitive data vs. derived API:
- primitive data: the prime `q`, geometric unibranchness of `Localization.AtPrime (q ∩ A)`, the
  source-facing unramified-at-prime hypothesis `Algebra.UnramifiedAt A B q`, and injectivity of
  the canonical localized map `A_(q ∩ A) → B_q`;
- derived API: an étale basic-open neighbourhood of `q`.

Source/core/bridge triage:
- `source-facing`: the existence of an étale basic-open neighbourhood of `q`;
- `core/canonical`: `Algebra.UnramifiedAt`, `Localization.localRingHom`, and
  `IsGeometricallyUnibranch`;
- `bridge/view`: the contraction `q.asIdeal.under A`, which replaces the redundant explicit
  parameter `p`.
-/
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A]

-- Proof sketch: use the local unramified hypothesis at `q` to shrink `B` to a standard étale
-- neighborhood of `q`, localize further to isolate the unique branch coming from the
-- geometrically unibranch local ring `A_p`, and then apply Lemma `15.108.1` to the kernel of the
-- resulting surjection to prove that the map is injective after shrinking. The localized target is
-- then étale over `A`.
/-- Lemma 15.108.2: if `q` lies over `p`, `A` is a domain, `A_p` is geometrically unibranch,
`A → B` is unramified at `q`, and the induced local map `A_p → B_q` is injective, then there
exists `g ∈ B \ q` such that `B_g` is étale over `A`. -/
theorem exists_etale_localizationAway_of_geometricallyUnibranch_of_unramifiedAtPrime_of_injective_localRingHom
    (q : PrimeSpectrum B)
    [IsGeometricallyUnibranch (Localization.AtPrime (q.asIdeal.under A))]
    (hunram : Algebra.UnramifiedAt A B q)
    (hinj : Function.Injective
      (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)) :
    ∃ g : B, g ∉ q.asIdeal ∧ Algebra.Etale A (Localization.Away g) := sorry

end

/-! ### Lemma_15_108_3 (from Chap15) -/
open IsLocalRing

universe u v

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of geometrically unibranch local domains, essential
  finite type local maps, and étale localization criteria;
- sampled owner declarations of the same kind:
  `IsLocalization`,
  `Algebra.Etale`,
  `exists_etale_localizationAway_of_geometricallyUnibranch_of_unramifiedAtPrime_of_injective_localRingHom`,
  `ideal_comap_ne_bot_of_cases`;
- best owner abstraction: the source-facing conclusion is an intermediate étale `A`-algebra `C`
  together with a localization witness `IsLocalization M B`; collapsing this to
  `Algebra.Etale A B` is too strong here, because a local ring obtained by localizing an étale
  `A`-algebra need not itself be finite presented over `A`;
- primitive data: the local domain `A`, the local `A`-algebra `B`, the injective local map,
  the maximal-ideal equality, the separable residue-field extension, and the essential finite type
  hypothesis;
- derived API: an étale `A`-algebra whose localization is `B`.

Source/core/bridge triage:
- `source-facing`: the theorem below, expressing Stacks Lemma `15.108.3` as a localization
  existence result;
- `core/canonical`: the owner predicate `Algebra.Etale A C` on an intermediate algebra `C` and
  the localization owner `IsLocalization M B`;
- `bridge/view`: the essential finite type presentation of `B` and the étale-localization
  neighborhood produced by Lemma `15.108.2`.
-/
variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsLocalRing A] [IsGeometricallyUnibranch A]
variable [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [Algebra.EssFiniteType A B]

-- Proof sketch: write `B` as a localization of a finite type `A`-algebra `C` at a prime over the
-- maximal ideal of `A`. Lemma `10.151.7` gives that `A → C` is unramified at that prime from the
-- maximal-ideal and separable-residue-field hypotheses, and Lemma `15.108.2` then produces an
-- étale `A`-algebra after shrinking around that prime. The geometric-unibranch hypotheses and
-- Lemmas `15.107.7`, `15.107.8`, and `15.108.1` show that the resulting local map into `B` is
-- injective, yielding an intermediate étale `A`-algebra whose localization identifies with `B`.
/-- Lemma 15.108.3: if `(A, 𝔪)` is a geometrically unibranch local domain and `A → B` is an
injective local homomorphism of local rings that is essentially of finite type, such that
`𝔪 B = maximalIdeal B` and the induced residue-field extension is separable, then `B` is the
localization of an étale `A`-algebra. -/
theorem exists_etale_localization_of_isGeometricallyUnibranch_of_injective_localHom
    (hinj : Function.Injective (algebraMap A B))
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (M : Submonoid C), Algebra.Etale A C ∧ IsLocalization M B := sorry

end

/-! ### Lemma_15_108_4 (from Chap15) -/
open IsLocalRing
open PrimeSpectrum
open scoped TensorProduct

universe u

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of strict henselizations, tensor products of local
  `k`-algebras, and minimal primes;
- sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `IsStrictHenselizationOf`,
  `minimalPrimes`,
  `Localization.AtPrime`,
  `Algebra.TensorProduct.includeLeft` / `includeRight`;
- best owner abstraction: the source-facing content is the contraction of a prime of the chosen
  strict henselization of the canonical closed-point localization of the tensor product to the
  pair of primes in the two tensor factors, while the canonical owners remain the closed-point
  prime, the strict-henselization structure, and the minimal primes as subtype owners;
- primitive data: the local `k`-algebras `A`, `B`, the closed-point localization of `A ⊗[k] B`,
  and its chosen strict henselization `C`;
- derived API: the two canonical maps `A → C`, `B → C`, and the induced map from primes of `C`
  to pairs of minimal primes of `A` and `B`; the localization step should be expressed through
  the canonical owner `Localization.AtPrime`, while the residue-field identifications with `k`
  should be `k`-algebra equivalences rather than bare ring equivalences.

Source/core/bridge triage:
- `source-facing`: `strictHenselianTensorMinimalPrimePair` and the bijection theorem below;
- `core/canonical`: `StrictHenselianLocalRing`, `IsStrictHenselizationOf`,
  `strictHenselianTensorClosedPoint`, `Ideal.comap`, `minimalPrimes`;
- `bridge/view`: the chosen strict henselization `C` of the canonical closed-point localization.
-/

variable {k A B C : Type u}
variable [Field k]
variable [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]

section ClosedPoint

variable [IsLocalRing A] [IsLocalRing B]

/-- The closed-point ideal `m_A ⊗ B + A ⊗ m_B` in the tensor product of two local `k`-algebras. -/
abbrev strictHenselianTensorClosedPointIdeal : Ideal (A ⊗[k] B) :=
  Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
      (IsLocalRing.maximalIdeal A) +
    Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
      (IsLocalRing.maximalIdeal B)

-- Proof sketch: the residue-field identifications make the closed fiber of
-- `A ⊗[k] B → ResidueField A ⊗[k] ResidueField B` canonically the field `k`, so the closed-point
-- ideal is the kernel of a map to a field and hence prime.
/-- The closed-point ideal in `A ⊗[k] B` is prime once the residue fields of `A` and `B` are
identified with `k` as `k`-algebras. -/
theorem strictHenselianTensorClosedPointIdeal_isPrime
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) :
    (strictHenselianTensorClosedPointIdeal : Ideal (A ⊗[k] B)).IsPrime := sorry

/-- The closed point of `Spec (A ⊗[k] B)` cut out by `m_A ⊗ B + A ⊗ m_B`. -/
abbrev strictHenselianTensorClosedPoint
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) :
    PrimeSpectrum (A ⊗[k] B) :=
  ⟨strictHenselianTensorClosedPointIdeal, strictHenselianTensorClosedPointIdeal_isPrime hκA hκB⟩

instance strictHenselianTensorClosedPoint_isPrime
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) :
    (strictHenselianTensorClosedPoint hκA hκB).asIdeal.IsPrime :=
  (strictHenselianTensorClosedPoint hκA hκB).isPrime

/-- The canonical localization of `A ⊗[k] B` at its closed point. -/
abbrev strictHenselianTensorClosedPointLocalization
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) : Type u :=
  Localization.AtPrime (strictHenselianTensorClosedPoint hκA hκB).asIdeal

end ClosedPoint

section StrictHenselization

variable [StrictHenselianLocalRing A] [StrictHenselianLocalRing B]

section

variable (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k)

variable [CommRing C]
variable [Algebra (strictHenselianTensorClosedPointLocalization hκA hκB) C]

/-- The map from `A` to the chosen strict henselization of the closed-point localization of
`A ⊗[k] B`. -/
abbrev strictHenselianTensorStrictHenselizationLeftMap : A →+* C :=
  (algebraMap (strictHenselianTensorClosedPointLocalization hκA hκB) C).comp <|
    (algebraMap (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB)).comp <|
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom

/-- The map from `B` to the chosen strict henselization of the closed-point localization of
`A ⊗[k] B`. -/
abbrev strictHenselianTensorStrictHenselizationRightMap : B →+* C :=
  (algebraMap (strictHenselianTensorClosedPointLocalization hκA hκB) C).comp <|
    (algebraMap (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB)).comp <|
      (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom

-- Proof sketch: once `C` is a strict henselization of the canonical closed-point localization of
-- `A ⊗[k] B`, a minimal prime of `C` contracts to minimal primes of `A` and `B`.
/-- The contraction of a minimal prime of `C` along the left map `A → C` is a minimal prime
of `A`. -/
theorem strictHenselianTensorStrictHenselization_left_mem_minimalPrimes
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (r : minimalPrimes C) :
    Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1 ∈
      minimalPrimes A := by
  sorry

/-- The contraction of a minimal prime of `C` along the right map `B → C` is a minimal prime
of `B`. -/
theorem strictHenselianTensorStrictHenselization_right_mem_minimalPrimes
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (r : minimalPrimes C) :
    Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1 ∈
      minimalPrimes B := by
  sorry

/-- A minimal prime of the chosen strict henselization of the closed-point localization of
`A ⊗[k] B` determines a pair of contracted minimal primes in `A` and `B`. -/
abbrev strictHenselianTensorMinimalPrimePair
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (r : minimalPrimes C) :
    minimalPrimes A × minimalPrimes B :=
  ( ⟨ Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1
      , strictHenselianTensorStrictHenselization_left_mem_minimalPrimes hκA hκB r ⟩
  , ⟨ Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1
      , strictHenselianTensorStrictHenselization_right_mem_minimalPrimes hκA hκB r ⟩ )

-- Proof sketch: contract a minimal prime of `C` along the flat maps from the localized tensor
-- product to `A` and `B` to get minimal primes of the two factors. For surjectivity, reduce to
-- the quotients by chosen minimal primes of `A` and `B`, use strict henselianity of those
-- quotients, normalize the resulting local domains, and compare with the strict henselization via
-- the normal local domain obtained from the localized tensor product of the normalizations.
/-- Lemma 15.108.4: if `A` and `B` are strictly henselian local `k`-algebras with residue fields
identified with `k` as `k`-algebras, and `C` is a chosen strict
henselization of the canonical localization of `A ⊗[k] B` at `m_A ⊗ B + A ⊗ m_B`, then
contraction along the canonical maps `A → C` and `B → C` gives a bijection between the minimal
primes of `C` and pairs of minimal primes of `A` and `B`. -/
theorem strictHenselianTensorStrictHenselization_bijOn_minimalPrimePairs
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C] :
    Function.Bijective
      (fun r : minimalPrimes C ↦ strictHenselianTensorMinimalPrimePair hκA hκB r) := by
  sorry

end

end StrictHenselization

end
