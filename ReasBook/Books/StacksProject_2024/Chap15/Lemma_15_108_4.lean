import Mathlib
import stacks_project.Chap10.Definition_10_153_1
import stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

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
