import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FractionRing IsLocalization Localization

noncomputable section

section

variable (R : Type u) [CommRing R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-
Lemma 10.25.4 is a `source-facing` total-quotient-ring splitting statement.
The owner abstractions are the canonical minimal-prime index type `minimalPrimes R`, the
localizations `Localization.AtPrime p.1`, and the canonical map
`Algebra.ofId (FractionRing R) (∀ p : minimalPrimes R, Localization.AtPrime p.1)`.
The bijectivity statement below is derived API used only to build the canonical algebra
equivalence, so it is kept private rather than exposed as a second public owner.
-/

-- Proof sketch: a minimal prime is disjoint from the nonzerodivisors by
-- `Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes`; rewriting that disjointness gives the
-- required containment in the prime complement.
/-- Every nonzerodivisor lies in the prime complement of a minimal prime ideal. -/
private theorem nonZeroDivisors_le_primeCompl_of_mem_minimalPrimes
    (p : minimalPrimes R) :
    nonZeroDivisors R ≤ p.1.primeCompl := by
  intro x hx hxI
  exact (Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes p.2)) hxI hx

local instance (p : minimalPrimes R) :
    Algebra (FractionRing R) (Localization.AtPrime p.1) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (FractionRing R)
    (Localization.AtPrime p.1)
    (nonZeroDivisors R)
    p.1.primeCompl
    (nonZeroDivisors_le_primeCompl_of_mem_minimalPrimes R p)

local instance (p : minimalPrimes R) :
    IsScalarTower R (FractionRing R) (Localization.AtPrime p.1) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (FractionRing R)
    (Localization.AtPrime p.1)
    (nonZeroDivisors R)
    p.1.primeCompl
    (nonZeroDivisors_le_primeCompl_of_mem_minimalPrimes R p)

variable [Finite (minimalPrimes R)]

-- Proof sketch: use the zerodivisor hypothesis to identify `Spec(Q(R))` with the finite set of
-- minimal primes of `R`, then apply the finite-discrete-spectrum splitting result from the
-- previous item and identify each factor with the localization at the corresponding minimal prime.
private theorem fractionRing_to_minimalPrimeLocalizations_bijective
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    Function.Bijective
      (Algebra.ofId
        (FractionRing R)
        (∀ p : minimalPrimes R, Localization.AtPrime p.1)) := sorry

/-- Lemma 10.25.4: if `R` has finitely many minimal primes and their union is exactly the set of
zerodivisors, then the total quotient ring `Q(R)` is canonically isomorphic to the product of the
localizations of `R` at its minimal prime ideals. -/
noncomputable def fractionRing_equiv_pi_minimalPrimeLocalizations
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    FractionRing R ≃ₐ[R] ∀ p : minimalPrimes R, Localization.AtPrime p.1 :=
  (AlgEquiv.ofBijective
      (Algebra.ofId
        (FractionRing R)
        (∀ p : minimalPrimes R, Localization.AtPrime p.1))
      (fractionRing_to_minimalPrimeLocalizations_bijective R hzdiv)).restrictScalars R

/-- The canonical equivalence from `Q(R)` to the product of the minimal-prime localizations
commutes with the map from `R`. -/
@[simp]
theorem fractionRing_equiv_pi_minimalPrimeLocalizations_apply_algebraMap
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (r : R) :
    fractionRing_equiv_pi_minimalPrimeLocalizations R hzdiv
        (algebraMap R (FractionRing R) r) =
      algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1) r := by
  exact AlgEquiv.commutes (fractionRing_equiv_pi_minimalPrimeLocalizations R hzdiv) r

end
