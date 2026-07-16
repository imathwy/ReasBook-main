import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_113_2

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing

universe u v

section

/-
Domain triage:
* primary domain: one-dimensional local domains, primes lying over the closed point, and the
  induced residue-field extensions;
* source-facing owner data: the fiber index `P : 𝔪.primesOver S` for `𝔪 = maximalIdeal R`;
* core/canonical owners sampled for this refinement:
  `FiniteDimensional (FractionRing R) (FractionRing S)`,
  `Algebra (FractionRing R) (FractionRing S)`,
  `IsScalarTower R (FractionRing R) (FractionRing S)`,
  `Ideal.primesOver`,
  `finite_primesOver_and_primeHeight_eq_one_of_primeHeight_eq_one`,
  `Ideal.ResidueField.map`,
  `IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim`;
* layer: `source-facing`, since the textbook item is specifically about the closed fiber over the
  maximal ideal of a local domain, while `primesOver` and residue-field maps are the canonical
  ambient owners.

Primitive data are the rings `R`, `S`, the ring map `R → S`, the owner hypothesis that `Frac(S)`
is finite-dimensional over `Frac(R)`, and a prime `P : 𝔪.primesOver S`. The three
public theorems are derived API: maximality of `P`, finiteness of the closed fiber, and finiteness
of the residue-field extension `κ(𝔪) → κ(P)`. -/
variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [IsLocalRing R] [IsNoetherianRing R] [Algebra R S]
variable [Algebra (FractionRing R) (FractionRing S)]
variable [IsScalarTower R (FractionRing R) (FractionRing S)]
variable [FiniteDimensional (FractionRing R) (FractionRing S)]

local notation "mR" => maximalIdeal R
local notation "kR" => Ideal.ResidueField mR

-- Proof sketch: choose a nonzero element of `maximalIdeal R`, use Lemma `10.119.9` to show that
-- `S / maximalIdeal R • S` has finite length over `ResidueField R`, and hence is Artinian. Prime
-- ideals of `S` lying over `maximalIdeal R` correspond to prime ideals of this Artinian quotient,
-- so each such prime is maximal.
/-- Lemma 10.119.10 (1): if `R → S` is a homomorphism of domains, `R` is a one-dimensional
Noetherian local domain, and the induced extension of fraction rings is finite, then each prime
ideal of `S` lying over `maximalIdeal R` is maximal. -/
theorem isMaximal_of_primeOver_maximalIdeal_of_finite_fractionField_extension
    (hdim : ringKrullDim R = 1) (P : (mR).primesOver S) :
    P.1.IsMaximal := sorry

-- Proof sketch: the same finite-length argument shows that `S / maximalIdeal R • S` is an
-- Artinian ring. Its prime spectrum is finite, and primes of `S` lying over `maximalIdeal R`
-- identify with primes of this quotient, giving finiteness of the fiber over `maximalIdeal R`.
/-- Lemma 10.119.10 (2): if `R → S` is a homomorphism of domains, `R` is a one-dimensional
Noetherian local domain, and the induced extension of fraction rings is finite, then only finitely
many prime ideals of `S` lie over `maximalIdeal R`. -/
theorem finite_primesOver_maximalIdeal_of_finite_fractionField_extension
    (hdim : ringKrullDim R = 1) :
    Finite ((mR).primesOver S) := sorry

-- Proof sketch: after proving that `S / maximalIdeal R • S` has finite length over
-- `ResidueField (Localization.AtPrime (maximalIdeal R)) = (maximalIdeal R).ResidueField`, each
-- quotient by a prime lying over `maximalIdeal R` is a finite module over the same residue field.
-- Identifying that quotient field with `P.ResidueField` gives the required finite residue-field
-- extension.
/-- Lemma 10.119.10 (3): if `R → S` is a homomorphism of domains, `R` is a one-dimensional
Noetherian local domain, and the induced extension of fraction rings is finite, then for each
prime ideal `𝔫` of `S` lying over `maximalIdeal R`, the residue field extension
`κ(𝔫) / κ(maximalIdeal R)` is finite. -/
theorem moduleFinite_residueField_of_primeOver_maximalIdeal_of_finite_fractionField_extension
    (hdim : ringKrullDim R = 1) (P : (mR).primesOver S) :
    Module.Finite kR P.1.ResidueField := sorry

end
