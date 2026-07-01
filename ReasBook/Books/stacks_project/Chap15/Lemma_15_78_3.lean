import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Data.List.TFAE
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Definition_15_75_1
import stacks_project.Chap15.Lemma_15_60_1
import stacks_project.Chap15.Lemma_15_75_9
import stacks_project.Chap15.Lemma_15_76_7

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.78.3:
- primary domain: perfectness and negative derived-fiber homology criteria for pseudo-coherent
  bounded-below objects of `D(R)` under localization at primes and maximal ideals;
- sampled owner declarations:
  `K.IsPerfect`,
  `derivedTensorWithAlgebra_isPerfect`,
  `primeResidueFieldDerivedHomology`,
  `K.IsPseudoCoherent`,
  `MaximalSpectrum`;
- best owner abstraction: this file is `source-facing` for the local/global `TFAE`, while the
  core/canonical owners are `K.IsPerfect`, `K.IsPseudoCoherent`, `K.IsGE`, the standard derived
  base-change notation `K ⊗[R]^L[S]`, the prime-fiber homology owner
  `primeResidueFieldDerivedHomology`, and the chapter-level maximal-local owner
  `MaximalSpectrum R`;
- primitive vs. derived:
  primitive data are `K`, the prime and maximal localization tests, the residue-field homology
  vanishing tests, and the bounded-below hypothesis in the final theorem;
  derived API is the fiber homology object itself, already owned upstream by
  `primeResidueFieldDerivedHomology`, so this file should reuse that owner instead of restating
  raw homology-functor applications, with maximal tests transported through the canonical bridge
  `m.toPrimeSpectrum : PrimeSpectrum R`;
- source/core/bridge triage:
  `source-facing`: the two `TFAE` theorems below;
  `core/canonical`: `K.IsPerfect`, `K.IsPseudoCoherent`, `K.IsGE`, `derivedTensorWithAlgebra`,
    and `primeResidueFieldDerivedHomology`;
  `bridge/view`: the prime-localization specialization of `derivedTensorWithAlgebra_isPerfect`.
-/

/-- The ideal underlying a point of `Spec R` is prime, viewed as a local typeclass instance. -/
local instance (𝔭 : PrimeSpectrum R) : 𝔭.asIdeal.IsPrime := 𝔭.isPrime

-- Proof sketch: specialize derived base change of perfect complexes to the algebra maps
-- `R → R_𝔭` for prime localizations.
/-- A perfect derived `R`-complex remains perfect after localization at any prime ideal. -/
theorem isPerfect_localizationAtPrime_of_isPerfect
    {K : DMod} (hK : K.IsPerfect) (𝔭 : PrimeSpectrum R) :
    (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect := by
  have hloc : (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect :=
    derivedTensorWithAlgebra_isPerfect K hK
  exact hloc

-- Proof sketch: `(2) ⇒ (3)` is immediate. For `(3) ⇒ (2)`, localize further from a maximal ideal
-- containing the given prime. The implications `(2) ⇒ (4)` and `(3) ⇒ (5)` come from base change
-- to residue fields. For `(4) ⇒ (2)` and `(5) ⇒ (3)`, reduce to the local case and use the gap
-- splitting statement of Lemma `15.77.4` together with Nakayama to force the lower truncation to
-- vanish.
/-- For a pseudo-coherent object of `D(R)`, perfectness after localization at primes, perfectness
after localization at maximal ideals, and vanishing of sufficiently negative residue-field
homology at primes or maximal ideals are equivalent conditions. -/
theorem prime_and_maximal_localizations_and_residueField_vanishing_tfae_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) :
    List.TFAE
      [ ∀ 𝔭 : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect
      , ∀ 𝔪 : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔭 K i)
      , ∀ 𝔪 : MaximalSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)
      ] := sorry

-- Proof sketch: perfection implies perfectness after prime localization by the first theorem.
-- The bounded-below hypothesis and Lemma `15.78.1` upgrade the residue-field vanishing conditions
-- to local perfectness near each maximal ideal, and the previous TFAE then yields equivalence of
-- all five conditions.
/-- Lemma 15.78.3: for a pseudo-coherent bounded-below object `K` of `D(R)`, the following are
equivalent: `K` is perfect, all prime localizations `K \otimes_R^{\mathbf L} R_\mathfrak p` are
perfect, all maximal localizations `K \otimes_R^{\mathbf L} R_\mathfrak m` are perfect, and the
derived fibers over primes or maximal ideals have vanishing homology in all sufficiently negative
degrees. -/
theorem perfect_primeLocalizations_maximalLocalizations_residueField_vanishing_tfae_of_isPseudoCoherent_of_isGE
    (K : DMod) (hK : K.IsPseudoCoherent) (hboundedBelow : ∃ n : ℤ, K.IsGE n) :
    List.TFAE
      [ K.IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect
      , ∀ 𝔪 : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔭 K i)
      , ∀ 𝔪 : MaximalSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)
      ] := sorry

end

end CategoryTheory
