import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_76_7

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.78.2:
- primary domain: perfectness and tor-amplitude for pseudo-coherent derived `R`-complexes,
  detected on residue-field fibers over prime and maximal ideals;
- sampled owner declarations:
  `K.IsPerfect`,
  `HasTorAmplitudeIn K a b`,
  `primeResidueFieldDerivedHomology`,
  `K ⊗[R]^L[κ(𝔭)]`;
- best owner abstraction: the public source-facing statement should be expressed in terms of the
  canonical owners `K.IsPerfect`, `HasTorAmplitudeIn`, and the earlier chapter bridge
  `primeResidueFieldDerivedHomology`, rather than re-expanding residue-field fibers through
  `derivedTensorProduct` and `singleFunctor`;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K`, the interval bounds `a, b`, and the
  residue-field homology objects indexed by primes;
  derived API is the conjunction `K.IsPerfect ∧ HasTorAmplitudeIn K a b` and the maximal-ideal
  specialization of the prime-fiber vanishing condition.

Source/core/bridge triage:
- `source-facing`: the TFAE criterion below;
- `core/canonical`: `K.IsPerfect` and `HasTorAmplitudeIn K a b`;
- `bridge/view`: `primeResidueFieldDerivedHomology`, which names the degreewise homology of the
  canonical derived base change `K ⊗_R^L κ(𝔭)` without introducing a second owner abstraction.
-/

-- Proof sketch: the implications from perfection with tor-amplitude to prime fibers and then to
-- maximal fibers are immediate by derived base change. For the converse, use Lemma `15.77.4` to
-- deduce vanishing of the cohomology of `K` outside `[a, b]` and to obtain local perfect
-- tor-amplitude bounds near every maximal ideal; then conclude globally from Lemma `15.75.12` and
-- Lemma `15.67.16`.
/-- Lemma 15.78.2: for a pseudo-coherent object `K` of `D(R)`, the following are equivalent:
`K` is perfect with tor-amplitude in `[a, b]`; for every prime `𝔭` of `R`, the derived fiber
`K \otimes_R^{\mathbf L} κ(\mathfrak p)` has vanishing homology outside `[a, b]`; and it is
enough to check this only on maximal ideals. -/
theorem perfect_torAmplitude_tfae_prime_and_maximal_residueField_homology_vanishing_of_isPseudoCoherent
    (K : DMod) (a b : ℤ) (hK : K.IsPseudoCoherent) :
    List.TFAE [
      K.IsPerfect ∧ HasTorAmplitudeIn K a b,
      ∀ 𝔭 : PrimeSpectrum R, ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology 𝔭 K i),
      ∀ (𝔪 : PrimeSpectrum R) (_ : 𝔪.asIdeal.IsMaximal) (i : ℤ), i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology 𝔪 K i)
    ] := by
  sorry

end

end CategoryTheory
