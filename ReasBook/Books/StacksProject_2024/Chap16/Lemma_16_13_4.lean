import Mathlib
import StacksProject_2024.Chap15.Definition_15_50_1
import StacksProject_2024.Chap15.Lemma_15_50_14
import StacksProject_2024.Chap16.Theorem_16_13_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open Algebra
open MvPolynomial

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (p : PrimeSpectrum R)

local notation "Rₚ" => Localization.AtPrime p.asIdeal

/- Domain-style sampling:
- primary domain: Artin approximation over a localized Noetherian ring, descended back to an
  étale neighborhood over the original ring;
- sampled owner declarations in this domain:
  `IsGRing`,
  `CompletedLocalizationAtPrime`,
  `CompletedLocalizationAtPrime.map`,
  `RingHom.adicCompletionMap`,
  `Localization.localRingHom`,
  `IsRegularRingMap`,
  `(inferInstance : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap)`,
  `Algebra.Etale`,
  `Ideal.ResidueField.map`;
- best owner abstraction: the main source-facing theorem should keep `IsGRing Rₚ` as the owner
  hypothesis for the localized ring `Rₚ`, while the regularity of the completion map
  `Rₚ → R̂_[p]` is a derived bridge supplied by the Chapter 15 owner instance on
  `(algebraMap Rₚ (R̂_[p])).IsRegularRingMap`; the completed local rings themselves
  should use the chapter owner `CompletedLocalizationAtPrime` and its notation `R̂_[p]`, while the
  primewise comparison map between completed localizations should use the owner-level bridge
  `CompletedLocalizationAtPrime.map`, and the residue-field comparison should use the canonical
  owner `Ideal.ResidueField.map` derived directly from the intrinsic condition
  `PrimeSpectrum.comap (algebraMap R R') p' = p`;
- primitive data: the étale `R`-algebra `R'`, the prime `p'` over `p`, and the solution `b`;
- derived API: the canonical map `R̂_[p] → R̂_[p']`, residue-field bijectivity, exact solvability
  of the polynomial system, and the congruence modulo the `N`-th power of the maximal ideal
  upstairs.

Source/core/bridge triage:
- `source-facing`: the existence theorem below;
- `core/canonical`: `IsGRing`, `CompletedLocalizationAtPrime`,
  `CompletedLocalizationAtPrime.map`, `RingHom.adicCompletionMap`, `Localization.localRingHom`,
  `IsRegularRingMap`, `Algebra.Etale`, and
  `Ideal.ResidueField.map`;
- `bridge/view`: the Chapter 15 owner instance
  `(inferInstance : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap)` for the regular completion map;
  the theorem itself is the bridge from the localized version of the approximation theorem back to
  étale neighborhoods over `R`. -/

-- Proof sketch for the regular-completion bridge: apply Theorem `16.13.2` to the local ring
-- `R_𝔭` and the given formal solution in its completion. This yields an étale `R_𝔭`-algebra with
-- a solution approximating `a`. Then use localization descent for étale algebras to write that
-- local étale algebra as the localization of an étale `R`-algebra `R'` at a prime `𝔭'` over
-- `𝔭`, and transport the approximate solution through the identified completed local rings.
/-- Lemma 16.13.4, regular-completion bridge case: if the completion map
`R_𝔭 → (R_𝔭)^` is regular, then every finite polynomial system over `R` with a solution in
`((R_𝔭)^)^n` can, for each `N`, be approximated modulo `(𝔭')^N` by a solution in an étale
neighborhood of `R` above `𝔭`, with unchanged residue field. -/
theorem exists_etale_solution_at_prime_of_completed_local_solution_of_isRegularRingMap
    (hCompletion : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (a : Fin n → R̂_[p])
    (ha : ∀ j, aeval a (f j) = 0) (N : ℕ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : PrimeSpectrum R') (hp' : PrimeSpectrum.comap (algebraMap R R') p' = p)
      (b : Fin n → R'),
      Function.Bijective
        (Ideal.ResidueField.map p.asIdeal p'.asIdeal (algebraMap R R')
          (by
            simpa [PrimeSpectrum.comap_asIdeal] using
              (congrArg PrimeSpectrum.asIdeal hp').symm)) ∧
      (∀ j, aeval b (f j) = 0) ∧
      ∀ i,
        CompletedLocalizationAtPrime.map p p' hp' (a i) -
            algebraMap R' (R̂_[p']) (b i) ∈
          Ideal.map
            (algebraMap (Localization.AtPrime p'.asIdeal) (R̂_[p']))
            ((maximalIdeal (Localization.AtPrime p'.asIdeal)) ^ N) := sorry

-- Proof sketch for the source-facing statement: use the Chapter 15 owner instance on the
-- completion map `Rₚ → R̂_[p]` to convert the `G`-ring hypothesis on the local ring `R_𝔭` into
-- the regular-completion hypothesis above.
/-- Lemma 16.13.4: let `R` be a Noetherian ring and `𝔭 ⊂ R` a prime ideal. If a finite system of
polynomials over `R` has a solution in the completed local ring `((R_𝔭)^)^n`, and if the local
ring `R_𝔭` is a `G`-ring, then for every `N` there exists an étale `R`-algebra `R'`, a prime
`𝔭' ⊂ R'` with `PrimeSpectrum.comap (algebraMap R R') 𝔭' = 𝔭`, and a solution in `R'` whose
image in the completed localization at `𝔭'` under the canonical primewise map
`CompletedLocalizationAtPrime.map p p' hp' : R̂_[p] →+* R̂_[p']` agrees with the given formal
solution modulo `(𝔭')^N`, with unchanged residue field. -/
theorem exists_etale_solution_at_prime_of_completed_local_solution
    [IsGRing Rₚ]
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (a : Fin n → R̂_[p])
    (ha : ∀ j, aeval a (f j) = 0) (N : ℕ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : PrimeSpectrum R') (hp' : PrimeSpectrum.comap (algebraMap R R') p' = p)
      (b : Fin n → R'),
      Function.Bijective
        (Ideal.ResidueField.map p.asIdeal p'.asIdeal (algebraMap R R')
          (by
            simpa [PrimeSpectrum.comap_asIdeal] using
              (congrArg PrimeSpectrum.asIdeal hp').symm)) ∧
      (∀ j, aeval b (f j) = 0) ∧
      ∀ i,
        CompletedLocalizationAtPrime.map p p' hp' (a i) -
            algebraMap R' (R̂_[p']) (b i) ∈
          Ideal.map
            (algebraMap (Localization.AtPrime p'.asIdeal) (R̂_[p']))
            ((maximalIdeal (Localization.AtPrime p'.asIdeal)) ^ N) := by
  let hCompletion : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap := inferInstance
  exact
    exists_etale_solution_at_prime_of_completed_local_solution_of_isRegularRingMap p
      hCompletion f a ha N

end
