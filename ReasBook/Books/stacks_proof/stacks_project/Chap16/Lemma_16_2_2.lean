import Mathlib
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap16.Lemma_16_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A] [FinitePresentation R A]

/- Domain-style sampling for Lemma 16.2.2:
* primary domain: local smoothness of finitely presented commutative algebras at primes and
  source-facing Jacobian-standard neighbourhoods;
* sampled owner declarations:
  `SmoothAtPrime`,
  `smoothAtPrime_iff_isSmoothAt`,
  `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`,
  `standardSmoothAway_eventually_elementaryStandard_pow`;
* best owner abstraction:
  `SmoothAtPrime` is the source-facing owner at a prime of `Spec A`, while `IsSmoothAt` and
  `IsStandardSmooth` are the canonical core owners for the proof route on a basic open
  localization;
* primitive vs. derived:
  the primitive public data are only the prime `q` and the source-facing smoothness hypothesis.
  The standard-smooth basic open and the eventual elementary-standard powers are derived bridge
  data and should be reused directly from the existing owner theorems rather than repackaged
  locally.

Source/core/bridge triage:
* `source-facing`: existence of an element outside `q` that is elementary standard or strictly
  standard;
* `core/canonical`: `IsSmoothAt` and `IsStandardSmooth` on localizations `A[1/a]`;
* `bridge/view`: `smoothAtPrime_iff_isSmoothAt`,
  `standardSmoothAway_eventually_elementaryStandard_pow`, and
  `isElementaryStandard_implies_isStrictlyStandard`.
-/

-- Proof sketch: use `IsSmoothAt.exists_notMem_isStandardSmooth` to pass to a basic open
-- neighbourhood on which `A` becomes standard smooth, then apply the Chapter 16 bridge from
-- standard smoothness of a localization to eventual elementary standardness of a power of the
-- defining element.
/-- Lemma 16.2.2: if the finitely presented `R`-algebra `A` is smooth at the prime `q`, then some
element of `A` avoiding `q` is elementary standard over `R`. Equivalently, every smooth point of
`Spec A` admits a basic open neighbourhood cut out by an elementary standard element. -/
@[stacks 07C6]
theorem smoothAtPrime_exists_not_mem_isElementaryStandard
    (q : PrimeSpectrum A) (hq : SmoothAtPrime R A q) :
    ∃ a : A, a ∉ q.asIdeal ∧ IsElementaryStandard R a := by
  letI : IsSmoothAt R q.asIdeal := (smoothAtPrime_iff_isSmoothAt R A q).mp hq
  obtain ⟨a, haq, hstd⟩ :=
    IsSmoothAt.exists_notMem_isStandardSmooth R q.asIdeal
  obtain ⟨e0, he0⟩ :=
    standardSmoothAway_eventually_elementaryStandard_pow a hstd
  refine ⟨a ^ (e0 + 1), ?_, he0 (e0 + 1) (Nat.le_succ e0)⟩
  exact fun hpow ↦ haq ((inferInstance : q.asIdeal.IsPrime).mem_of_pow_mem _ hpow)

-- Proof sketch: apply Lemma 16.3.7 (b), i.e. the implication `(6) ⇒ (5)`, to the elementary
-- standard element produced above.
/-- Companion corollary: a smooth point also admits a basic open neighbourhood cut out by a
strictly standard element. -/
theorem smoothAtPrime_exists_not_mem_isStrictlyStandard
    (q : PrimeSpectrum A) (hq : SmoothAtPrime R A q) :
    ∃ a : A, a ∉ q.asIdeal ∧ IsStrictlyStandard R a := by
  rcases smoothAtPrime_exists_not_mem_isElementaryStandard q hq with
    ⟨a, haq, ha⟩
  exact ⟨a, haq, isElementaryStandard_implies_isStrictlyStandard a ha⟩

end Algebra
