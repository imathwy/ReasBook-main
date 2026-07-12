import Mathlib
import StacksProject_2024.Chap10.Lemma_10_37_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- 
Domain-style sampling:
* primary domain: the normal locus on `Spec R` in commutative algebra;
* sampled owner declarations of the same kind:
  `IsNormalRing`,
  `IsNormalRing.isNormalLocalizationAtPrime`,
  `isIntegrallyClosed_of_isNormalRing`,
  `IsLocalization.isDomain_of_atPrime`;
* best owner abstraction: membership in the normal locus is owned by
  `IsNormalRing (Localization.AtPrime p.asIdeal)`;
* primitive data vs. derived API: the primitive pointwise datum is the local normal-ring owner
  `IsNormalRing (Localization.AtPrime p.asIdeal)`, while the domain and integrally-closed views are
  derived API under the ambient domain hypothesis.

Source/core/bridge triage:
* `source-facing`: the normal locus of `Spec R` and the theorem that it is open under the
  existence of one normal principal localization;
* `core/canonical`: `Localization.AtPrime`, `Localization.Away`, and the owner `IsNormalRing`;
* `bridge/view`: the domain-specialized equivalence with integrally closed prime localizations.
-/

namespace PrimeSpectrum

/-- The normal locus of `Spec R`, consisting of the primes whose local rings are normal. -/
def normalLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  { p | IsNormalRing (Localization.AtPrime p.asIdeal) }

/-- Membership in `PrimeSpectrum.normalLocus R` means that the corresponding local ring is
normal. -/
theorem mem_normalLocus {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    p ∈ normalLocus R ↔
      IsNormalRing (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

/-- Over a domain, membership in `PrimeSpectrum.normalLocus R` is equivalent to the corresponding
prime localization being integrally closed. -/
theorem mem_normalLocus_iff_isIntegrallyClosed {R : Type u} [CommRing R] [IsDomain R]
    (p : PrimeSpectrum R) :
    p ∈ normalLocus R ↔
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  rw [mem_normalLocus]
  constructor
  · intro hp
    letI : IsNormalRing (Localization.AtPrime p.asIdeal) := hp
    infer_instance
  · intro hp
    letI : IsDomain (Localization.AtPrime p.asIdeal) :=
      IsLocalization.isDomain_of_atPrime (Localization.AtPrime p.asIdeal) p.asIdeal
    letI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := hp
    infer_instance

end PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

-- Proof sketch: choose `f ≠ 0` such that `Localization.Away f` is normal, so the basic open
-- `D(f)` lies in the normal locus. If `p` is not in the normal locus, Serre's criterion
-- yields a prime `q ≤ p` where either `(S_2)` fails or a height-one localization is not regular;
-- since `R_f` is normal, necessarily `f ∈ q`. These bad primes `q` are controlled by the finitely
-- many associated and embedded associated primes of `R ⧸ Ideal.span ({f} : Set R)`, so the
-- complement of the normal locus is a finite union of closed subsets `V(q)`.
/-- Lemma 10.161.14: if `R` is a Noetherian domain and some nonzero localization `R_f` is normal,
then the normal locus is open in `PrimeSpectrum R`. -/
theorem isOpen_normal_locus_of_exists_isNormalRing_localizationAway
    (h : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f)) :
    IsOpen (PrimeSpectrum.normalLocus R) := sorry

/-- Domain-case companion to Lemma 10.161.14: for a domain, the source-facing normality
hypothesis on `R_f` can be replaced by integrally closedness. -/
theorem isOpen_normal_locus_of_exists_isIntegrallyClosed_localizationAway
    (h : ∃ f : R, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f)) :
    IsOpen (PrimeSpectrum.normalLocus R) := by
  apply isOpen_normal_locus_of_exists_isNormalRing_localizationAway
  rcases h with ⟨f, hf, hclosed⟩
  letI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  letI : IsIntegrallyClosed (Localization.Away f) := hclosed
  exact ⟨f, hf, inferInstance⟩

end
