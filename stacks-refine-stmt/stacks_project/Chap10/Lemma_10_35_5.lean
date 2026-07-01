import Mathlib
import stacks_project.Chap05.Lemma_5_18_3
import stacks_project.Chap10.Definition_10_17_1
import stacks_project.Chap10.Lemma_10_17_6
import stacks_project.Chap10.Lemma_10_17_7
import stacks_project.Chap10.Lemma_10_35_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum TopologicalSpace
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: Jacobson-topological behavior of `Spec R` and its basic opens/localizations;
* source-facing layer: the two public theorems keep the Stacks formulation in terms of
  `V(p) ∩ D(f)`;
* core/canonical owners: `IsJacobsonRing R`, `JacobsonSpace (PrimeSpectrum R)`, the chapter
  homeomorphisms `primeSpectrum_quotient_homeomorph_zeroLocus` and
  `primeSpectrum_localizationAway_homeomorph_D`, and mathlib's
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`;
* primitive data vs. derived API: the only public witnesses are the textbook `p` and `f`. The
  singleton-spectrum and localization-at-prime identifications stay derived from the owner
  abstractions rather than appearing as extra wrapper data in the theorem statements.
-/

-- Proof sketch: use Lemma `5.18.3` together with
-- `PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace` to obtain a nonclosed prime `p` whose
-- singleton is locally closed in `Spec R`. Express that singleton as `V(p) ∩ D(f)` via the
-- quotient and localization homeomorphisms from Lemmas `10.17.7` and `10.17.6`.
/-- Lemma 10.35.5 (1): if `R` is not Jacobson, then there exist a nonmaximal prime `p` and an
element `f` such that `V(p) ∩ D(f) = {p}`. -/
theorem exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing
    (hR : ¬ IsJacobsonRing R) :
    ∃ (p : PrimeSpectrum R) (f : R),
      ¬ p.asIdeal.IsMaximal ∧
        V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) = {p} := sorry

-- Proof sketch: transport the singleton description of `V(p) ∩ D(f)` along the quotient and
-- localization spectrum homeomorphisms from Lemmas `10.17.7` and `10.17.6`, then apply
-- `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton` to identify
-- `((R ⧸ p)_f)` with the local ring at the corresponding singleton point of its spectrum.
/-- Lemma 10.35.5 (2): if `V(p) ∩ D(f) = {p}`, then the localization `(R / p)_f` is a field. -/
theorem isField_localizationAway_quotient_of_zeroLocus_inter_basicOpen_eq_singleton
    (p : PrimeSpectrum R) (f : R)
    (hp :
      V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) = {p}) :
    IsField (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) := sorry

-- Proof sketch: in the Jacobson space `Spec R`, the locally closed subset `V(p) ∩ D(f)` has
-- dense closed points. If it were finite, it would be discrete by `JacobsonSpace.discreteTopology`,
-- so the point `p` would be closed in that subset and hence closed in `Spec R`, contradicting
-- `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.
/-- Lemma 10.35.5 (3): if `R` is Jacobson, then for every nonmaximal prime `p` and every
`f ∉ p`, the locally closed subset `V(p) ∩ D(f)` is infinite. -/
theorem infinite_zeroLocus_inter_basicOpen_of_isJacobsonRing
    [IsJacobsonRing R] (p : PrimeSpectrum R) (f : R)
    (hp : ¬ p.asIdeal.IsMaximal) (hf : f ∉ p.asIdeal) :
    Set.Infinite (V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R))) := sorry

end
