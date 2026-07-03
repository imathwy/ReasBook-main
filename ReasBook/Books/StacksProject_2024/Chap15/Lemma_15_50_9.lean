import Mathlib
import stacks_project.Chap10.Definition_10_160_1
import stacks_project.Chap15.Lemma_15_50_2
import stacks_project.Chap15.Proposition_15_50_12

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra IsLocalRing
open scoped Polynomial

universe u

section

variable {A : Type u} [CommRing A]

local instance polynomial_isGRing [IsGRing A] : IsGRing A[X] :=
  by
    exact isGRing_of_finiteType A

/- Domain-style sampling:
- primary domain: `G`-rings, completed localizations, and geometric regularity of formal fibers in
  the polynomial case over a Noetherian complete local base;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `isGRing_of_finiteType`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: `IsGRing` is the `core/canonical` owner for the proof route, while the
  numbered lemma itself is the `source-facing` maximal/prime-pair specialization in `A[X]`;
- primitive data for the source-facing theorem: a Noetherian complete local ring `A`, a maximal
  ideal `q : MaximalSpectrum A[X]`, and a prime `r : PrimeSpectrum A[X]` with
  `r ⊆ q`;
- derived API: geometric regularity of the formal fiber
  `r.asIdeal.Fiber (R̂_[q.toPrimeSpectrum])`;
- the proof should reuse the finite-type transfer theorem `isGRing_of_finiteType` and the prime-pair
  criterion from Lemma `15.50.2` directly, rather than keeping a parallel local specialization.
-/
/-- Lemma 15.50.9: for a Noetherian complete local ring `A`, every prime pair `r ⊆ q` in `A[X]`
with `q` maximal has geometrically regular formal fiber
`r.asIdeal.Fiber (R̂_[q.toPrimeSpectrum])` over `κ(r)`.

In the source's positive-characteristic complete-local-domain situation, the extra hypotheses are
already absorbed by the canonical `IsGRing` instance on Noetherian complete local rings, so the
public statement keeps only the genuine inputs used by the owner-level transfer
`isGRing_of_finiteType` together with the prime-pair criterion from Lemma `15.50.2`. -/
theorem polynomial_completedLocalization_formalFiber_isGeometricallyRegular
    [IsNoetherianRing A] [IsCompleteLocalRing A]
    (q : MaximalSpectrum A[X]) (r : PrimeSpectrum A[X])
    (hr_le : r.asIdeal ≤ q.asIdeal) :
    IsGeometricallyRegular r.asIdeal.ResidueField
      (r.asIdeal.Fiber (R̂_[q.toPrimeSpectrum])) := by
  exact
    (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular A[X]).1
      (inferInstance : IsGRing A[X]) q.toPrimeSpectrum r hr_le

end
