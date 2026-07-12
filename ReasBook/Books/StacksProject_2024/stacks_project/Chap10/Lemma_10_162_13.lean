import Mathlib
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Definition_10_162_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R] [NagataRing R]

/- Domain-style sampling:
- primary domain: local Nagata domains and analytically unramified maximal-ideal completions;
- sampled owner declarations:
  `NagataRing`,
  `IsAnalyticallyUnramified`,
  `isAnalyticallyUnramified_iff`,
  and `PrimeSpectrum.IsAnalyticallyUnramified`;
- best owner abstraction: `IsAnalyticallyUnramified` is the core/canonical owner for the target
  conclusion, so this file should expose the result directly in that owner language rather than
  through a parallel completion-reducedness wrapper;
- primitive data vs. derived API: the primitive data are the ambient hypotheses
  `[IsLocalRing R] [IsDomain R] [NagataRing R]`, while reducedness of the completion is derived
  bridge API coming from `isAnalyticallyUnramified_iff`.
-/

-- Proof sketch: let `S` be the integral closure of `R` in `FractionRing R`. Since `R` is Nagata,
-- `S` is module-finite over `R`; localize at the finitely many maximal ideals of `S` over the
-- maximal ideal of `R` and use completion to reduce to the normal case. Then apply Lemma
-- `10.162.12` to a nonzero element of the maximal ideal, using the height-one regularity of the
-- associated primes of `R / xR` and induction on dimension for the quotient domains.
/-- Lemma 10.162.13: a local Nagata domain is analytically unramified. -/
instance isAnalyticallyUnramified_of_nagataRing : IsAnalyticallyUnramified R := sorry

end
