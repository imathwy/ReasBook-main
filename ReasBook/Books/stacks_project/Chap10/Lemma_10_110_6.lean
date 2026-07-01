import Mathlib
import stacks_project.Chap10.Definition_10_110_7
import stacks_project.Chap10.Proposition_10_110_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: Noetherian local commutative algebra, relating the owner predicates
  `IsRegularLocalRing` and `IsFiniteGlobalDimensionRing`;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `IsFiniteGlobalDimensionRing`,
  `residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae`,
  `IsRegularRing.isRegularLocalRing_atPrime`;
* best owner abstraction: the core owners are `IsRegularLocalRing R`, `IsFiniteGlobalDimensionRing R`,
  and, for primewise propagation, `IsRegularRing R`;
* primitive data vs. derived API: the two owner predicates are primitive here, while the
  source-facing equivalence below and the localization theorem are derived API obtained from
  Proposition `10.110.5` and the regular-ring owner field.
* source/core/bridge triage:
  `isRegularLocalRing_iff_isFiniteGlobalDimensionRing` is `source-facing`,
  the owner predicates above are `core/canonical`,
  and `isRegularLocalRing_localizationAtPrime` is a `bridge/view` consequence of the regular-ring
  owner.

This file should therefore reuse those owners directly and avoid a parallel local proof/API layer.
-/

/-- Lemma 10.110.6: a Noetherian local ring is a regular local ring if and only if it has finite
global dimension. -/
theorem isRegularLocalRing_iff_isFiniteGlobalDimensionRing :
    IsRegularLocalRing R ↔ IsFiniteGlobalDimensionRing R := by
  simpa using
    (residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae).out 2 1

variable [IsRegularLocalRing R]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Every localization of a regular local ring at a prime ideal is again a regular local ring. -/
theorem isRegularLocalRing_localizationAtPrime (p : PrimeSpectrum R) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  IsRegularRing.isRegularLocalRing_atPrime p

end
