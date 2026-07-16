import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_110_7
import stacks_proof.stacks_project.Chap10.Lemma_10_109_13
import stacks_proof.stacks_project.Chap10.Proposition_10_110_5

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
  Proposition `10.110.5` and localization of finite global dimension.
* source/core/bridge triage:
  `isRegularLocalRing_iff_isFiniteGlobalDimensionRing` is `source-facing`,
  the owner predicates above are `core/canonical`,
  and `isRegularLocalRing_localizationAtPrime` is a `bridge/view` consequence of
  Proposition `10.110.5` plus `localization_hasGlobalDimensionLE`.

This file should therefore reuse those owners directly and avoid a parallel local proof/API layer.
-/

/-- Lemma 10.110.6: a Noetherian local ring is a regular local ring if and only if it has finite
global dimension. -/
@[stacks 0AFS]
theorem isRegularLocalRing_iff_isFiniteGlobalDimensionRing :
    IsRegularLocalRing R ↔ IsFiniteGlobalDimensionRing R := by
  simpa using
    (residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae).out 2 1

variable [IsRegularLocalRing R]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Every localization of a regular local ring at a prime ideal is again a regular local ring. -/
theorem isRegularLocalRing_localizationAtPrime (p : PrimeSpectrum R) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  -- Route correction: prove the localization theorem directly through finite global dimension,
  -- instead of routing through the moved `IsRegularRing` instance.
  let _ : IsFiniteGlobalDimensionRing R :=
    (isRegularLocalRing_iff_isFiniteGlobalDimensionRing (R := R)).1 inferInstance
  rcases (inferInstance : IsFiniteGlobalDimensionRing R).exists_bound with ⟨n, hn⟩
  let _ : HasGlobalDimensionLE R n := hn
  let _ : HasGlobalDimensionLE (Localization.AtPrime p.asIdeal) n := inferInstance
  let hlocalized : IsFiniteGlobalDimensionRing (Localization.AtPrime p.asIdeal) := ⟨⟨n, inferInstance⟩⟩
  exact
    (isRegularLocalRing_iff_isFiniteGlobalDimensionRing
      (R := Localization.AtPrime p.asIdeal)).2 hlocalized

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Chap10 Definition 10 110 7 companion: a regular local ring is regular in the global sense. -/
instance isRegularRing_of_isRegularLocalRing : IsRegularRing R where
  toIsNoetherian := inferInstance
  -- Every prime localization inherits regular-locality from the ambient regular local ring.
  isRegularLocalRing_atPrime := isRegularLocalRing_localizationAtPrime

end
