import Mathlib
import Mathlib.Tactic.TFAE
import stacks_project.Chap10.Lemma_10_110_2
import stacks_project.Chap10.Lemma_10_110_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: homological and local characterizations of regular Noetherian rings;
* sampled owner declarations:
  `IsFiniteGlobalDimensionRing`,
  `IsRegularRing`,
  `globalDimension`,
  `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal`,
  `isRegularLocalRing_iff_isFiniteGlobalDimensionRing`;
* best owner abstraction: the core owners are `IsFiniteGlobalDimensionRing R` and
  `IsRegularRing R`; the fixed-`n` statements in this file should therefore use those owners
  directly, with only the equalities and localization bounds kept as source-facing clauses;
* primitive data vs. derived API: the owner predicates above are primitive, while the four fixed-
  `n` textbook clauses are derived API;
* source/core/bridge triage:
  `source-facing`: the fixed-`n` TFAE theorem and its four textbook clauses;
  `core/canonical`: `IsFiniteGlobalDimensionRing R`, `IsRegularRing R`, and the local equality
    theorem from Proposition `10.110.5`;
  `bridge/view`: the maximal-local finite-global-dimension criterion
    `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal` and the local
    equivalence `isRegularLocalRing_iff_isFiniteGlobalDimensionRing`.
-/

-- Proof sketch: apply the canonical maximal-local criterion
-- `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal` and the local
-- equivalence `isRegularLocalRing_iff_isFiniteGlobalDimensionRing` to each localization
-- `Localization.AtPrime m.asIdeal`. Proposition `10.110.5` identifies the corresponding local
-- global dimensions with local Krull dimensions, and Definition `10.110.7` upgrades the resulting
-- primewise regularity to `IsRegularRing R`. The equalities at some maximal or prime localization
-- then pin down the common integer `n`.
/-- Lemma 10.110.8: for a Noetherian ring `R`, the following are equivalent: `R` has finite global
dimension `n`, `R` is a regular ring of dimension `n`, every localization at a maximal ideal is a
regular local ring of dimension at most `n` with equality for at least one maximal ideal, and
every localization at a prime ideal is a regular local ring of dimension at most `n` with
equality for at least one prime ideal. -/
theorem finiteGlobalDimension_regularRing_localizations_tfae (n : ℕ) :
    List.TFAE
      [ ∃ _ : IsFiniteGlobalDimensionRing R, globalDimension R = n
      , IsRegularRing R ∧ ringKrullDim R = n
      , (∀ m : MaximalSpectrum R,
            IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
              ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
          ∃ m : MaximalSpectrum R, ringKrullDim (Localization.AtPrime m.asIdeal) = n
      , (∀ p : PrimeSpectrum R,
            IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
              ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
          ∃ p : PrimeSpectrum R, ringKrullDim (Localization.AtPrime p.asIdeal) = n ] := sorry

end
