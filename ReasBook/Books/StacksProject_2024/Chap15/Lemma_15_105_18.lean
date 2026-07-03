import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap15.Definition_15_105_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (A : Type u) [CommRing A]

/- Domain-style sampling:
- primary domain: commutative algebra of weak dimension, flatness criteria for ideals and
  submodules, and the valuation-ring criterion on prime localizations;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `Module.Flat`,
  `ValuationRing`,
  `ValuationRing.iff_local_bezout_domain`;
- best owner abstraction: clause `(1)` should use the chapter owner `HasWeakDimensionLE A 1`,
  clauses `(2)` through `(4)` should stay as the source-facing flatness conditions on ideals and
  `A`-modules, with clause `(4)` quantified over the canonical owner `ModuleCat A`; clause `(5)`
  should use the canonical mathlib owner `ValuationRing` directly rather than a one-off local
  wrapper;
- primitive vs. derived:
  primitive data is only the ring `A` together with the owner predicates on ideals, submodules,
  and prime localizations;
  derived API is the TFAE bridge among these five formulations, so no extra public packaging is
  warranted here.

Source/core/bridge triage:
- `source-facing`: the five-way equivalence matching the Stacks lemma;
- `core/canonical`: `HasWeakDimensionLE`, `Module.Flat`, `PrimeSpectrum`, `Localization.AtPrime`,
  and `ValuationRing`;
- `bridge/view`: the theorem itself, whose last clause presents the Stacks “`A_p` is a valuation
  ring” wording via the minimal existential witness needed to supply the domain instance required
  by the canonical owner `ValuationRing`.
-/

-- Proof sketch: `(1) → (2)` uses the short exact sequence `0 → I → A → A ⧸ I → 0` and the
-- characterization of weak dimension `≤ 1` by vanishing of higher tors. `(2) ↔ (3)` is the
-- filtered-colimit argument reducing arbitrary ideals to finitely generated ones. `(2) → (4)`
-- writes a flat module as a filtered colimit of finite free modules and filters submodules by
-- ideals. `(4) → (1)` resolves an arbitrary module by a free module with flat kernel. `(1) → (5)`
-- localizes weak dimension `≤ 1` and uses the local criterion that finitely generated flat ideals
-- in a local ring are principal, giving a valuation ring on each canonical prime localization.
-- `(5) → (3)` checks finitely generated ideals after localizing at primes and applies the local
-- criterion for flatness.
/-- Lemma 15.105.18: for a commutative ring `A`, the following are equivalent: `A` has weak
dimension at most `1`; every ideal of `A` is flat; every finitely generated ideal of `A` is flat;
every submodule of a flat `A`-module is flat; and every localization `Aₚ` at a prime ideal is a
valuation ring. -/
theorem weakDimensionLEOne_idealFlat_fgIdealFlat_submoduleFlat_localizations_valuationRing_tfae :
    List.TFAE
      [ HasWeakDimensionLE A 1
      , ∀ I : Ideal A, Module.Flat A I
      , ∀ I : Ideal A, I.FG → Module.Flat A I
      , ∀ (M : ModuleCat.{v} A) [Module.Flat A M] (N : Submodule A M),
          Module.Flat A N
      , ∀ p : PrimeSpectrum A,
          ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
            ValuationRing (Localization.AtPrime p.asIdeal)
      ] := sorry

end
