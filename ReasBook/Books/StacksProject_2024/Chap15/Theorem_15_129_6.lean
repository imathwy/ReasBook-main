import StacksProject_2024.Chap10.Lemma_10_85_2
import StacksProject_2024.Chap15.Lemma_15_129_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

open Module

/- Domain triage:
- primary domain: projective modules, countable generation, and freeness criteria via free
  and stably free direct summands;
- sampled owner declarations:
  `Module.CountablyGenerated`,
  `exists_finiteStablyFree_directSummand_submodule_containing`,
  `exists_perturbation_with_cyclicSpan_free_directSummand`,
  and `Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty`;
- `source-facing`: the numbered theorem is the Chapter 15 freeness statement for one countably
  generated projective module under the maximal-localization infinite-rank hypothesis;
- `core/canonical`: the ambient owners are `Module.CountablyGenerated R P` and `Module.Free R P`;
- `bridge/view`: Lemma `15.129.5` gives the source-facing finite stably free summands, and
  Lemma `15.129.4` is the free rank-one splitting step used in the Stacks proof to upgrade those
  summands to a countable free decomposition.

Primitive data are the ambient projective module `P`, the countable-generation hypothesis, and the
local maximal-ideal non-finiteness condition. The Chapter 10 owner
`Module.HasFiniteFreeComplementSummandProperty R P` is stronger than Lemma `15.129.5` and is not
the direct output of Lemma `15.129.5`, so the source-facing theorem should remain the main public
entry while this file provides a separate bridge to that owner. The maximal-local condition should
still use the chapter’s canonical `MaximalSpectrum R` indexing rather than an `Ideal` parameter
with a hidden `[IsMaximal]` binder. -/

namespace Module

/-- Bridge from the Chapter 15 maximal-local hypothesis to the Chapter 10 owner
`HasFiniteFreeComplementSummandProperty`. This packages the repeated finite-summand splitting
argument needed to invoke Lemma `10.85.2`, while keeping the source-facing freeness theorem below
as the main public statement for Theorem `15.129.6`. -/
theorem hasFiniteFreeComplementSummandProperty_of_localizations_not_finite
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    HasFiniteFreeComplementSummandProperty R P := by
  sorry

end Module

-- Proof sketch: first pass from the maximal-local hypothesis to the Chapter 10 owner
-- `Module.HasFiniteFreeComplementSummandProperty R P` via the bridge theorem above, then apply
-- Lemma `10.85.2`.
/-- Theorem 15.129.6: if `R ⧸ Ring.jacobson R` is Noetherian and `P` is a countably generated
projective `R`-module whose localizations at maximal ideals are not finitely generated, then `P`
is free. This is the Lean rendering of the condition that each `P_𝔪` has infinite rank. -/
theorem free_of_countablyGenerated_projective_of_localizations_not_finite
    (hcg : CountablyGenerated R P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    Free R P := by
  exact Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty hcg
    (Module.hasFiniteFreeComplementSummandProperty_of_localizations_not_finite hnotFiniteAtMax)

end
