import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_22_2

namespace CategoryTheory

/- Domain-style sampling for Lemma 20.35.2:
- primary domain: sheaf cohomology of sequential inverse systems of `A`-module sheaves, with the
  source eventual ranges `N_n` formed from the towers `m ↦ H^{p+1}(X, I^n \mathcal F_{m+1})`;
- sampled owner declarations:
  * `CategoryTheory.CommSq`;
  * `CategoryTheory.siteModuleCohomologyIdealPowerEventualRange`;
  * `CategoryTheory.siteModuleCohomologyTower`;
  * `CategoryTheory.site_module_cohomology_tower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition`;
- owner choice:
  * `source-facing`: the source eventual-range terms `N_n` and the square compatibility of the
    ideal-power rows;
  * `core/canonical`: `CommSq`, `siteModuleCohomologyIdealPowerEventualRange`,
    `siteModuleCohomologyTower`, and the site-level owner theorem from
    `Chap21/Lemma_21_22_2.lean`;
  * `bridge/view`: none beyond specializing the generic site parameter to
    `Opens.grothendieckTopology X` for a topological space `X`.
- primitive data: the ideal `I`, the towers `ℱ` and `powSheaf`, the maps
  `I^n \mathcal F_{m+1} → \mathcal F_{m+1}`, their short exact rows, and their compatibility
  squares;
- derived API: the eventual-range additive subgroup
  `siteModuleCohomologyIdealPowerEventualRange powSheaf p n` and the resulting Mittag-Leffler
  statement for `siteModuleCohomologyTower ℱ p`.

This file is recall-only after refinement: the Chapter 21 owner theorem now already uses the
canonical `CommSq` naturality hypothesis, so Lemma 20.35.2 adds no second owner or wrapper theorem
beyond the topological-space specialization of that site-level statement.
-/

/- Lemma 20.35.2 uses the canonical eventual-range term
`siteModuleCohomologyIdealPowerEventualRange` for
`N_n = \bigcap_{m \ge n} \operatorname{im}(H^{p+1}(X, I^n \mathcal F_{m+1}) →
  H^{p+1}(X, I^n \mathcal F_{n+1}))`. -/
recall siteModuleCohomologyIdealPowerEventualRange

/- Lemma 20.35.2 uses the canonical cohomology tower `n ↦ H^p(X, \mathcal F_n)`, formalized by
`siteModuleCohomologyTower`. -/
recall siteModuleCohomologyTower

/- The square compatibility in Lemma 20.35.2 is expressed by the canonical owner `CommSq`. -/
recall CommSq

/- Lemma 20.35.2 itself is the site-level owner theorem
`site_module_cohomology_tower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition`
specialized to the site of opens of a topological space; this chapter file only recalls that
canonical statement and does not introduce a second topological-space wrapper. -/
recall site_module_cohomology_tower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition

end CategoryTheory
