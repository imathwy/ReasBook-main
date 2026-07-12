import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap18.Lemma_18_28_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 17.17.5:
- primary domain: closure of flat module sheaves under filtered colimits and coproducts;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered`,
  `SheafOfModules.RingedSite.isFlat_coproduct`,
  `SheafOfModules.isFlat_stalk`,
  `RingedSpace.Modules`;
- best owner abstraction: flatness is owned by
  `SheafOfModules.RingedSite.IsFlat X.sheaf` on `X.Modules`, and the closure results are already
  owned upstream by the Chapter 18 site-level theorems specialized to `X.sheaf`;
- primitive data: a diagram of sheaves of modules on `X` whose objects are all flat;
- derived API: the filtered-colimit and coproduct closure theorems below.

Source/core/bridge triage:
- `source-facing`: flatness is preserved by filtered colimits and direct sums;
- `core/canonical`: `X.Modules`, `SheafOfModules.RingedSite.IsFlat X.sheaf`, and the Chapter 18
  owner theorems `SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered` and
  `SheafOfModules.RingedSite.isFlat_coproduct`;
- `bridge/view`: the ringed-space specialization of those site-level closure results.

This file should therefore be recall-only: the ringed-space case is obtained by specializing the
canonical Chapter 18 owner theorems, so no parallel Chapter 17 theorem names should remain.
-/

/- Lemma 17.17.5 (1): a filtered colimit of flat `\mathcal O_X`-modules is flat. This is exactly
the ringed-space specialization of the canonical owner theorem
`SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered`. -/
recall SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered

/- Lemma 17.17.5 (2): a direct sum of flat `\mathcal O_X`-modules is flat. This is exactly the
ringed-space specialization of the canonical owner theorem
`SheafOfModules.RingedSite.isFlat_coproduct`. -/
recall SheafOfModules.RingedSite.isFlat_coproduct
