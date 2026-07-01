import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 17.11.1:
- primary domain: sheaves of modules on ringed spaces and the finite-presentation predicate on
  `\mathcal O_X`-modules;
- sampled canonical owner declarations:
  `SheafOfModules.QuasicoherentData`,
  `SheafOfModules.QuasicoherentData.IsFinitePresentation`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.isFinitePresentation`;
- best owner abstraction: the mathlib owner class `SheafOfModules.IsFinitePresentation`;
- primitive data: local presentation data on a covering family, packaged upstream by
  `SheafOfModules.QuasicoherentData` and its finite-presentation predicate;
- derived API: the object-property form `SheafOfModules.isFinitePresentation` and the canonical
  instances from finite presentation to quasi-coherence and finite type;
- source/core/bridge triage:
  `core/canonical`: `SheafOfModules.IsFinitePresentation`,
  `bridge/view`: `SheafOfModules.isFinitePresentation`.

This item is a canonical recall item: the source-facing notion is already owned upstream, so this
file should reuse that owner directly rather than introducing a ringed-space-local wrapper around
the local finite-presentation data.
-/

/- Definition 17.11.1: for a sheaf of `\mathcal O_X`-modules on a ringed space, being of finite
presentation is the canonical predicate `SheafOfModules.IsFinitePresentation`, defined upstream by
local finite presentations on a covering family of opens and matching the neighbourhood
formulation in the text. -/
recall SheafOfModules.IsFinitePresentation
