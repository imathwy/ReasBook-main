import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 17.10.1:
- primary domain: sheaves of modules on ringed spaces and the quasi-coherence predicate on
  `\mathcal O_X`-modules;
- sampled owner declarations:
  `SheafOfModules.QuasicoherentData`,
  `SheafOfModules.QuasicoherentData.isQuasicoherent`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.isQuasicoherent`;
- best owner abstraction: the mathlib owner class `SheafOfModules.IsQuasicoherent`;
- primitive data: local presentation data on a covering family, packaged upstream by
  `SheafOfModules.QuasicoherentData`;
- derived API: the object-property view `SheafOfModules.isQuasicoherent` and the canonical
  instance-valued predicate on a sheaf of modules.

Source/core/bridge triage:
- `source-facing`: quasi-coherence of a sheaf of `\mathcal O_X`-modules;
- `core/canonical`: `SheafOfModules.IsQuasicoherent`;
- `bridge/view`: `SheafOfModules.QuasicoherentData.isQuasicoherent` and the object-property alias
  `SheafOfModules.isQuasicoherent`.

This item is a canonical recall item: the notion is already owned upstream, so the file should
reuse that owner directly rather than introducing a chapter-local wrapper around the local
presentation data.
-/

/- Definition 17.10.1: a quasi-coherent sheaf of `\mathcal O_X`-modules is the canonical
predicate `SheafOfModules.IsQuasicoherent`, expressing that locally it is the cokernel of a
morphism between coproducts of copies of the structure sheaf. -/
recall SheafOfModules.IsQuasicoherent
