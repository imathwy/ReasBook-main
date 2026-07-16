import stacks_proof.stacks_project.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Domain-style sampling for the Cohen-Macaulay local-ring condition:
- primary domain: Cohen-Macaulay modules and their self-module specialization over Noetherian
  local rings;
- sampled owner declarations:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `Module.MaximalCohenMacaulay`,
  `Module.LocallyCohenMacaulay`;
- best owner abstraction: `Module.CohenMacaulay R R`;
- primitive data: exactly the owner data already carried by `Module.CohenMacaulay R R`;
- derived API: the field projection
  `Module.CohenMacaulay.supportDim_eq_moduleDepth` and the later global owner
  `Module.LocallyCohenMacaulay R R`.

Source/core/bridge triage:
* source-facing: Definition 10.104.1 is the local-ring specialization of the Cohen-Macaulay
  module condition;
* core/canonical: `Module.CohenMacaulay R R`;
* bridge/view: none, since the source item adds no extra data beyond the self-module
  specialization.

A separate ring-level alias here would only duplicate the owner abstraction and create a parallel
API surface.
-/
/- Definition 10.104.1: a Noetherian local ring is Cohen-Macaulay if it is Cohen-Macaulay as a
module over itself. -/
#check (Module.CohenMacaulay R R)

end
