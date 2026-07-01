import Mathlib.Tactic.Recall
import stacks_project.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 17.28.2:
- primary domain: sheafified relative differentials and their universal derivation on a
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- best owner abstraction: `TopCat.Sheaf.relativeDifferentials`, together with its universal
  derivation `TopCat.Sheaf.relativeDifferential`;
- primitive data: the sheafification of the presheaf of relative differentials and the induced
  universal derivation;
- derived API: the representing theorem
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`.

Source/core/bridge triage:
- `source-facing`: `TopCat.Sheaf.relativeDifferentials` with
  `TopCat.Sheaf.relativeDifferential`;
- this file is a recall-only reuse of the owner theorem
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`, not a second owner. -/

/- Lemma 17.28.2: the universal property of the sheaf of relative differentials on a topological
space is already owned by `TopCat.Sheaf.relativeDifferentials_representsDerivations` from Definition
`17.28.3`. -/
recall TopCat.Sheaf.relativeDifferentials_representsDerivations
