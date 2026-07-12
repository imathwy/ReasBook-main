import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Definition_17_28_3

/- Domain-style sampling for Lemma 17.28.4:
- primary domain: sheafified relative differentials of sheaves of commutative rings on a
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_def`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- best owner abstraction: the source-facing owner `TopCat.Sheaf.relativeDifferentials`;
- primitive data: the owner `TopCat.Sheaf.relativeDifferentials` itself;
- derived API: its defining sheafification equation
  `TopCat.Sheaf.relativeDifferentials_def`.

Source/core/bridge triage:
- `source-facing`: `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: `TopCat.Sheaf.relativeDifferentials_def`;
- this file is a recall-only reuse of the owner theorem from `Definition_17_28_3`, not a second
  owner declaration. -/

/- Lemma 17.28.4: the sheaf of relative differentials `Ω_{O₂/O₁}` on a topological space is
already canonically owned by `TopCat.Sheaf.relativeDifferentials`, and its associated-sheaf
presentation is exactly `TopCat.Sheaf.relativeDifferentials_def`. -/
recall TopCat.Sheaf.relativeDifferentials_def
