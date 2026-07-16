import Mathlib
import StacksProject_2024.stacks_project.Chap14.Definition_14_28_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.
open CategoryTheory.CosimplicialObject

/- Domain-style sampling for 14.28.1.1:
- primary domain: naturality of the degreewise components of a cosimplicial `Δ[1]`-homotopy;
- inspected owner declarations:
  `CategoryTheory.homFromSimplicialSet`,
  `CategoryTheory.homFromSimplicialSet_map_π`,
  `CategoryTheory.CosimplicialObject.Homotopy`,
  `CategoryTheory.CosimplicialObject.Homotopy.naturality`,
  `CategoryTheory.CosimplicialObject.Homotopy.app`;
- owner abstraction: the source-facing chapter owner is `Homotopy a b`, while
  `homFromSimplicialSet` is the ambient cotensor owner and `homFromSimplicialSet_map_π` is the
  core bridge theorem used to derive the degreewise naturality square;
- primitive data: the homotopy object `H : Homotopy a b`;
- derived API: evaluation `H.app α` at a simplex `α : Δ[1]_n` and its naturality square;
- layer for this file: `source-facing`.

Source/core/bridge triage:
- `source-facing`: the naturality of the degreewise components `h_{n,α}` of a cosimplicial
  `Δ[1]`-homotopy;
- `core/canonical`: the owner theorem `Homotopy.naturality`;
- `bridge/view`: the simplicial cotensor owner `homFromSimplicialSet` together with the
  projection-square theorem `homFromSimplicialSet_map_π` used internally in
  `Definition_14_28_1`.
-/

/- 14.28.1.1 is the source-facing naturality theorem for the degreewise components of a
cosimplicial `Δ[1]`-homotopy. -/
recall Homotopy.naturality
