import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Lemma_13_9_10

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage for Lemma 22.8.1:
- primary domain: triangles in the homotopy category of differential graded `A`-modules attached
  to admissible short exact sequences, and the independence of that triangle from the chosen
  degreewise splitting in the canonical cochain-complex model;
- inspected owner declarations:
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.trianglehOfDegreewiseSplit_iso_of_splittings`;
- best owner abstraction: this numbered item is a recall-only bridge statement, so the main public
  entry should be the existing Chapter 13 canonical comparison
  `CochainComplex.trianglehOfDegreewiseSplit_iso_of_splittings`, not a duplicate local wrapper;
- source/core/bridge triage:
  `source-facing`: the associated triangle `K ⟶ L ⟶ M ⟶ K[1]` of an admissible short exact
    sequence is independent of the chosen degreewise splitting;
  `core/canonical`: the owner triangle `CochainComplex.trianglehOfDegreewiseSplit`;
  `bridge/view`: the identity-on-terms comparison
    `CochainComplex.trianglehOfDegreewiseSplit_iso_of_splittings`;
- derived API: the termwise split owner construction and the comparison isomorphism remain in
  Chapter 13 and are reused directly here.
-/

/- Lemma 22.8.1: for an admissible short exact sequence of differential graded `A`-modules,
represented in the canonical cochain-complex model by a short exact complex with two degreewise
splitting choices, the associated triangle `K ⟶ L ⟶ M ⟶ K[1]` is independent of those choices
up to the canonical identity-on-objects isomorphism in the homotopy category. This source-facing
independence statement is exactly the canonical owner
`CochainComplex.trianglehOfDegreewiseSplit_iso_of_splittings`. -/
recall CochainComplex.trianglehOfDegreewiseSplit_iso_of_splittings
