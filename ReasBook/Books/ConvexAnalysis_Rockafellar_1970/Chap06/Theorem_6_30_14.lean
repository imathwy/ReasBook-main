import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

/-!
Source/core/bridge triage:

- `source-facing`: Section 30, item 6.30.14 is the adjoint bifunction attached to a bifunction
  `F`, not a separate theorem-level identity.
- `core/canonical`: that owner already lives in
  `ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14` as
  `Bifunction.adjoint`.
- `bridge/view`: the pointwise and zero-slice formulas are already the companion API
  `Bifunction.adjoint_apply` and `Bifunction.objective_adjoint_apply` in the same owner file.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.adjoint_apply` from `Definition_6_30_14`;
- `Bifunction.objective_adjoint_apply` from `Definition_6_30_14`.

Primitive data vs derived API:
- primitive owner for item 6.30.14: `Bifunction.adjoint`;
- derived API already upstream: its pointwise and zero-slice evaluation lemmas;
- no additional theorem-level owner belongs in this file.

Layer target: `core/canonical recall/use`.
-/

/- Section 30, item 6.30.14 is already formalized by the canonical owner
`Bifunction.adjoint` in `Definition_6_30_14`. There is no separate theorem declaration here. -/
recall Bifunction.adjoint
