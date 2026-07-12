import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_8

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.10 says that the concave program attached to a concave
  bifunction `G` maximizes the zero slice `G₀`, and that its perturbations are obtained by
  replacing `G₀` with the slices `Gᵤ`.
- `core/canonical`: the zero-slice owner is already `Bifunction.objective` from
  Definition 6.29.12, while the perturbation family is just the given bifunction `G` itself.
- `bridge/view`: no new program wrapper or maximization-objective alias should be introduced
  here; the source notion is exactly the existing zero-slice owner together with the existing
  family of slices.

Domain-style sampling used here:
- `concᵇ[𝕜](G)` from `Definition_6_30_8`;
- `Bifunction.objective`;
- `Bifunction.objective_apply`;
- the generic bifunction-slice surface `G u`.

Primitive data vs derived API:
- primitive source data: a concave bifunction `G : U → X → WithBotTop α` with owner
  `concᵇ[𝕜](G)`;
- canonical owner for the unperturbed objective: `objective G`;
- perturbations: the existing functions `G u`.

Layer target: `core/canonical recall/use`.
-/

namespace Bifunction

open scoped Rockafellar

/- Definition 6.30.10: the source hypothesis is that `G` is a concave bifunction, expressed on the
canonical Chapter 6 owner surface `concᵇ[𝕜](G)` from `Definition_6_30_8`. -/
recall Function.IsConcave

/- Definition 6.30.10: the associated concave program uses the existing zero-slice owner `(G)₀`
as its unperturbed objective, while perturbation objectives stay at the primitive slice surface
`G u` with no extra wrapper owner. -/
recall objective
recall objective_eq
recall objective_apply

end Bifunction
