import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.22 says that the convex program `(P)` attached to a bifunction
  `F` is strictly consistent when the origin belongs to the interior of the bifunction domain,
  written in the source as `{0} ∈ int (dom F)`.
- `core/canonical`: the chapter already owns this notion as `Bifunction.IsStrictlyConsistent F`
  from Definition 6.29.10.
- `bridge/view`: the source wording is already the canonical specification theorem
  `Bifunction.isStrictlyConsistent_iff`.

Domain-style sampling used here:
- `Bifunction.IsStrictlyConsistent` from `Definition_6_29_10`;
- `Bifunction.isStrictlyConsistent_iff` from `Definition_6_29_10`;
- `TopologicalSpace.interior` as the canonical owner for ordinary interior.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` on the codomain layer `[Top β] [LT β]`;
- primitive owner: `IsStrictlyConsistent F`;
- derived API: the source-facing spelling `0 ∈ interior (dom F)` of the owner theorem.

Abstraction checks:
- codomain/ambient layer: already at the codomain-generic owner layer used by `dom F`;
- scalar structure: none is required for strict consistency itself;
- model owner: the owner is intrinsic (`Bifunction.IsStrictlyConsistent`), not a local wrapper;
- topology phrasing: ambient `interior` is primary for strict consistency, while relative
  interior is the separate strong-consistency owner from Definition 6.29.10.

Layer target: `core/canonical` recall of the owner and its existing specification theorem, with no
parallel local wrapper.
-/

/- Definition 6.29.22: the strict-consistency notion for the convex program associated with a
bifunction `F` is the already existing owner `Bifunction.IsStrictlyConsistent F`; the source
condition `{0} ∈ int (dom F)` is rendered here as `0 ∈ interior (dom F)`. -/
recall IsStrictlyConsistent

/- Definition 6.29.22, source-facing specification: the canonical owner theorem is already
`Bifunction.isStrictlyConsistent_iff`. -/
recall isStrictlyConsistent_iff

end Bifunction
