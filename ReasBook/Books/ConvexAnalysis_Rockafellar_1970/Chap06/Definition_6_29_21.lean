import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.21 says that the convex program `(P)` attached to a bifunction
  `F` is strongly consistent when the origin belongs to the relative interior of the bifunction
  domain, written in the source as `0 ∈ ri (dom F)`.
- `core/canonical`: the chapter already owns this notion as `Bifunction.IsStronglyConsistent 𝕜 F`
  from Definition 6.29.10.
- `bridge/view`: the source wording is already the canonical specification theorem
  `Bifunction.isStronglyConsistent_iff`, with `ri[𝕜](·)` just the chapter notation for
  `intrinsicInterior`.

Domain-style sampling used here:
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_10`;
- `Bifunction.isStronglyConsistent_iff` from `Definition_6_29_10`;
- `intrinsicInterior` as the mathlib owner for relative interior.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` with ordered-top codomain data;
- primitive owner: `IsStronglyConsistent 𝕜 F`;
- derived API: the source-facing spelling `(0 : U) ∈ ri[𝕜](dom F)` of the owner theorem.

Layer target: `core/canonical` recall of the owner and its existing specification theorem, with no
parallel local wrapper.
-/

/- Definition 6.29.21: the strong-consistency notion for the convex program associated with a
bifunction `F` is the already existing owner `Bifunction.IsStronglyConsistent 𝕜 F`; the source
condition `0 ∈ ri (dom F)` is rendered here as `(0 : U) ∈ ri[𝕜](dom F)`. -/
recall IsStronglyConsistent

/- Definition 6.29.21, source-facing specification: the canonical owner theorem is already
`Bifunction.isStronglyConsistent_iff`. -/
recall isStronglyConsistent_iff

end Bifunction
