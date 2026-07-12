import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.1 identifies convex processes with multivalued mappings whose
  graphs are convex cones containing the origin.
- `core/canonical`: Definition 39.0.1 already chose the correct owner
  `SetRel.IsConvexProcess R A` on the relation graph `A : SetRel U X`.
- `bridge/view`: the textbook graph `graph A` is just the relation set `A : Set (U × X)`, and the
  graph-side criterion is the canonical bridge
  `SetRel.isConvexProcess_iff`.

Domain-style sampling used here:
- `SetRel` and graph membership notation from `Mathlib.Data.Rel`;
- `Set.IsConvexCone` from `Chap01.Definition_2_5_10`;
- `SetRel.IsConvexProcess` and its canonical iff bridge theorem from
  `Chap08.Definition_39_0_1`.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive owner predicate: `A.IsConvexProcess R`;
- bridge graph view: `Set.IsConvexCone R A` together with `(0 : U) ~[A] (0 : X)`.

Layer target: `bridge/view`. The proposition is an exact graph-side characterization of the
canonical owner and therefore should be reused directly rather than wrapped in a parallel theorem.

Abstraction checks for this item:
- Codomain/ambient concreteness: no ordered-extended codomain owner is introduced here; this file
  only recalls the relation-graph characterization already owned upstream.
- Scalar/ambient structure: no concrete scalar or model specialization is fixed in this file; the
  reused owner remains parametric in `R`, `U`, and `X` under the canonical assumptions from
  `SetRel.IsConvexProcess`.
- Owner choice: the intrinsic owner is `A.IsConvexProcess R` on `SetRel`; no extra local wrapper
  theorem is introduced.
- Topology language: not applicable; the proposition has no ambient/intrinsic topology surface.
- Owner naming/notation: keep the short canonical owner and its canonical iff bridge
  `SetRel.isConvexProcess_iff` directly.
-/

/- Proposition 39.0.1: a multivalued mapping is a convex process exactly when its graph, viewed as
the relation set `A : Set (U × X)`, is a convex cone containing the origin. This is exactly the
canonical graph-side characterization for `SetRel.IsConvexProcess`. -/
recall SetRel.isConvexProcess_iff
