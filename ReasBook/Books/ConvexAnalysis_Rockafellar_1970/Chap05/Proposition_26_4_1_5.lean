import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 26.4.1.5 says that for a closed proper convex function `f`, the
  multivalued subdifferential `∂f` is one-to-one if and only if the restriction
  `(riDom(f), f.realBranch)` is of Legendre type.
- `core/canonical`: the project already owns this content as the theorem
  `biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom`, built from the canonical
  relation owner `(_root_.subdifferentialGraph f).BiUnique` and the Chapter 26 owner
  `Function.IsLegendreTypeOn`.
- `bridge/view`: this numbered proposition adds no new primitive data beyond that earlier theorem;
  it is only a textbook-location recall of the same owner-level statement.

Domain-style sampling used here:
- `Function.IsLegendreTypeOn` from `Definition_26_4_1_4`;
- `biUnique_subdifferentialGraph_iff_strictConvexOn_interior_dom_and_isEssentiallySmooth` from
  `Corollary_26_3_1`;
- `(_root_.subdifferentialGraph f).BiUnique` from `Definition_26_0_3`;
- `Function.realBranch` together with the domain owner `dom(f)`.

Primitive data vs derived API:
- primitive source input: a closed proper convex function `f`;
- primitive owner surface: bi-uniqueness of `_root_.subdifferentialGraph f` and the Legendre-type
  predicate on `riDom(f)`;
- derived API here: none. The earlier theorem already has the exact target interface.

Layer target: `bridge/view`. This file is a direct canonical recall rather than a second
exact-interface theorem shell.
-/

/- Proposition 26.4.1.5 is exactly the earlier chapter theorem
`biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom`; this file reuses that canonical owner
result directly instead of maintaining a parallel theorem name. -/
recall biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom
