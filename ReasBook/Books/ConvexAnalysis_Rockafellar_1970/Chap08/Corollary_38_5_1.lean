import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.5.1 is the closed-case companion to Theorem 38.5 for the product
  `GF`, asserting closedness of `GF`, pointwise attainment of the defining infimum, and the
  adjoint-side closure identity `(GF)^* = cl(F^* G^*)`.
- `core/canonical`: the owner declarations already present in the chapter are the product owner
  `Bifunction.comp`, `Bifunction.adjoint`, `Bifunction.inverse`, `Bifunction.dom`,
  `Bifunction.IsProper`, `Bifunction.IsClosedConvex`, `Bifunction.closure`, and the canonical
  Corollary 38.5.1 theorem family already recorded in `Items/Chap08/Proposition_38_5_1.lean`.
- `bridge/view`: this file contributes no new mathematics beyond those existing source-facing
  owner theorems, so it should reuse them directly instead of maintaining a second wrapper API.

Primary mathematical domain:
- composition of closed proper convex bifunctions and the adjoint-side closure formula.

Domain-style sampling used here:
- `Bifunction.comp` from `Theorem_38_5`;
- `Bifunction.adjoint` from the Chapter 6 duality owner layer;
- `Bifunction.closure` from `Definition_6_29_24`;
- the canonical Corollary 38.5.1 theorem family in `Proposition_38_5_1`.

Primitive data vs derived API:
- primitive source data: closed proper convex bifunctions `F : U → X → EReal` and
  `G : X → Y → EReal`;
- primitive owner layer: the existing chapter owners `comp G F`, `adjoint`, `inverse`,
  `dom`, and `closure`;
- derived API: closedness of `comp G F`, pointwise attainment of its defining infimum, and the
  adjoint-side closure identity.

Layer target: `bridge/view`. This file reuses the existing source-facing owner theorems directly
instead of maintaining renamed local copies.
-/

/- Corollary 38.5.1 is already recorded upstream on the canonical `Bifunction` owners. -/
recall isClosedConvex_comp_of_common_riDom_adjoint_inverse

recall exists_eq_comp_of_common_riDom_adjoint_inverse
recall adjointFunction_comp_eq_closure_comp_adjointFunction_of_common_riDom_adjoint_inverse
