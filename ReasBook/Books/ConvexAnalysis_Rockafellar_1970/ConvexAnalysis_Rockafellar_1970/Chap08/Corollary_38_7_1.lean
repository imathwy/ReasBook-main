import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_7_1

/-!
Corollary 38.7.1 is already owned upstream by
`ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_7_1`.

Layer triage:
- `source-facing`: the textbook corollary is the fixed-dual-point specialization of the Chapter 38
  image/adjoint duality bridge.
- `core/canonical`: the owner declarations are
  `Bifunction.hasInnerProduct_adjointFunction_of_common_riDom` and
  `Bifunction.convexConjugate_image_eq_innerProduct_adjointFunction_of_common_riDom`.
- `bridge/view`: this file contributes only the source label, so it should be a pure recall bridge
  rather than a second local theorem family specialized to the self-dual `EReal` setting.

Primitive data vs derived API:
- primitive owner layer: `Bifunction.image`, `Bifunction.adjoint`, `Function.HasInnerProduct`, and
  `Function.innerProduct`, already used directly by the owner file;
- derived API here: none beyond re-exposing the existing canonical owner theorems under the
  textbook item label.
-/

/- Corollary 38.7.1, existence clause: reuse the canonical owner theorem directly. -/
recall Bifunction.hasInnerProduct_adjointFunction_of_common_riDom

/- Corollary 38.7.1, equality clause: reuse the canonical owner theorem directly. -/
recall Bifunction.convexConjugate_image_eq_innerProduct_adjointFunction_of_common_riDom
