import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.7 introduces the terminology that the set-valued map
  `x ↦ ∂g(x)` is the subdifferential of `g`.
- `core/canonical`: the chapter's intrinsic owner for this map is
  `_root_.concaveSubdifferentialAt` from `Definition_6_30_5`.
- `bridge/view`: `Function.concaveSubdifferentialAt` is the Fréchet-Riesz Euclidean
  specialization of that intrinsic owner.
- this item adds no new mathematical data beyond those existing owners, so the correct
  statement-stage entry is direct recall rather than a fresh alias.

Domain-style sampling:
- `_root_.concaveSubdifferentialAt` and `_root_.mem_concaveSubdifferentialAt` from
  `Definition_6_30_5`;
- `Function.concaveSubdifferentialAt`, the Euclidean bridge owner from the same file.

Layer target: `source-facing` terminology recall of the intrinsic owner, together with its
Euclidean bridge recall.
-/

/- Definition 6.30.7, intrinsic owner form: the set-valued mapping
`x ↦ _root_.concaveSubdifferentialAt g x` is called the subdifferential of `g`. -/
recall concaveSubdifferentialAt

namespace Function

/- Definition 6.30.7, Euclidean bridge form: in inner-product coordinates, the source's
set-valued map is `x ↦ Function.concaveSubdifferentialAt g x`. -/
recall concaveSubdifferentialAt

end Function
