import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.12 records three basic order properties of the Chapter 7 closure
  operator: `cl(f) ≤ f`, monotonicity under pointwise order, and preservation of the global
  infimum.
- `core/canonical`: the owner construction is `lowerSemicontinuousHull`, written `cl(·)`, and the
  corresponding owner theorems now all live upstream in `Text_7_0_4`.
- `bridge/view`: this item contributes no new owner data or wrapper layer; it is a direct
  source-facing recall of the canonical closure-order API.

Domain-style sampling used here:
- `lowerSemicontinuousHull_le`;
- `lowerSemicontinuousHull_mono`;
- `iInf_lowerSemicontinuousHull_eq_iInf`.

Primitive data vs derived API:
- primitive owner data: a function `f : α → WithBotTop 𝕜`;
- derived API: the pointwise minorant property, monotonicity of `cl(·)`, and the `iInf`
  invariance already exposed by the owner file.

Layer target: `bridge/view`. This file is a direct canonical recall surface for the three source
clauses rather than a second home for owner theorems.
-/

/- Text 7.0.12 (1): for every extended-codomain function, the closure `cl(f)` is pointwise
majorized by `f`. This is exactly the canonical owner theorem
`lowerSemicontinuousHull_le`. -/
recall lowerSemicontinuousHull_le

/- Text 7.0.12 (2): the closure operator `cl(·)` is monotone with respect to pointwise order.
This is the canonical owner theorem `lowerSemicontinuousHull_mono`. -/
recall lowerSemicontinuousHull_mono

/- Text 7.0.12 (3): taking the closure `cl(f)` preserves the global infimum of an
extended-codomain function. This is the canonical owner theorem
`iInf_lowerSemicontinuousHull_eq_iInf`. -/
recall iInf_lowerSemicontinuousHull_eq_iInf

end
