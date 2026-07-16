import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

/-!
Source/core/bridge triage:

- `source-facing`: Remark 7.0.21 observes that the chapter closure operator `cl(·)` acts as a
  normalization in convex analysis: it produces the lower-semicontinuous representative, and
  closed-epigraph functions are precisely fixed points of that normalization.
- `core/canonical`: the owner abstraction is the Chapter 2 closure operator
  `lowerSemicontinuousHull`, written `cl(·)`.
- `bridge/view`: the fixed-point sentence of the remark is already the upstream theorem
  `cl_eq_self_of_isClosed_epi`, derived from the epigraph-closure owner API.

Domain-style sampling used here:
- `lowerSemicontinuousHull` from `Text_7_0_4`;
- `closure_epi_eq_epi_lowerSemicontinuousHull` from `Text_7_0_4`;
- `cl_eq_self_of_isClosed_epi` from `Text_7_0_4`.

Primitive data vs derived API:
- primitive datum: a function `f`;
- owner abstraction: the closure operator `cl(f) = lowerSemicontinuousHull f`;
- derived API: the closed-epigraph fixed-point statement, which should be recalled directly rather
  than restated through a parallel local wrapper.

Layer target: `bridge/view`. This remark does not define new mathematical data, so the canonical
form is a direct recall of the existing owner theorem instead of a local alias or `_iff`
reformulation.
-/

/- Remark 7.0.21: the fixed-point clause for the chapter closure operator is the canonical theorem
`cl_eq_self_of_isClosed_epi`. -/
recall cl_eq_self_of_isClosed_epi

end
