import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1

-- Declarations for this item will be appended below by the statement pipeline.

section

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.6 introduces the textbook terminology that a convex function is
  "closed" exactly when it is lower semicontinuous, equivalently when its epigraph is closed.
- `core/canonical`: the owner abstraction is `LowerSemicontinuous` on the chapter codomain layer
  `WithTopBot α`.
- `bridge/view`: the epigraph formulation is read on the chapter epigraph owner `epi` via
  `lowerSemicontinuous_iff_isClosed_epi` together with its two direction theorems.

Domain-style sampling used here:
- `LowerSemicontinuous`;
- `epi`;
- `lowerSemicontinuous_iff_isClosed_epi`;
- `isClosed_epi_of_lowerSemicontinuous`;
- `lowerSemicontinuous_of_isClosed_epi`.

Primitive data vs derived API:
- primitive datum: a function `f : E → WithTopBot α` on a topological domain;
- canonical owner: `LowerSemicontinuous f`;
- derived API: the closed-`epi` characterization.

Layer target: `bridge/view`. This item is a direct recall of the canonical owner and its epigraph
characterization, so no parallel local owner such as `Function.IsClosed` is kept.
-/

/- Text 7.0.6 uses the canonical owner `LowerSemicontinuous` for the source terminology
"closed function". -/
recall LowerSemicontinuous

/- Text 7.0.6 reads epigraph closedness on the canonical epigraph owner `epi`. -/
recall epi

/- Closedness of a function in the sense of Text 7.0.6 is equivalently closedness of its
chapter epigraph owner `epi`. -/
recall lowerSemicontinuous_iff_isClosed_epi

/- Forward epigraph bridge on the canonical owner surface. -/
recall isClosed_epi_of_lowerSemicontinuous

/- Reverse epigraph bridge on the canonical owner surface. -/
recall lowerSemicontinuous_of_isClosed_epi

end
