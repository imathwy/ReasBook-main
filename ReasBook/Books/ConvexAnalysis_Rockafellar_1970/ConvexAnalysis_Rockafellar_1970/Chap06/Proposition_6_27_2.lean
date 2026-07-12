import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1_WithBotTopBridge

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {α : Type v}
variable [TopologicalSpace E] [LinearOrder α] [NoMinOrder α] [Nonempty α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.2 says that every finite-height sublevel set
  `{x | f x ≤ a}` is closed.
- `core/canonical`: the chapter owner theorem for that statement is
  `lowerSemicontinuous_iff_isClosed_sublevel`.
- `bridge/view`: the lower-level mathlib mechanism is
  `LowerSemicontinuous.isClosed_preimage`, while the Chapter 3 bundle
  `Function.IsClosedProperConvex` supplies lower semicontinuity only as a downstream bridge.

Domain-style sampling used here:
- `lowerSemicontinuous_iff_isClosed_sublevel` from `Chap02.Theorem_7_1`;
- `lowerSemicontinuous_iff_isClosed_preimage` from the same lower-semicontinuity owner layer;
- `LowerSemicontinuous.isClosed_preimage` from mathlib's semicontinuity API;
- `Function.IsClosedProperConvex.lowerSemicontinuous` from `Chap03.Text_12_3_6`.

Primitive data vs derived API:
- primitive data: a function `f : E → WithBotTop α` and the owner hypothesis
  `LowerSemicontinuous f`;
- derived API: closedness of the scalar sublevel sets `{x | f x ≤ a}`;
- this file keeps the proposition on the owner surface `LowerSemicontinuous` and derives it from
  the Chapter 2 characterization theorem, rather than recalling the stronger biconditional as the
  main entry.

Layer target: `source-facing`, with the main theorem stated as the forward-direction specialization
of the Chapter 2 owner theorem on the canonical owner namespace.
-/

namespace LowerSemicontinuous

/-- Proposition 6.27.2: every finite-height scalar sublevel set of a lower semicontinuous
function is closed. This is the forward-direction specialization of
`lowerSemicontinuous_iff_isClosed_sublevel`. -/
theorem isClosed_sublevel {f : E → WithBotTop α} (hf : LowerSemicontinuous f) (a : α) :
    IsClosed {x : E | f x ≤ a} :=
  (lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf) a

end LowerSemicontinuous

end
