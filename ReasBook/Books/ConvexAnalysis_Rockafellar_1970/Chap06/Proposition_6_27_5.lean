import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {γ : Type v} [TopologicalSpace E] [Preorder γ]
/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.5 says that the minimum set of a closed proper convex
  function is a closed subset of the ambient space.
- `core/canonical`: the owner abstractions sampled for this repair are
  the source-facing minimum-set owner `minimumSet` from `Definition_6_27_3`,
  mathlib's owner theorem `LowerSemicontinuous.isClosed_preimage` for lower-ray preimages,
  and the Chapter 3 bundle `Function.IsClosedProperConvex` only as a downstream bridge to that
  lower-semicontinuous owner.
- `bridge/view`: the canonical theorem is stated on `LowerSemicontinuous`, while the textbook
  closed-proper-convex proposition is kept as a one-line specialization on the same
  source-facing set owner `minimumSet f`.

Domain-style sampling used here:
- `minimumSet` and `isMinOn_univ_iff` from `Definition_6_27_3` and mathlib's extrema API;
- `LowerSemicontinuous.isClosed_preimage` from mathlib's semicontinuity API;
- `Function.IsClosedProperConvex.lowerSemicontinuous` from `Text_12_3_6`;
- `lowerSemicontinuous_iff_isClosed_sublevel` from `Chap02.Theorem_7_1`, whose forward direction
  is the chapter owner for ordinary sublevel-set closedness.

Primitive data vs derived API:
- primitive data: a function `f : E → γ` and closedness of each scalar lower-ray preimage
  `f ⁻¹' Set.Iic r`;
- derived API: the closedness of the source-facing minimum set `minimumSet f`;
- bridge API: lower semicontinuity and closed-proper-convexity as sufficient hypotheses that
  imply the primitive closed-sublevel input.

Layer target: `source-facing`, with the owner abstraction refined downward to the minimal
closedness input.
-/

-- Proof sketch: `minimumSet f` is exactly the intersection of scalar lower-ray preimages
-- `f ⁻¹' Set.Iic (f y)` over all `y`. If every scalar lower-ray preimage is closed, then the minimum set is
-- closed by arbitrary intersection.
/-- The minimum set is closed whenever all scalar lower-ray preimages are closed. -/
theorem minimumSet_isClosed_of_isClosed_sublevel {f : E → γ}
    (hsublevel : ∀ r : γ, IsClosed (f ⁻¹' Set.Iic r)) :
    IsClosed (minimumSet f) := by
  rw [show minimumSet f = ⋂ y, f ⁻¹' Set.Iic (f y) by
    ext x
    simp [minimumSet, isMinOn_univ_iff]]
  refine isClosed_iInter ?_
  intro y
  exact hsublevel (f y)

end

section

variable {E : Type u} {γ : Type v} [TopologicalSpace E] [LinearOrder γ]

namespace LowerSemicontinuous

-- Proof sketch: lower semicontinuity gives closedness of scalar lower-ray preimages
-- `f ⁻¹' Set.Iic r`, then the primitive closed-sublevel minimum-set theorem applies.
/-- The minimum set of a lower semicontinuous function is closed. -/
theorem minimumSet_isClosed {f : E → γ} (hf : LowerSemicontinuous f) :
    IsClosed (minimumSet f) :=
  minimumSet_isClosed_of_isClosed_sublevel (f := f) hf.isClosed_preimage

end LowerSemicontinuous

end

section

variable {𝕜 : Type*} {E : Type u} {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [LinearOrder α] [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul 𝕜 α]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace Function.IsClosedProperConvex

-- Proof sketch: closed-proper-convexity provides lower semicontinuity via the owner projection,
-- then the canonical lower-semicontinuous minimum-set theorem applies.
/-- The minimum set of a closed proper convex function is closed. -/
theorem minimumSet_isClosed {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsClosed (minimumSet f) :=
  hf.lowerSemicontinuous.minimumSet_isClosed

end Function.IsClosedProperConvex

-- Proof sketch: Proposition 6.27.5 is the source-facing specialization of the canonical owner
-- theorem `Function.IsClosedProperConvex.minimumSet_isClosed`.
/-- Proposition 6.27.5: the minimum set of a closed proper convex function is closed. -/
theorem minimumSet_isClosed {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsClosed (minimumSet f) :=
  hf.minimumSet_isClosed

end
