import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Remark_9_2_0_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_3_1

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

open Bornology

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [SMul 𝕜 E]
variable {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [SMul 𝕜 α]
variable [TopologicalSpace (WithTopBot α)]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.3.2 says that a closed proper convex function is co-finite whenever
  its domain is bounded.
- `core/canonical`: the owner predicates already fixed in this chapter are
  `Function.IsClosedProperConvex`, the co-finite owner predicate `Function.IsCofinite`, and the
  effective-domain owner `dom(·)`.
- `bridge/view`: boundedness of the source-visible domain is rendered canonically by
  `IsBounded dom(f)`, while the recession-side criterion is supplied by the chapter
  recession owner theorem.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `Function.IsCofinite` from `Text_13_3_1`;
- `effectiveDomain` from `Definition_4_4`;
- `recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain` from
  `Remark_9_2_0_2`;

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot α`;
- owner hypotheses: closed proper convexity of `f` and boundedness of its effective domain
  `dom(f)`;
- derived API: the co-finite conclusion, expressed by the owner predicate from Text 13.3.1.

Layer target: this item stays `source-facing`, but both its hypothesis package and its conclusion
are stated directly using the chapter owner predicates rather than re-expanding them locally.
Ambient refinement: the only genuinely metric input is boundedness of `dom(f)`, so the theorem is
stated on an intrinsic `RCLike` normed-space ambient layer `[NormedSpace K E]`, while the
closed/proper/convex and co-finite owners remain scalar-generic in `𝕜`.
-/

namespace Function.IsClosedProperConvex

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

/-- Text 13.3.2: a closed proper convex function is co-finite whenever its effective domain
`dom(f)` is bounded. -/
-- Proof sketch: boundedness of the effective domain rules out every nonzero recession
-- direction, because any half-line `x + t • y` with `y ≠ 0` would be unbounded. The previous text
-- identifies co-finiteness with the condition `(f0⁺) y = ⊤` for all nonzero `y`,
-- and the remaining closed/proper/convex hypotheses are already packaged by the owner predicate
-- `Function.IsClosedProperConvex`.
theorem isCofinite_of_bounded_effectiveDomain
    {K : Type*} [RCLike K] [NormedSpace K E]
    {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f)
    (hdom_bounded : IsBounded dom(f)) :
    IsCofinite[𝕜] f := by
  have hcof := hf.isCofinite_iff_dom_recessionFunction_subset_zero
  rw [hcof]
  intro y hy_dom
  have hy0 : y = 0 := by
    by_contra hy0
    have hy_top : recessionFunction f y = ⊤ :=
      recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain
        f hf.proper.nonempty_dom hdom_bounded y hy0
    have hy_not_mem : y ∉ dom(recessionFunction f) := by
      simpa [mem_effectiveDomain, hy_top]
    exact hy_not_mem hy_dom
  simp [hy0]

end Function.IsClosedProperConvex

end
