import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexFunctionPolar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.30 states the Young-type inequality
  `⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆` for points in the effective domains of a nonnegative closed convex
  function `f` with `f 0 = 0` and of its polar.
- `core/canonical`: the preceding Chapter 15 item introduces the polar by the affine-majorant
  infimum formula and proves exactly this inequality for finite-value points.
- `bridge/view`: this item is therefore a direct recall of that owner theorem rather than a second
  local theorem shell.

Domain-style sampling used here:
- `gauge_polar` from `Text_15_0_5`;
- `convex_function_polar` from `Text_15_0_29`;
- `inner_le_one_add_mul_convex_function_polar` from `Text_15_0_29`.

Layer target: `core/canonical` direct recall. This item adds no new owner abstraction and no new
bridge theorem beyond the existing Chapter 15 owner statement.
-/

/- Text 15.0.30: if `x` is a finite-value point of a nonnegative `WithBotTop 𝕜`-valued function
`f` and `x⋆` is a finite-value point of its polar, then
`⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆`. This is exactly
`inner_le_one_add_mul_convex_function_polar` from `Text_15_0_29`. -/
recall inner_le_one_add_mul_convex_function_polar
