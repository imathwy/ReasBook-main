import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.1 says that for a convex function
  `f : ℝ^n → (-∞, +∞]`, each real closed sublevel set `{x | f x ≤ α}` is convex.
- `core/canonical`: the project owner theorem for this statement is
  `Function.IsConvex.convex_le`, already stated at the natural abstraction level of a convex
  `WithBotTop α`-valued function on a module.
- `bridge/view`: the textbook `ℝ^n` statement is the real finite-dimensional specialization of
  that owner theorem; no extra local wrapper or renamed specialization is mathematically needed.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsConvex.convex_le` from `Chap01.Theorem_4_6`;
- `Function.IsConvex.convex_lt` from `Chap01.Theorem_4_6`;
- `Function.IsConvex.quasiconvexOn` from `Chap01.Theorem_4_6`.

Primitive data vs derived API:
- primitive input: a convex function in the owner sense `Function.IsConvex`;
- derived conclusion: convexity of its closed sublevel set at a chosen level.

Layer target: `core/canonical`. This item is a direct reuse of the existing owner theorem rather
than a new declaration.
-/

/- Proposition 6.27.1: for a convex function, every closed sublevel set `{x | f x ≤ α}` is
convex. This is exactly the canonical owner theorem `Function.IsConvex.convex_le`, specialized in
the book to `f : ℝ^n → (-∞, +∞]` and `α : ℝ`. -/
recall Function.IsConvex.convex_le
