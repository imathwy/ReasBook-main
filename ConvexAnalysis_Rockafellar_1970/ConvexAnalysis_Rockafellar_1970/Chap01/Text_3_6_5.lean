import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.5 states that if `C₁` and `C₂` are convex subsets of an ambient
  product space, then their common part is convex.
- `core/canonical`: the owner abstraction is the predicate `Convex 𝕜 s` on sets in a
  `𝕜`-module-like ambient space (at the weak layer used by mathlib's owner theorem), and the
  matching canonical theorem is `Convex.inter`.
- `bridge/view`: the displayed membership condition "belongs to both sets" is exactly set
  intersection `C₁ ∩ C₂`, so no additional bridge layer is needed.
- Primitive data vs derived API: the sets `C₁` and `C₂` and their convexity are primitive; the
  conclusion is the direct closure theorem for intersections, so no local wrapper or surrogate
  definition should be introduced.
- Domain-style sampling: this item aligns with mathlib's owner declarations `Convex.inter`,
  `convex_sInter`, and `Convex.prod`, together with the chapter's earlier exact-reuse intersection
  recall `Text_3_6_4`.
- Layer target: `core/canonical`; this numbered text is just the product-space presentation of the
  owner theorem `Convex.inter`, so the main entry should remain a direct `recall` rather than a
  parallel local theorem specialized to pairs.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `Yes` in the textbook wording (`R^(m+p)`), but `No` in
    the owner theorem: `Convex.inter` already lives at the scalar-generic module layer.
  - Scalar structure over-concrete? `No`: the owner theorem already uses the weaker canonical
    assumptions from mathlib (`[Semiring 𝕜] [PartialOrder 𝕜]` plus module-like ambient data).
  - Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜` on `Set E`.
  - Ambient-vs-intrinsic topology issue? `Not applicable`: this item is order-convexity, not a
    topology statement.
  - Owner name too long/concrete? `No`: `Convex.inter` is the short canonical owner theorem.
  - Missing theorem-surface notation? `No`: the primary textbook surface is set intersection, and
    the canonical notation `C₁ ∩ C₂` is already the theorem surface of `Convex.inter`.
-/

/- Text 3.6.5: if `C₁` and `C₂` are convex subsets of a product ambient space, then their
intersection is convex. This is exactly the canonical theorem `Convex.inter`; the textbook
coordinate wording is a concrete specialization of that owner-level statement. -/
recall Convex.inter
