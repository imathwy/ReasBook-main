import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.1 states that the intersection of any family of convex sets is again
  convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜 s` for a set `s` at the minimal canonical
  layer `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]`; the intrinsic family-level
  closure theorem is `convex_iInter`.
- `bridge/view`: the textbook's “arbitrary collection” presentation is the concrete model
  `Set (Set E)`, which is available as the bridge theorem `convex_sInter`.
- Primitive data vs derived API: the convexity predicate is the owner notion; the intersection
  closure statement should be reused directly rather than repackaged as a second theorem.
- Domain-style sampling: the relevant owner-side declarations here are mathlib's
  `convex_iInter`, `convex_iInter₂`, and `convex_sInter`; this item recalls the canonical
  intrinsic owner theorem directly and leaves the collection-level encoding as a bridge view.
- Layer target: `core/canonical`; expose only the indexed-family owner theorem on the item
  surface.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: `Convex 𝕜` is reused at the minimal ordered-semiring
  scalar layer from mathlib.
- Scalar/ambient structure stronger than needed? `No`: there is no `ℝ`-specific or
  finite-coordinate specialization in this item surface.
- Owner tied to a concrete model? `No` for the exposed theorem surface: `convex_iInter` keeps the
  owner intrinsic, while `convex_sInter` remains an available bridge encoding.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is purely order/algebraic.
- Owner name/notation too heavy or too concrete? `No` on the exposed surface: canonical owner and
  standard intersection notation `⋂` are used directly.
- Upstream over-specialization to repair first? `No`: the upstream owners already sit at the
  intended abstraction layer.
-/

/- Theorem 2.1, intrinsic indexed-family form: arbitrary intersections preserve convexity at the
canonical ambient scalar layer. -/
recall convex_iInter
