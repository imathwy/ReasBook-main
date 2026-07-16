import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.5 states that the direct sum of two convex sets is convex.
- `core/canonical`: once Text 3.5.1 identifies that direct sum with `C ×ˢ D`, the canonical owner
  theorem is `Convex.prod` at the scalar-generic `Convex 𝕜` layer.
- `bridge/view`: product-set constructors and pair-membership (`Set.prod`, `Set.mem_prod`) are
  bridge material and belong to the neighboring bridge text item (`Text_3_5_1`).
- Primitive data vs derived API: only convexity of the two factors is primitive for this theorem
  item; the product bridge is upstream and should not be redundantly re-exposed here.
- Domain-style sampling: this matches the chapter pattern where theorem items expose the owner
  closure theorem directly when the mathlib owner is already primitive-layer correct (for example
  `Theorem_3_4` recalling `Convex.linear_image` and `Convex.linear_preimage`).
- Layer target: `core/canonical`; keep the theorem file owner-first, with bridge declarations left
  to the dedicated bridge text files.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: `Convex.prod` is already codomain-free
  and scalar-generic.
- Scalar/ambient structure stronger than needed? `No`: this theorem stays at the native owner
  assumptions of `Convex.prod`, not a concrete-scalar specialization.
- Concrete-model owner instead of intrinsic owner? `No`: owner is the intrinsic set predicate
  `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is convexity closure, not a
  topological interior/closure statement.
- Owner-name/notation mismatch? `No`: the canonical owner name `Convex.prod` and canonical set
  product notation `×ˢ` are the theorem surface.
- Upstream over-specialization to repair first? `No`: the bridge is already upstream in
  `Text_3_5_1`, so this theorem remains a direct owner recall.
-/

/- Theorem 3.5: after identifying the direct sum with the set product `C ×ˢ D`, convexity is the
canonical owner theorem `Convex.prod`. -/
recall Convex.prod
