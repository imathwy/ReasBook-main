import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.4 says that the intersection of two convex sets is convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜` on subsets of an ambient type carrying
  `[AddCommMonoid E] [SMul 𝕜 E]` with scalar assumptions `[Semiring 𝕜] [PartialOrder 𝕜]`, and
  the exact canonical closure theorem is `Convex.inter`.
- `bridge/view`: any concrete ambient model is a specialization of this owner theorem, so no extra
  wrapper or coordinate-specific bridge layer is needed.
- Primitive data vs derived API: the sets and their convexity proofs are primitive; convexity of
  the intersection is the whole statement.
- Domain-style sampling: the relevant owner-side declarations here are `Convex.inter`,
  `convex_sInter`, `convex_iInter`, and the nearby closure theorem `Convex.prod`.
- Layer target: `core/canonical`; this item is exact owner reuse, so the public entry should stay
  a direct `recall` of `Convex.inter` rather than a parallel local wrapper.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `No`: the owner already lives on intrinsic sets
    `Set E` in a scalar-generic ambient module-like type.
  - Scalar/ambient structure over-concrete? `No`: `Convex.inter` already sits at
    `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]`.
  - Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜`, not a coordinate wrapper.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: this is convexity, not a topology
    statement.
  - Owner name too long/concrete? `No`: `Convex.inter` is the short canonical owner theorem.
  - Missing theorem-surface notation? `No`: the theorem surface is already the primary notation
    `C₁ ∩ C₂`.
-/

/- Text 3.6.4: if `C₁` and `C₂` are convex sets, then `C₁ ∩ C₂` is convex; this is exactly the
canonical theorem `Convex.inter`. -/
recall Convex.inter
