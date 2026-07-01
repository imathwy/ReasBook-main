import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.11 states that for convex sets `C₁, C₂`, the pointwise sum of their
  homogenization sets is convex.
- `core/canonical`: this is exactly the owner theorem `Convex.homogenizationSet_add` on
  `homogenizationSet` and set addition.
- `bridge/view`: the textbook set `K` is the notation-level surface `K[R | C₁] + K[R | C₂]`.
- Primitive data vs derived API: no new owner is introduced here; this text item is direct reuse of
  the canonical derived API on `homogenizationSet`.
- Layer target: `core/canonical`; expose the existing owner theorem by recall.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this item is a set-convexity statement
  and reuses the canonical owner `Convex R`.
- Scalar or ambient structure too concrete? `No` in this file: no extra assumptions are introduced
  beyond those of the upstream owner theorem `Convex.homogenizationSet_add`.
- Owner tied to a concrete model? `No`: the surface is intrinsic (`homogenizationSet` and set
  addition), not a coordinate model shadow owner.
- Ambient vs intrinsic topology issue? `Not applicable`: no topology primitives occur here.
- Owner naming too concrete/long? `No`: the theorem surface is the short owner theorem itself.
- Notation needed on theorem surface? `Yes`, and already satisfied via `K[R | _]`.
-/

/- Text 3.6.11: for convex sets `C₁` and `C₂`, the pointwise sum
`K[R | C₁] + K[R | C₂]` is convex. This item is exact reuse of
`Convex.homogenizationSet_add`. -/
recall Convex.homogenizationSet_add
