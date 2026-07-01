import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.3 states closure of convex sets under pointwise addition in a product
  ambient additive space.
- `core/canonical`: the owner abstraction is the scalar-generic predicate `Convex 𝕜` on sets, and
  the chapter-level canonical bridge is `Convex.add_set`.
- `bridge/view`: in any product ambient type, the displayed coordinatewise-sum set is exactly the
  pointwise sum `C₁ + C₂`.
- Primitive data vs derived API: the sets `C₁` and `C₂` are primitive; convexity of their
  pointwise sum is the whole statement, so no local wrapper theorem is needed.
- Domain-style sampling: this item reuses the upstream weak-layer owner bridge in `Theorem_3_1`,
  then follows nearby exact-reuse items such as `Theorem_3_5` (`Convex.prod`) and
  `Text_3_6_4` (`Convex.inter`).
- Layer target: `core/canonical`; this text is exact owner reuse, so the public entry should stay
  as a direct `recall` of the upstream weak-layer owner bridge rather than a local wrapper.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `Yes` in the textbook coordinate wording, but `No` in
    the owner theorem: `Convex.add_set` lives on intrinsic set convexity.
  - Scalar structure over-concrete? `No`: the theorem surface now reuses the weaker canonical
    layer from `Theorem_3_1` (`[DistribSMul 𝕜 E]`, not a forced module-level bridge).
  - Owner tied to a concrete model? `No`: the public owner is intrinsic `Convex 𝕜` on `Set E`.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is convexity closure, not
    a topological closure/interior statement.
  - Owner name/notation too heavy or too concrete? `No`: `Convex.add_set` and
    pointwise set addition notation `C₁ + C₂` are canonical here.
-/

/- Text 3.6.3: the displayed set of coordinatewise sums is exactly the pointwise sum `C₁ + C₂`, so
its convexity is given by the canonical weak-layer chapter bridge
`Convex.add_set`. -/
recall Convex.add_set
