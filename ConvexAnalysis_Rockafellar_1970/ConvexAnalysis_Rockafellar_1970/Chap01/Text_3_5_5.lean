import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.5 introduces, from a convex set `C ⊆ E`, the subset
  `K_C = {(λ, x) | 0 ≤ λ, x ∈ λ • C}` in one higher dimension and asserts that it is convex.
- `core/canonical`: the public owner is the existing chapter definition
  `homogenizationSet C : Set (R × E)` from Proposition 2.6.12, with its owner-side derived API
  `Convex.homogenizationSet`.
- `bridge/view`: the textbook notation `K_C` is exactly the already named chapter owner
  `homogenizationSet C`, so the convexity assertion here is exact reuse of the owner theorem rather
  than a new bridge construction.
- Primitive data vs derived API: the set `K_C` itself is the already defined source-facing owner
  `homogenizationSet C`; its convexity is derived API on that owner.
- Domain-style sampling: this item aligns with `homogenizationSet`,
  `mem_homogenizationSet_iff`, `Convex.homogenizationSet`, and the chapter pointed-cone bridge
  `pointedConeHull_lift_eq_homogenizationSet`.
- Layer target: `core/canonical`; this numbered text is exact owner reuse, so the main entry should
  be a direct `recall` of `Convex.homogenizationSet` rather than a parallel local theorem.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this item has no function codomain owner;
  it is a set-convexity statement over the existing canonical owner `Convex R`.
- Scalar or ambient structure too concrete? `No` in this file: this item reuses the upstream owner
  theorem `Convex.homogenizationSet` without adding stronger local assumptions.
- Owner tied to a concrete model? `No`: owner surface is intrinsic (`homogenizationSet` / `Convex`)
  and does not introduce model-specific shadow predicates.
- Ambient vs intrinsic topology issue? `Not applicable`: no topology primitives occur here.
- Owner naming too concrete/long? `No`: theorem surface reuses the short canonical owner theorem
  directly via `recall`.
- Notation need on theorem surface? `Already satisfied`: the source-facing notation bridge `K[·|·]`
  is provided upstream, and this item introduces no parallel notation layer.
-/

/- Text 3.5.5: for a convex set `C`, the set
`K_C = {(λ, x) ∈ R × E | 0 ≤ λ, x ∈ λ • C}` is convex. Since `K_C` is exactly
`homogenizationSet C`, this item is exact reuse of the canonical owner theorem
`Convex.homogenizationSet`. -/
recall Convex.homogenizationSet
