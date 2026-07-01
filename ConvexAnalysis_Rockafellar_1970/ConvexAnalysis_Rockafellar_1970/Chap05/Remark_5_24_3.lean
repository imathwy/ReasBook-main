import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_4

namespace SetRel

section

variable {ι : Type*} [LE ι]
variable {α : Type*} [LE α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.3 characterizes the Chapter 5 owner
  `SetRel.IsCompleteNondecreasingCurve` on relations `Γ : SetRel ι α`.
- `core/canonical`: mathlib's order-theoretic owner for a maximal chain is
  `IsMaxChain`, and on `ι × α` the ambient relation `(· ≤ ·)` is the coordinatewise order relation.
- `bridge/view`: this standalone item file reuses the canonical bridge theorem from
  `Definition_5_24_4` directly and only provides directional projection lemmas for source-style
  forward/backward use.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` and `Function.completeNondecreasingCurve` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_4.lean`, the project owners for
  the source notion and its witness-side graph realization;
- `Function.leftLim` and `Function.rightLim` from
  `.lake/packages/mathlib/Mathlib/Topology/Order/LeftRightLim.lean`, the canonical owners for the
  one-sided limits used in that witness-side realization;
- `IsChain` and `IsMaxChain` from mathlib's
  `.lake/packages/mathlib/Mathlib/Order/Preorder/Chain.lean`, the canonical owners for chain and
  maximal-chain structure;
- the product order relation on `ι × α`, whose `≤` is exactly the coordinatewise ordering
  appearing in the source.

Primitive data vs derived API:
- primitive source-facing owner: `SetRel.IsCompleteNondecreasingCurve Γ`;
- primitive canonical comparison owner: `IsMaxChain (· ≤ ·) Γ`;
- derived API kept here: only directional projection lemmas from the upstream equivalence, with no
  local duplicate `↔` theorem and no extra chain wrapper or maximal-curve package.

Layer target: `bridge/view`.

Semantic-fidelity audit:
- the source-facing owner `SetRel.IsCompleteNondecreasingCurve` from Definition 5.24.4 remains the
  main mathematical notion on the left side;
- the right side reuses the exact mathlib order-theoretic owner `IsMaxChain` for the coordinatewise
  order on `ι × α`, with no new wrapper around chains or maximality;
- this file therefore operates purely at the `bridge/view` layer, does not introduce any second
  owner for complete non-decreasing curves, and does not duplicate the upstream bridge theorem name.
-/

/-- A complete non-decreasing curve in `ι × α` is a maximal chain for the coordinatewise order. -/
@[simp] theorem IsCompleteNondecreasingCurve.isMaxChain {Γ : SetRel ι α}
    (hΓ : Γ.IsCompleteNondecreasingCurve) :
    IsMaxChain (· ≤ ·) Γ :=
  (isCompleteNondecreasingCurve_iff_isMaxChain Γ).1 hΓ

/-- A maximal chain in `ι × α` for the coordinatewise order is a complete non-decreasing curve. -/
@[simp] theorem IsMaxChain.isCompleteNondecreasingCurve {Γ : SetRel ι α}
    (hΓ : IsMaxChain (· ≤ ·) Γ) :
    Γ.IsCompleteNondecreasingCurve :=
  (isCompleteNondecreasingCurve_iff_isMaxChain Γ).2 hΓ

end

end SetRel
