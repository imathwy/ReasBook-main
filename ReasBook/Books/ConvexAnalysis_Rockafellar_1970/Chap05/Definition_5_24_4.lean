import Mathlib

noncomputable section

open scoped SetRel

universe u v

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.4 uses one-sided limits to describe complete non-decreasing
  curves via witness profiles.
- `core/canonical`: the chapter owner for the curve notion itself is the intrinsic order-theoretic
  owner `IsMaxChain (· ≤ ·)` on `ι × α`.
- `bridge/view`: `Function.completeNondecreasingCurve` is retained as the witness-side
  interval-fiber realization built from `leftLim` and `rightLim`.

Domain-style sampling used here:
- `Function.leftLim` and `Function.rightLim` from
  `.lake/packages/mathlib/Mathlib/Topology/Order/LeftRightLim.lean`, which are the canonical
  owners for strict one-sided limits;
- the intrinsic interval owner `Set.Icc` in the chapter's canonical extended codomain
  `WithTopBot α`, expressing membership in the source interval fiber `[φ_-(x), φ_+(x)]`;
- `subdifferentialGraph` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean`, which fixes the chapter's
  owner level for multivalued graphs as `SetRel`.

Primitive data vs derived API:
- primitive source-facing owner: mathlib's canonical `IsMaxChain (· ≤ ·) Γ` on relations;
- derived bridge/view API: the witness-side relation `φ.completeNondecreasingCurve` and its
  membership simplification.
-/

namespace Function

section

variable {ι : Type u} [LinearOrder ι]
variable {α : Type v} [Preorder α] [TopologicalSpace (WithTopBot α)]

/- Definition 5.24.4, witness-side bridge: the non-decreasing function `φ` determines the graph
relation whose fiber over `x` is the interval cut out by `φ_-(x)` and `φ_+(x)` in the ambient
extended codomain. In the source specialization `ι = ℝ`, `α = ℝ`, this is exactly
`[φ_-(x), φ_+(x)] ∩ ℝ`. -/
abbrev completeNondecreasingCurve (φ : ι → WithTopBot α) : SetRel ι α :=
  {p | (p.2 : WithTopBot α) ∈ Set.Icc (φ.leftLim p.1) (φ.rightLim p.1)}

/-- Pointwise membership in `φ.completeNondecreasingCurve` is exactly interval membership in
`[φ_-(x), φ_+(x)]` inside the ambient codomain. -/
@[simp] theorem mem_completeNondecreasingCurve_iff_mem_Icc
    {φ : ι → WithTopBot α} {x : ι} {xStar : α} :
    x ~[φ.completeNondecreasingCurve] xStar ↔
      (xStar : WithTopBot α) ∈ Set.Icc (φ.leftLim x) (φ.rightLim x) :=
  Iff.rfl

/-- Pointwise membership in `φ.completeNondecreasingCurve` is exactly
`φ_-(x) ≤ x⋆ ≤ φ_+(x)` in the ambient codomain order. -/
@[simp] theorem mem_completeNondecreasingCurve
    {φ : ι → WithTopBot α} {x : ι} {xStar : α} :
    x ~[φ.completeNondecreasingCurve] xStar ↔
      φ.leftLim x ≤ (xStar : WithTopBot α) ∧
        (xStar : WithTopBot α) ≤ φ.rightLim x := by
  simp [Set.mem_Icc]

end

end Function

namespace SetRel

section

variable {ι : Type u} [LE ι]
variable {α : Type v} [LE α]

/- Layer target: `source-facing`. The owner itself is the canonical order owner
`IsMaxChain (· ≤ ·)` on relations; the function-side graph construction above is a bridge/view. -/

/-- Canonical owner for complete non-decreasing curves: maximal chains for the coordinatewise
order on `ι × α`. -/
abbrev IsCompleteNondecreasingCurve (Γ : SetRel ι α) : Prop :=
  IsMaxChain (· ≤ ·) Γ

/-- Definitional bridge to the canonical order owner. -/
@[simp] theorem isCompleteNondecreasingCurve_iff_isMaxChain (Γ : SetRel ι α) :
    Γ.IsCompleteNondecreasingCurve ↔ IsMaxChain (· ≤ ·) Γ :=
  Iff.rfl

end

end SetRel
