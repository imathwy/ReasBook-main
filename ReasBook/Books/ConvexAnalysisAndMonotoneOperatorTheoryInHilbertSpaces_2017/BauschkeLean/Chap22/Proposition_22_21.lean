import Mathlib
import BauschkeLean.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Proposition 22.21 is the one-dimensional graph-order characterization of a
  monotone set-valued operator.
- `core/canonical`: the owner abstractions are `SetValuedOperator.IsMonotone`, `gra`, and the
  order-theoretic owner `IsChain` on the canonical product order of `ℝ × ℝ`.
- `bridge/view`: this file only rewrites the Chapter 20 monotonicity inequality into pairwise
  comparability in `ℝ × ℝ`; it should not introduce a parallel graph-order wrapper.

Primitive data: the operator `A`.
Derived API: the graph-chain reformulation. -/

/-- Proposition 22.21: a set-valued operator `A : ℝ → 2^ℝ` is monotone if and only if `gra A` is
a chain in `(ℝ × ℝ, ≼)`, where `≼` is the componentwise order on `ℝ × ℝ`. The textbook nonempty
graph hypothesis is redundant for this equivalence, so the canonical Lean statement omits it. -/
theorem isMonotone_iff_graph_isChain
    (A : SetValuedOperator ℝ ℝ) :
    A.IsMonotone ↔ IsChain (· ≤ ·) (gra A) := by
  rw [SetValuedOperator.isMonotone_iff, IsChain]
  constructor
  · intro h p hp q hq hpq
    rcases p with ⟨x, u⟩
    rcases q with ⟨y, v⟩
    have hinner :
        0 ≤ ⟪x - y, u - v⟫_ℝ := h hp hq
    have hinner_eq : ⟪x - y, u - v⟫_ℝ = (x - y) * (u - v) := by
      simpa [conj_trivial] using (RCLike.inner_apply' (x - y) (u - v))
    have hmul : 0 ≤ (x - y) * (u - v) := by
      simpa [hinner_eq] using hinner
    rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos] at hmul
    rcases hmul with hqp | hpq'
    · exact Or.inr hqp
    · exact Or.inl hpq'
  · intro h x u y v hu hv
    have hcomp : (x, u) ≤ (y, v) ∨ (y, v) ≤ (x, u) := by
      by_cases hxyu : (x, u) = (y, v)
      · simp [hxyu]
      · exact h (by simpa using hu) (by simpa using hv) hxyu
    have hmul : 0 ≤ (x - y) * (u - v) := by
      rcases hcomp with hxy | hyx
      · rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos]
        exact Or.inr hxy
      · rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos]
        exact Or.inl hyx
    have hinner_eq : ⟪x - y, u - v⟫_ℝ = (x - y) * (u - v) := by
      simpa [conj_trivial] using (RCLike.inner_apply' (x - y) (u - v))
    simpa [hinner_eq] using hmul

end SetValuedOperator
