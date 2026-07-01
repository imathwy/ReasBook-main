import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 7.13 lies in the feasible-set / closed-ball localization domain.

Sampled owner-style declarations:
- mathlib `Metric.closedBall`
- mathlib `Metric.mem_closedBall`
- core `Set.inter`

Best owner abstraction:
- source-facing: `boundedFeasibleSet Q1 x0 ρ`, the textbook localized feasible set `Q₁(ρ)`
- core/canonical: `Q1 ∩ Metric.closedBall x0 ρ`
- bridge/view: membership lemmas in distance and norm form

Primitive data:
- a feasible set `Q1 : Set E`
- a base point `x0 : E`
- a radius `ρ : ℝ`

Derived API:
- membership as `x ∈ Q1 ∧ dist x x0 ≤ ρ`
- in normed additive groups, the equivalent norm form `x ∈ Q1 ∧ ‖x - x0‖ ≤ ρ`
-/

section Metric

variable {E : Type u} [PseudoMetricSpace E]

/-- Definition 7.13: for `ρ ≥ 0`, the bounded feasible set `Q₁(ρ)` is the subset of the feasible
set `Q₁` consisting of the points whose distance from `x₀` is at most `ρ`. -/
def boundedFeasibleSet (Q1 : Set E) (x0 : E) (ρ : ℝ) : Set E :=
  Q1 ∩ Metric.closedBall x0 ρ

/-- Membership in the bounded feasible set means ambient feasibility together with the distance
bound `dist x x₀ ≤ ρ`. -/
theorem mem_boundedFeasibleSet_iff_dist
    {Q1 : Set E} {x0 x : E} {ρ : ℝ} :
    x ∈ boundedFeasibleSet Q1 x0 ρ ↔ x ∈ Q1 ∧ dist x x0 ≤ ρ := by
  simp [boundedFeasibleSet]

end Metric

section Normed

variable {E : Type u} [SeminormedAddCommGroup E]

/-- Membership in the bounded feasible set means ambient feasibility together with the Euclidean
bound `‖x - x₀‖ ≤ ρ`. -/
theorem mem_boundedFeasibleSet_iff
    {Q1 : Set E} {x0 x : E} {ρ : ℝ} :
    x ∈ boundedFeasibleSet Q1 x0 ρ ↔ x ∈ Q1 ∧ ‖x - x0‖ ≤ ρ := by
  simpa [dist_eq_norm] using
    (mem_boundedFeasibleSet_iff_dist : x ∈ boundedFeasibleSet Q1 x0 ρ ↔ x ∈ Q1 ∧ dist x x0 ≤ ρ)

end Normed
