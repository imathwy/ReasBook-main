import ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import ProbabilityTheory_Klenke_2020.Items.Chap19.Exercise_19_5_LadderGraphs
import ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_19

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/- Domain-style sampling for Exercise 19.5.4:
- `source-facing`: the crossed ladder graph of Fig. 19.16 with the distinguished vertices `a` and
  `z`.
- Inspected owner declarations:
  `SimpleLadderVertex`,
  `simpleLadderA`,
  `simpleLadderZ`,
  `effectiveConductance`,
  `escapeToSetProbability`.
- Best owner abstraction: the concrete Fig. 19.16 graph on the shared ladder carrier from
  `Exercise_19_5_LadderGraphs`, with the source quantities expressed through the Chapter 19 owners
  `effectiveConductance` and `escapeToSetProbability`.
- Primitive data: the graph of Fig. 19.16 itself. The carrier and marked vertices are reused from
  `Exercise_19_5_LadderGraphs` rather than duplicated.
  Derived API: the effective conductance between `a` and `z` and the hit-before-return probability
  for simple random walk on that graph.
- Source/core/bridge triage: this file is `source-facing`; it models the concrete graph from the
  figure, while the conductance and hitting-probability expressions are the existing canonical
  Chapter 19 bridge/view owners. -/

-- Proof sketch: by reflection symmetry across the horizontal midline and across the middle
-- column, every non-boundary column has potential `1 / 2` on both vertices in the unit boundary
-- value problem with `u(a) = 1` and `u(z) = 0`. The emitted current from `a` is therefore
-- `1 + 4 * (1 / 2) = 3`.
/-- Exercise 19.5.4 (1): for the crossed ladder graph of Fig. 19.16, the effective conductance
between `a` and `z` is `3`. -/
theorem crossedLadder_effectiveConductance_between_a_z_eq_three :
    effectiveConductance (simpleGraphWeights crossedLadderGraph)
      ({simpleLadderA} : Set SimpleLadderVertex) ({simpleLadderZ} : Set SimpleLadderVertex) = 3 :=
  sorry

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : SimpleLadderVertex → SimpleLadderVertex → ℝ≥0∞}
variable {P : SimpleLadderVertex → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → SimpleLadderVertex}
variable [IsSimpleRandomWalk p crossedLadderGraph]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: the marked vertex `a` has degree `5` in the crossed ladder graph. Combine the
-- conductance value from `crossedLadder_effectiveConductance_between_a_z_eq_three` with the
-- Chapter 19 identity `P_a[τ_z < τ_a] = conductance(a)⁻¹ C_eff(a ↔ z)`.
/-- Exercise 19.5.4 (2): for the simple random walk on the crossed ladder graph of Fig. 19.16,
started at `a`, the probability of hitting `z` before the first strictly positive return to `a`
is `3 / 5`. -/
theorem crossedLadder_hit_z_before_return_to_a_eq_three_fifths :
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex) =
      (3 / 5 : ℝ≥0∞) := sorry

end

end ProbabilityTheory
