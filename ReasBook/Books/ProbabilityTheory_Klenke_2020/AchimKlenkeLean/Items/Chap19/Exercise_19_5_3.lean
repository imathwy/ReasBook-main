import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Theorem_17_8
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Definition_19_17
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Definition_19_23
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Exercise_19_5_LadderGraphs
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Theorem_19_19
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Theorem_19_15
import Mathlib

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-
Domain-style sampling for Exercise 19.5.3:
- `source-facing`: the simple ladder graph of Fig. 19.15 together with the marked vertices `a`
  and `z`.
- `core/canonical`: `SimpleGraph.pathGraph`, `SimpleGraph.boxProd`, `SimpleGraph.pathGraph_adj`,
  and `SimpleGraph.boxProd_adj`.
- `bridge/view`: any explicit coordinate adjacency description on `Fin 7 × Fin 2`, derived from
  the box-product owner when needed.
Primitive data: the ladder graph and the distinguished vertices `a`, `z`, reused from
`Exercise_19_5_LadderGraphs`.
Derived API: the conductance and hitting-probability statements below.
-/

-- Proof sketch: use the left-right reflection symmetry about the middle rung to reduce the
-- network to one half of the ladder, solve the resulting reduced network by series-parallel
-- reduction, and evaluate the induced effective conductance.
/-- Exercise 19.5.3 (1): item (i). For the simple ladder graph of Fig. 19.15, the effective
conductance between the middle vertices `a` and `z` is `√3`. -/
theorem simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three
    :
    effectiveConductance (simpleGraphWeights simpleLadderGraph)
      ({simpleLadderA} : Set SimpleLadderVertex) ({simpleLadderZ} : Set SimpleLadderVertex) =
        Real.sqrt 3 := sorry

-- Proof sketch: apply the owner-level formula
-- `effectiveConductance_eq_netFlowOnSet_electricalCurrent` to the simple ladder boundary value
-- problem and then use
-- `simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three`.
/-- For any unit-boundary electrical potential on the simple ladder graph with `u(a) = 1` and
`u(z) = 0`, the emitted boundary current through the sink `{z}` is `-√3` because `netFlowOnSet`
uses the emitted-current convention. This is the boundary-current companion to the owner-level
conductance statement above. -/
theorem simpleLadder_netFlowOnSet_electricalCurrent_at_z_eq_neg_sqrt_three
    {u : SimpleLadderVertex → ℝ}
    (hu : IsElectricalPotential (simpleGraphWeights simpleLadderGraph) simpleLadderBoundary u)
    (ha : u simpleLadderA = 1)
    (hz : u simpleLadderZ = 0) :
    netFlowOnSet (electricalCurrent (simpleGraphWeights simpleLadderGraph) u)
      ({simpleLadderZ} : Set SimpleLadderVertex) = -Real.sqrt 3 := sorry

-- Proof sketch: identify `P_a[τ_z < τ_a]` with
-- `escapeToSetProbability P X simpleLadderA {simpleLadderZ}`. Then use the effective
-- conductance computation from
-- `simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three` together with the network identity
-- `P_a[τ_z < τ_a] = conductance(a)⁻¹ C_eff(a ↔ z)` and the fact that the Chapter 19 owner
-- `IsSimpleRandomWalk p simpleLadderGraph` makes `a` a degree-`3` simple-graph state.
/-- Exercise 19.5.3 (2): item (ii). For a random walk started at the middle top vertex `a` of the
simple ladder graph, the probability of hitting `z` before the first strictly positive return to
`a` is `1 / √3`. -/
theorem simpleLadder_hit_z_before_return_to_a_eq_inv_sqrt_three
    {Ω : Type v} [MeasurableSpace Ω]
    {p : SimpleLadderVertex → SimpleLadderVertex → ℝ≥0∞}
    {P : SimpleLadderVertex → ProbabilityMeasure Ω}
    {X : ℕ → Ω → SimpleLadderVertex}
    [IsSimpleRandomWalk p simpleLadderGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex) =
      ENNReal.ofReal (1 / Real.sqrt 3) := sorry

end ProbabilityTheory
