import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Theorem_19_15
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Theorem_19_6
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Theorem_17_38

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {E : Type u} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

section

variable {p C : E → E → ℝ≥0∞}
variable [IsRandomWalkWithWeights p C]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
variable [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]

-- Proof sketch: `u` is harmonic on the complement of `{zeroVertex, oneVertex}` by
-- `electricalPotential_isHarmonicOn_compl`. Finite-state irreducibility gives
-- `IsRecurrentMarkovChain P X` via
-- `finite_irreducibleMarkovChain_isRecurrent_of_discreteMatrixKernel_isIrreducible`, so from any
-- start state the chain hits `{zeroVertex, oneVertex}` almost surely. Hence the first-hit value
-- function `x ↦ F_A P X {zeroVertex} x oneVertex` solves the same Dirichlet problem with boundary
-- values `0` at `zeroVertex` and `1` at `oneVertex`, including the boundary points themselves. By
-- the finite-state uniqueness of the Dirichlet problem, the two functions agree.
/-- Example 19.32: for a finite conductance network, hence in particular for a graph with unit
resistors and simple random walk, the probability that the chain started at `x` visits the
boundary vertex `oneVertex` before it visits `zeroVertex` equals the electrical potential `u x`
when `u` has boundary values `0` at `zeroVertex` and `1` at `oneVertex`. In the finite irreducible
setting below, the first hit of `{zeroVertex, oneVertex}` is derived internally to be almost
surely finite, so no separate stopping-time finiteness hypothesis or off-boundary guard is part of
the public API. -/
theorem voltage_eq_probability_hit_one_before_zero
    {u : E → ℝ} {zeroVertex oneVertex x : E}
    (hu : IsElectricalPotential C ({zeroVertex, oneVertex} : Set E) u)
    (hboundary :
      Set.EqOn u (fun z : E ↦ if z = oneVertex then (1 : ℝ) else 0)
        ({zeroVertex, oneVertex} : Set E)) :
    u x = F_A P X ({zeroVertex} : Set E) x oneVertex := sorry

end

end ProbabilityTheory
