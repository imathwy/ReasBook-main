import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.Chap19.Definition_19_11
import ProbabilityTheory_Klenke_2020.Chap19.Theorem_19_6
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {Ω' : Type w} [MeasurableSpace Ω']

-- Proof sketch: compare effective conductance to infinity for the two conductance families using
-- Rayleigh monotonicity, then apply the recurrence criterion of Theorem 19.25 to transfer
-- recurrence from the walk with weights `C` to the walk with weights `C'`.
/-- Theorem 19.30: if `C' x y ≤ C x y` for every edge pair and the Markov chain with weights `C`
is recurrent, then the Markov chain with weights `C'` is also recurrent. -/
theorem randomWalkWithWeights_recurrent_of_edgeWeights_le
    {p p' : E → E → ℝ≥0∞} {C C' : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : E → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → E}
    [IsRandomWalkWithWeights p C] [IsRandomWalkWithWeights p' C']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hCC' : ∀ x y : E, C' x y ≤ C x y)
    (hrec : IsRecurrentMarkovChain P X) :
    IsRecurrentMarkovChain P' X' := sorry

-- Proof sketch: unfold `simpleGraphWeights`; if `H` is a subgraph of `G`, adjacency in `H`
-- implies adjacency in `G`, so the indicator weight of each edge in `H` is bounded by the
-- corresponding indicator weight in `G`.
/-- Unit edge weights are pointwise monotone under passage to a simple subgraph. -/
theorem simpleGraphWeights_le_of_isSubgraph {V : Type u}
    (G H : SimpleGraph V) (hHG : H ≤ G) :
    ∀ x y : V, simpleGraphWeights H x y ≤ simpleGraphWeights G x y := sorry

-- Proof sketch: apply `randomWalkWithWeights_recurrent_of_edgeWeights_le` to the unit weight
-- families of `G'` and of the induced graph `SimpleGraph.induce s G`; the subgraph assumption
-- gives the needed pointwise edge-weight inequality.
/-- Passing from a recurrent simple random walk on `G` to a simple random walk on a subgraph of an
induced graph preserves recurrence. -/
theorem simpleRandomWalk_recurrent_of_subgraph
    {G : SimpleGraph E} {s : Set E} [DiscreteMeasurableSpace ↑s] {G' : SimpleGraph s}
    {p : E → E → ℝ≥0∞} {p' : s → s → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : s → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → s}
    [IsSimpleRandomWalk p G] [IsSimpleRandomWalk p' G']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hsub : G' ≤ SimpleGraph.induce s G)
    (hrec : IsRecurrentMarkovChain P X) :
    IsRecurrentMarkovChain P' X' := sorry

end ProbabilityTheory
