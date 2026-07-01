import AchimKlenkeLean.Items.Chap19.Example_19_10
import AchimKlenkeLean.Items.Chap19.Theorem_19_6
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory.DiscreteMarkovChain

/-
`source-facing`: the two-hexagon honeycomb graph together with the distinguished vertices
`one`, `zero`, and `start = x`.
`core/canonical`: the Chapter 19 graph-walk owner `IsSimpleRandomWalk`, the discrete-kernel owner
`discreteMatrixKernel`, and the first-hit owner `F_A`.
`bridge/view`: the concrete transition matrix `honeycombTransitionMatrix`, obtained from the unit
conductances of the honeycomb graph.
-/

/-- The ten vertices of the two-hexagon honeycomb graph from Exercise 19.5.2, with distinguished
vertices `one`, `zero`, and `start = x`. -/
inductive HoneycombVertex
  | one
  | leftUpper
  | sharedUpper
  | start
  | lowerMiddle
  | leftLower
  | rightUpperLeft
  | rightUpperRight
  | zero
  | rightLower
  deriving DecidableEq, Fintype

open HoneycombVertex

/-- The finite honeycomb state space carries the discrete measurable structure. -/
instance : MeasurableSpace HoneycombVertex := ⊤

/-- The measurable structure on the honeycomb state space is discrete. -/
instance : DiscreteMeasurableSpace HoneycombVertex := by
  infer_instance

/-- The undirected edges of the two-hexagon honeycomb graph, listed once each. -/
private def honeycombEdges : Finset (HoneycombVertex × HoneycombVertex) :=
  { (one, leftUpper),
    (one, leftLower),
    (leftUpper, sharedUpper),
    (sharedUpper, start),
    (sharedUpper, rightUpperLeft),
    (start, lowerMiddle),
    (start, rightLower),
    (lowerMiddle, leftLower),
    (rightUpperLeft, rightUpperRight),
    (rightUpperRight, zero),
    (zero, rightLower) }

/-- The adjacency relation of the two-hexagon honeycomb graph. -/
private def honeycombAdj (x y : HoneycombVertex) : Prop :=
  (x, y) ∈ honeycombEdges ∨ (y, x) ∈ honeycombEdges

private theorem honeycombAdj_symm : Symmetric honeycombAdj := by
  intro x y hxy
  simpa [honeycombAdj, or_comm] using hxy

private theorem honeycombAdj_irrefl : Std.Irrefl honeycombAdj := by
  exact ⟨fun x ↦ by
    cases x <;> simp [honeycombAdj, honeycombEdges]⟩

/-- The two-hexagon honeycomb graph from Exercise 19.5.2. -/
def honeycombGraph : SimpleGraph HoneycombVertex where
  Adj := honeycombAdj
  symm := honeycombAdj_symm
  loopless := honeycombAdj_irrefl

/-- The unit conductance family of the honeycomb graph. -/
def honeycombConductance : HoneycombVertex → HoneycombVertex → ℝ≥0∞ :=
  simpleGraphWeights honeycombGraph

/-- The simple random-walk transition matrix on the honeycomb graph. -/
def honeycombTransitionMatrix : HoneycombVertex → HoneycombVertex → ℝ≥0∞ :=
  conductanceTransitionMatrix honeycombConductance

-- Proof sketch: each honeycomb vertex has degree `2` or `3`, so the normalized unit-conductance
-- walk on `honeycombGraph` is exactly the simple random walk on that graph.
/-- The honeycomb transition matrix is the Chapter 19 simple-random-walk owner on
`honeycombGraph`. -/
theorem honeycombTransitionMatrix_isSimpleRandomWalk :
    IsSimpleRandomWalk honeycombTransitionMatrix honeycombGraph := sorry

/-- The honeycomb transition matrix is stochastic. -/
theorem honeycombTransitionMatrix_isStochastic :
    IsStochasticMatrix honeycombTransitionMatrix :=
  IsRandomWalkWithWeights.isStochasticMatrix honeycombTransitionMatrix_isSimpleRandomWalk

/-- The discrete kernel associated with `honeycombTransitionMatrix` is Markov. -/
instance : IsMarkovKernel (discreteMatrixKernel honeycombTransitionMatrix) :=
  discreteMatrixKernel_isMarkovKernel _ honeycombTransitionMatrix_isStochastic

section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : HoneycombVertex → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → HoneycombVertex}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel honeycombTransitionMatrix ^ n) P X]

-- Proof sketch: either reduce the electrical network by star-triangle moves and apply the
-- effective-resistance formula for the corresponding Dirichlet problem, or kill the chain at
-- `{one, zero}` and compute the Green matrix entry for the matrix inverse `(I - p̄)⁻¹`. Both
-- methods yield the same value `8 / 17`.
/-- Exercise 19.5.2: for the simple random walk on the two-hexagon honeycomb graph, started at the
distinguished vertex `x`, the probability of visiting `1` before `0` is `8 / 17`; this is the
value the exercise asks to recover both by network reduction and by matrix inversion. -/
theorem honeycomb_start_hittingProbability_one_before_zero :
    F_A P X ({zero} : Set HoneycombVertex) start one = (8 : ℝ) / 17 := sorry

end

end ProbabilityTheory.DiscreteMarkovChain
