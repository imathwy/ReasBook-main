import ProbabilityTheory_Klenke_2020.Items.Chap18.Exercise_18_4_6
import ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/- Domain-style sampling for Exercise 19.5.5:
- Primary domain: discrete-time Markov chains on finite graphs, viewed through electrical-network
  hitting probabilities.
- Inspected owner declarations:
  `HypercubeState`,
  `hypercubeFlipAt`,
  `simpleGraphWeights` / `IsSimpleRandomWalk`,
  `escapeToSetProbability`,
  `simpleLadder_hit_z_before_return_to_a_eq_inv_sqrt_three`.
- Best owner abstraction: the simple random walk on the Chapter 18 hypercube state space
  `HypercubeState 4`, with the source quantity `P_a[τ_z < τ_a]` expressed through the Chapter 19
  owner `escapeToSetProbability`.
- Primitive data: the Fig. 19.17 hypercube graph on `HypercubeState 4` and its distinguished
  vertices `a` and `z`.
  Derived API: the value of `escapeToSetProbability` for that walk.
- Source/core/bridge triage: the main item is `source-facing`; the graph and vertices model the
  concrete figure, while `escapeToSetProbability` is the existing `bridge/view` used to encode
  `P_a[τ_z < τ_a]` canonically. -/

/-- The adjacency relation of the hypercube in Fig. 19.17: two vertices are adjacent when one is
obtained from the other by flipping exactly one coordinate. -/
private def fig19_17Adj (x y : HypercubeState 4) : Prop :=
  ∃ i : Fin 4, y = hypercubeFlipAt x i

-- Proof sketch: flipping the same coordinate twice returns to the original vertex, so
-- `y = hypercubeFlipAt x i` implies `x = hypercubeFlipAt y i`.
/-- The Fig. 19.17 hypercube adjacency relation is symmetric. -/
private theorem fig19_17Adj_symm : Symmetric fig19_17Adj := sorry

-- Proof sketch: `hypercubeFlipAt x i` differs from `x` at the coordinate `i`, so no vertex is
-- adjacent to itself.
/-- The Fig. 19.17 hypercube adjacency relation is irreflexive. -/
private theorem fig19_17Adj_irrefl : Std.Irrefl fig19_17Adj := sorry

/-- The graph of Fig. 19.17, modeled as the 4-dimensional hypercube. -/
def fig19_17HypercubeGraph : SimpleGraph (HypercubeState 4) where
  Adj := fig19_17Adj
  symm := fig19_17Adj_symm
  loopless := fig19_17Adj_irrefl

/-- The distinguished starting vertex `a` in Fig. 19.17. -/
def fig19_17A : HypercubeState 4 := fun _ ↦ false

/-- The distinguished target vertex `z` in Fig. 19.17, opposite to `a` in the hypercube. -/
def fig19_17Z : HypercubeState 4 := fun _ ↦ true

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
variable {P : HypercubeState 4 → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → HypercubeState 4}
variable [IsSimpleRandomWalk p fig19_17HypercubeGraph]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: collapse the hypercube by Hamming distance from `a`; the resulting birth-death
-- chain on the four distance layers has boundary values `0` at `a` and `1` at `z`. Solving the
-- layer equations gives `P_a[τ_z < τ_a] = 3 / 8`.
/-- Exercise 19.5.5: for the simple random walk on the hypercube of Fig. 19.17, started at `a`,
the probability of hitting the opposite vertex `z` before the first strictly positive return to
`a` is `3 / 8`. -/
theorem fig19_17_hit_z_before_return_to_a_eq_three_eighths :
    escapeToSetProbability P X fig19_17A {fig19_17Z} =
      (3 / 8 : ℝ≥0∞) := sorry

end

end ProbabilityTheory
