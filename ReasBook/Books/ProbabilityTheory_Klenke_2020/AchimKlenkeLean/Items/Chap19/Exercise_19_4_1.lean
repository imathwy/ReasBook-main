import ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_47
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_39
import ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: `latticeGraph_adj_iff` says that adjacent vertices differ by `±1` in exactly one
-- coordinate and agree in all others; that coordinatewise description is equivalent to the
-- update-form textbook description used below.
/-- Adjacency in the canonical lattice graph is exactly the one-coordinate `±1` update condition
used in the textbook nearest-neighbor description. -/
theorem latticeGraph_adj_iff_update {d : ℕ} (x y : LatticePoint d) :
    (latticeGraph d).Adj x y ↔
      ∃ i : Fin d, y = Function.update x i (x i + 1) ∨ y = Function.update x i (x i - 1) := sorry

section Exercise1941

variable {d : ℕ}
variable (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
variable [NeZero d]
variable [IsMarkovProcessRealization
  (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF d).toMeasure ^ n) P X]

-- Proof sketch: use the canonical Chapter 19 finite-boundary conductance formula
-- `conductance C x0 * escapeToSetProbability P X x0 {x1}` for the singleton boundary `{x1}`,
-- compute the local conductance at `x0` as `2d`, and identify the corresponding hitting
-- probability with the symmetry value `1 / 2` for a neighboring edge.
/-- Exercise 19.4.1 (1): in the unit nearest-neighbor network on `ℤ^d`, the canonical
finite-boundary conductance from `x0` to the singleton boundary `{x1}` is `d` whenever `x0` and
`x1` are neighbors. -/
theorem latticeNearestNeighbor_effectiveConductance_eq_dimension
    {x0 x1 : LatticePoint d} (hneighbor : (latticeGraph d).Adj x0 x1) :
    conductance (simpleGraphWeights (latticeGraph d)) x0 *
        escapeToSetProbability P X x0 ({x1} : Set (LatticePoint d)) =
      (d : ℝ≥0∞) := sorry

-- Proof sketch: when `d ≤ 2`, the simple symmetric walk on `ℤ^d` is recurrent. Starting from
-- `x0`, the first positive hit of the two-point boundary `{x0, x1}` is therefore almost sure, and
-- symmetry across the edge `{x0, x1}` makes the two possible first hits equiprobable.
/-- Exercise 19.4.1 (2): if `d ≤ 2`, then for symmetric simple random walk on `ℤ^d` started at a
neighbor `x0` of `x1`, the probability of hitting `x1` before the first positive-time return to
`x0` is `1 / 2`. -/
theorem simpleRandomWalk_escapeBeforeNeighbor_eq_half_of_dimension_le_two
    (hd : d ≤ 2) {x0 x1 : LatticePoint d} (hneighbor : (latticeGraph d).Adj x0 x1) :
    escapeToSetProbability P X x0 ({x1} : Set (LatticePoint d)) = (1 / 2 : ℝ≥0∞) := sorry

-- Proof sketch: for `d ≥ 3`, condition on the event that the walk ever re-enters the two-point
-- boundary `{x0, x1}` after time `0`. By symmetry of the edge `{x0, x1}`, the two mutually
-- exclusive first-hit alternatives `τ_{x1} < τ_{x0}` and `τ_{x0} < τ_{x1}` have equal mass inside
-- that conditioning event, yielding the displayed conditional-probability identity.
/-- Exercise 19.4.1 (3): if `d ≥ 3`, then conditioning on the event that the walk started from
`x0` ever hits one of the two neighbors `x0` or `x1` again at positive time, the event
`τ_{x1} < τ_{x0}` has conditional probability `1 / 2`. This is encoded by the identity
`P[τ_{x1} < τ_{x0}] = (1 / 2) P[τ_{ {x0,x1} } < ∞]`. -/
theorem simpleRandomWalk_escapeBeforeNeighbor_eq_half_mul_hitPairProbability_of_three_le_dimension
    (hd : 3 ≤ d) {x0 x1 : LatticePoint d} (hneighbor : (latticeGraph d).Adj x0 x1) :
    escapeToSetProbability P X x0 ({x1} : Set (LatticePoint d)) =
      (1 / 2 : ℝ≥0∞) *
        (P x0 : Measure Ω) {ω |
          hittingAfter X ({x0, x1} : Set (LatticePoint d)) 1 ω < ⊤} := sorry

end Exercise1941

end ProbabilityTheory
