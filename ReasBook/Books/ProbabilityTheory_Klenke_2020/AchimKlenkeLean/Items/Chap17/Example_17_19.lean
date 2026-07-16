import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

section FiniteStateSimulation

variable {k : ℕ}

/-- The cumulative row sums of the `i`th row of the stochastic matrix `p`. -/
def stochasticMatrixSimulationCumulative
    (p : Fin k → Fin k → ℝ≥0∞) (i : Fin k) :
    Fin (k + 1) → ℝ :=
  Fin.partialSum fun j ↦ (p i j).toReal

/-- Example 17.19: for a finite stochastic matrix, the interval used to simulate the transition
from the state `i` to the state `j` is the half-open interval between the successive partial sums of
the `i`th row. Here `stochasticMatrixSimulationCumulative p i` is the textbook cumulative
function `r(i, ·)`, and the textbook states `{1, ..., k}` are encoded in Lean as `Fin k`. -/
def stochasticMatrixSimulationInterval
    (p : Fin k → Fin k → ℝ≥0∞) (i j : Fin k) : Set ℝ :=
  Set.Ico (stochasticMatrixSimulationCumulative p i j.castSucc)
    (stochasticMatrixSimulationCumulative p i j.succ)

-- Proof sketch: unfold `stochasticMatrixSimulationInterval`; membership in `Set.Ico` is exactly
-- the pair of inequalities cutting out the half-open interval between the two successive partial
-- sums.
/-- A real number lies in the simulation interval for `j` in row `i` exactly when it lies between
the two successive cumulative row sums. -/
theorem mem_stochasticMatrixSimulationInterval_iff
    (p : Fin k → Fin k → ℝ≥0∞) (i j : Fin k) {u : ℝ} :
    u ∈ stochasticMatrixSimulationInterval p i j ↔
      stochasticMatrixSimulationCumulative p i j.castSucc ≤ u ∧
        u < stochasticMatrixSimulationCumulative p i j.succ := by
  simp [stochasticMatrixSimulationInterval]

-- Proof sketch: apply `Fin.partialSum_succ`; the difference of two consecutive partial sums is the
-- corresponding summand, hence the matrix entry `p i j`.
/-- The width of the simulation interval for `j` in row `i` is exactly the transition probability
`p i j`. -/
theorem stochasticMatrixSimulationInterval_width
    (p : Fin k → Fin k → ℝ≥0∞) (i j : Fin k) :
    stochasticMatrixSimulationCumulative p i j.succ -
      stochasticMatrixSimulationCumulative p i j.castSucc = (p i j).toReal := by
  rw [sub_eq_iff_eq_add]
  simpa [stochasticMatrixSimulationCumulative, add_comm] using
    Fin.partialSum_succ (fun m ↦ (p i m).toReal) j

/-- The deterministic next-state map obtained by locating a driver value `u ∈ [0,1]` in the row
partition induced by the cumulative transition probabilities of the `i`th row of `p`. For `u < 1`,
the textbook half-open interval criterion is recovered by `stochasticMatrixSimulationState_eq_iff`;
at the boundary point `u = 1`, this definition returns the final state. -/
def stochasticMatrixSimulationState
    (p : Fin k → Fin k → ℝ≥0∞) (i : Fin k) (u : I) : Fin k :=
  let lower : Fin k → ℝ := fun j ↦ stochasticMatrixSimulationCumulative p i j.castSucc
  let j := Nat.findGreatest (fun n ↦ ∃ h : n < k, lower ⟨n, h⟩ ≤ (u : ℝ)) (k - 1)
  ⟨j, by
    have hj : j ≤ k - 1 := Nat.findGreatest_le (k - 1)
    have hk : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ i.1) (Nat.succ_le_of_lt i.2)
    exact lt_of_le_of_lt hj (Nat.sub_lt hk (by decide))⟩

-- Proof sketch: for `u : I` with `(u : ℝ) < 1`, the stochastic-row equation turns the cumulative
-- values into a genuine partition of the unit interval by the half-open intervals
-- `stochasticMatrixSimulationInterval p i j`; `Nat.findGreatest` selects exactly the label of
-- the interval containing `u`.
/-- For a driver value `u ∈ [0,1]` with `u < 1`, the simulation state is exactly the label of the
half-open interval containing `u`. -/
theorem stochasticMatrixSimulationState_eq_iff
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (i j : Fin k) (u : I) (hu : (u : ℝ) < 1) :
    stochasticMatrixSimulationState p i u = j ↔
      (u : ℝ) ∈ stochasticMatrixSimulationInterval p i j := by
  sorry

section RandomMapping

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The source-facing simulated step map `Rₙ(ω, i)` attached to the finite stochastic matrix `p`
and the unit-interval-valued drivers `Uₙ`. Its currying is chosen so that the owner construction
`stochasticMatrixTrajectory` can be applied directly to `fun n ↦ stochasticMatrixSimulationStep p U n`.
This is the intrinsic textbook interval simulation map. -/
def stochasticMatrixSimulationStep
    (p : Fin k → Fin k → ℝ≥0∞) (U : ℕ → Ω → I) (n : ℕ) : Ω → Fin k → Fin k :=
  fun ω i ↦ stochasticMatrixSimulationState p i (U n ω)

-- Proof sketch: for a uniform driver `U n : Ω → I`, the fiber of the simulated state `j` is,
-- away from the endpoint `1`, exactly the interval `stochasticMatrixSimulationInterval p i j`,
-- whose Lebesgue length is `(p i j).toReal`; the endpoint is sent to the final state by
-- `stochasticMatrixSimulationState`. This identifies the pushforward law with the `i`th row of
-- the canonical discrete kernel `discreteMatrixKernel p`.
/-- If the driving variable `U n` is uniform on `[0,1]`, then the simulated next state from `i`
has law given by the `i`th row of the canonical discrete kernel of `p`. -/
theorem hasLaw_stochasticMatrixSimulationStep
    (P : Measure Ω)
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (U : ℕ → Ω → I)
    (n : ℕ) (hU : HasLaw (U n) (volume : Measure I) P) (i : Fin k) :
    HasLaw (fun ω ↦ stochasticMatrixSimulationStep p U n ω i) (discreteMatrixKernel p i) P := by
  sorry

-- Proof sketch: evaluate the measure identity from `hasLaw_stochasticMatrixSimulationStep` on the
-- singleton `{j}` and rewrite with the explicit row of `discreteMatrixKernel p`.
/-- Equivalently, if `U n` is uniform on `[0,1]`, then the simulated next state satisfies the
textbook probability identity `P[R_n(i) = j] = p(i,j)`. -/
theorem measure_stochasticMatrixSimulationStep_eq_transitionProb
    (P : Measure Ω)
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (U : ℕ → Ω → I)
    (n : ℕ) (hU : HasLaw (U n) (volume : Measure I) P) (i j : Fin k) :
    P.real {ω | stochasticMatrixSimulationStep p U n ω i = j} = (p i j).toReal := by
  sorry

end RandomMapping
end FiniteStateSimulation

end ProbabilityTheory
