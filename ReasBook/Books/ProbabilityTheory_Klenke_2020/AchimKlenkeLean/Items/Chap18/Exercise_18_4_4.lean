import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory.DiscreteMarkovChain

/-- The transition matrix of the three-state chain from Exercise 18.4.4, written on `Fin 3` with
indices `0`, `1`, `2` corresponding to the textbook states `1`, `2`, `3`. -/
def three_state_transition_matrix : Fin 3 → Fin 3 → ℝ≥0∞ :=
  ![![(1 : ℝ≥0∞) / 2, (1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 6],
    ![(1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 3],
    ![0, (3 : ℝ≥0∞) / 4, (1 : ℝ≥0∞) / 4]]

/-- The same transition matrix regarded as a real matrix for spectral computations. -/
abbrev three_state_transition_matrix_real : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j ↦ (three_state_transition_matrix i j).toReal

/-- The one-step kernel associated with the Exercise 18.4.4 transition matrix. -/
abbrev three_state_transition_kernel : Kernel (Fin 3) (Fin 3) :=
  discreteMatrixKernel three_state_transition_matrix

-- Proof sketch: evaluate the three row sums of `three_state_transition_matrix`; they are
-- `1 / 2 + 1 / 3 + 1 / 6`, `1 / 3 + 1 / 3 + 1 / 3`, and `0 + 3 / 4 + 1 / 4`, each equal to `1`.
/-- The Exercise 18.4.4 transition matrix is stochastic. -/
theorem three_state_transition_matrix_isStochastic :
    IsStochasticMatrix three_state_transition_matrix := sorry

/-- The weights of the invariant distribution of the three-state chain. -/
def three_state_invariant_weights : Fin 3 → ℝ≥0∞ :=
  ![(18 : ℝ≥0∞) / 61, (27 : ℝ≥0∞) / 61, (16 : ℝ≥0∞) / 61]

-- Proof sketch: evaluate the finite sum over the three states and simplify
-- `18 / 61 + 27 / 61 + 16 / 61 = 1`.
/-- The explicit invariant weights form a probability vector. -/
theorem three_state_invariant_weights_sum :
    Finset.univ.sum three_state_invariant_weights = 1 := sorry

/-- Exercise 18.4.4 (1): the invariant distribution of the chain is the probability law assigning
masses `18 / 61`, `27 / 61`, and `16 / 61` to the states `1`, `2`, and `3`. -/
def three_state_invariant_distribution : ProbabilityMeasure (Fin 3) :=
  ⟨(PMF.ofFintype three_state_invariant_weights three_state_invariant_weights_sum).toMeasure,
    inferInstance⟩

-- Proof sketch: compute the image of `three_state_invariant_distribution` under the one-step
-- kernel `three_state_transition_kernel`; the stationarity equations reduce to the three linear
-- identities defining the weights `18 / 61`, `27 / 61`, and `16 / 61`.
/-- The explicit law with weights `18 / 61`, `27 / 61`, and `16 / 61` is invariant for the
one-step kernel of the chain. -/
theorem three_state_invariant_distribution_isInvariant :
    Kernel.Invariant three_state_transition_kernel
      (three_state_invariant_distribution : Measure (Fin 3)) := sorry

/-- Exercise 18.4.4 (2): the exponential convergence rate of the chain is
`(1 + √41) / 24`. -/
def three_state_exponential_convergence_rate : ℝ :=
  (1 + Real.sqrt 41) / 24

-- Proof sketch: compute the characteristic polynomial of `three_state_transition_matrix_real`,
-- factor it as `(x - 1) * (72 x^2 - 6 x - 5) / 72`, and solve the quadratic factor. The two
-- nontrivial eigenvalues are `(1 ± √41) / 24`, so the spectral decay rate is the larger modulus
-- `(1 + √41) / 24`.
/-- The real spectrum of the transition matrix consists of `1` and the two nontrivial eigenvalues
`(1 - √41) / 24` and `(1 + √41) / 24`. -/
theorem three_state_spectrum_eq :
    spectrum ℝ three_state_transition_matrix_real =
      ({1, (1 - Real.sqrt 41) / 24, three_state_exponential_convergence_rate} : Set ℝ) := sorry

end ProbabilityTheory.DiscreteMarkovChain
