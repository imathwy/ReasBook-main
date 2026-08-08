import ProbabilityTheory_Klenke_2020.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_16
import ProbabilityTheory_Klenke_2020.Chap17.Example_17_55
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_43
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_49
import ProbabilityTheory_Klenke_2020.Chap18.Definition_18_1
import ProbabilityTheory_Klenke_2020.Chap18.Theorem_18_13
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The state space `{0,1}^N`, represented as Boolean-valued functions on `Fin N`. -/
abbrev HypercubeState (N : ℕ) : Type :=
  Fin N → Bool

/-- The vertex obtained from `x` by flipping the coordinate `i`. -/
def hypercubeFlipAt {N : ℕ} (x : HypercubeState N) (i : Fin N) : HypercubeState N :=
  Function.update x i (!(x i))

/-- Exercise 18.4.6 (1): for `N > 0`, the transition matrix of the lazy random walk on
`{0,1}^N` places mass `ε` at the current vertex and mass `(1 - ε) / N` at each vertex obtained by
flipping exactly one coordinate. -/
def hypercubeLazyTransitionMatrix (N : ℕ) [NeZero N] (ε : Set.Ioo (0 : ℝ) 1) :
    HypercubeState N → HypercubeState N → ℝ≥0∞ :=
  fun x y ↦
    if y = x then
      ENNReal.ofReal (ε : ℝ)
    else
      ∑ i : Fin N,
        if y = hypercubeFlipAt x i then
          ENNReal.ofReal ((1 - (ε : ℝ)) / N)
        else
          0

/-- The uniform distribution on the finite hypercube `{0,1}^N`. -/
def hypercubeUniformDistribution (N : ℕ) : ProbabilityMeasure (HypercubeState N) :=
  ⟨(PMF.uniformOfFintype (HypercubeState N)).toMeasure, inferInstance⟩

section LazyHypercube

variable (N : ℕ) [NeZero N] (ε : Set.Ioo (0 : ℝ) 1)

/-- The canonical Markov-kernel view of the lazy hypercube transition matrix. -/
abbrev hypercubeLazyKernel : Kernel (HypercubeState N) (HypercubeState N) :=
  discreteMatrixKernel (hypercubeLazyTransitionMatrix N ε)

/-- The modulus of the largest nontrivial eigenvalue of the lazy hypercube walk. -/
def hypercubeLazyConvergenceFactor : ℝ :=
  max (|1 - 2 * (1 - (ε : ℝ)) / N|) (|2 * (ε : ℝ) - 1|)

-- Proof sketch: for each fixed `x`, there are exactly `N` one-coordinate flips of `x`, each with
-- mass `(1 - ε) / N`, and together with the self-loop mass `ε` these contributions sum to `1`.
/-- The lazy hypercube transition matrix is stochastic. -/
theorem hypercubeLazyTransitionMatrix_isStochastic :
    IsStochasticMatrix (hypercubeLazyTransitionMatrix N ε) := sorry

/-- The lazy hypercube kernel is Markov. -/
theorem hypercubeLazyKernel_isMarkovKernel :
    IsMarkovKernel (hypercubeLazyKernel N ε) := by
  simpa [hypercubeLazyKernel] using
    (discreteMatrixKernel_isMarkovKernel
      (hypercubeLazyTransitionMatrix N ε)
      (hypercubeLazyTransitionMatrix_isStochastic N ε))

-- Proof sketch: every state has a one-step self-loop of probability `ε > 0`, so each state has a
-- positive return time `1`, which forces period `1`.
/-- Exercise 18.4.6 (2): the lazy random walk on the hypercube is aperiodic. -/
theorem hypercubeLazyKernel_isAperiodic :
    IsAperiodic (hypercubeLazyKernel N ε) := sorry

-- Proof sketch: if `x` and `y` differ in `k` coordinates, successively flip those coordinates.
-- Each prescribed flip has probability `(1 - ε) / N > 0`, so concatenating them gives a
-- positive-probability path from `x` to `y`.
/-- Exercise 18.4.6 (3): the lazy random walk on the hypercube is irreducible with respect to
counting measure. -/
theorem hypercubeLazyKernel_isIrreducible :
    Kernel.IsIrreducible (Measure.count : Measure (HypercubeState N)) (hypercubeLazyKernel N ε) :=
  sorry

-- Proof sketch: the transition matrix is symmetric, hence doubly stochastic, so averaging over
-- all hypercube vertices is preserved by one step.
/-- Exercise 18.4.6 (4): the uniform distribution on `{0,1}^N` is invariant for the lazy
hypercube walk. -/
theorem hypercubeUniformDistribution_isInvariant :
    Kernel.Invariant (hypercubeLazyKernel N ε)
      (hypercubeUniformDistribution N : Measure (HypercubeState N)) := sorry

-- Proof sketch: combine the invariance of the uniform law with irreducibility and the Chapter
-- 17 uniqueness theorem for invariant distributions of irreducible discrete kernels.
/-- Any invariant distribution of the lazy hypercube walk is the uniform distribution. -/
theorem hypercubeLazyKernel_invariantDistribution_eq_uniform
    (μ : ProbabilityMeasure (HypercubeState N))
    (hμ : Kernel.Invariant (hypercubeLazyKernel N ε) (μ : Measure (HypercubeState N))) :
    μ = hypercubeUniformDistribution N := by
  let κ : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε
  let _ : IsMarkovKernel κ := by
    simpa [κ] using hypercubeLazyKernel_isMarkovKernel N ε
  let _ : Kernel.IsIrreducible (Measure.count : Measure (HypercubeState N)) κ := by
    simpa [κ] using hypercubeLazyKernel_isIrreducible N ε
  refine eq_of_isInvariantDistribution_of_irreducible κ ?_ ?_
  · simpa [κ] using hμ
  · simpa [κ] using hypercubeUniformDistribution_isInvariant N ε

-- Proof sketch: diagonalize the walk by the Walsh basis on `{0,1}^N`; the eigenvalues are
-- `1 - 2 (1 - ε) k / N` for `0 ≤ k ≤ N`, so the largest nontrivial modulus is
-- `hypercubeLazyConvergenceFactor N ε`; translating the spectral estimate to the chapter-owner
-- iterate law gives geometric convergence in total variation.
/-- Exercise 18.4.6 (5): the lazy hypercube walk converges exponentially fast to the uniform
distribution in total variation, with rate given by the largest nontrivial eigenvalue modulus. -/
theorem hypercubeLazyKernel_totalVariation_exponential_bound :
    let _ : IsMarkovKernel (hypercubeLazyKernel N ε) := hypercubeLazyKernel_isMarkovKernel N ε
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          ∀ μ : ProbabilityMeasure (HypercubeState N),
            let κn : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε ^ n
            totalVariationDistance
              (⟨κn ∘ₘ (μ : Measure (HypercubeState N)),
                inferInstance⟩ : ProbabilityMeasure (HypercubeState N))
              (hypercubeUniformDistribution N) ≤
            C * hypercubeLazyConvergenceFactor N ε ^ n := sorry

end LazyHypercube

end ProbabilityTheory
