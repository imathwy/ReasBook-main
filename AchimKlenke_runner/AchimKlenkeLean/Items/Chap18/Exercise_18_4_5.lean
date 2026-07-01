import AchimKlenkeLean.Items.Chap08.Example_8_27
import AchimKlenkeLean.Items.Chap17.Example_17_55
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap18.Definition_18_1
import AchimKlenkeLean.Items.Chap18.Theorem_18_13
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

private theorem fin_pos {N : ℕ} (i : Fin N) : 0 < N :=
  lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt i.2)

private theorem pos_of_two_le {N : ℕ} (hN : 2 ≤ N) : 0 < N :=
  lt_of_lt_of_le (by decide : 0 < 2) hN

/-- The transition matrix of the cyclic lazy walk on `Fin N`: from `i` the chain jumps to the
cyclic successor `finRotate N i` with probability `r` and stays put with probability `1 - r`. The
sum form handles the degenerate one-point cycle as well. -/
def cyclicLazyWalkTransitionMatrix (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j ↦
    (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
      (if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0)

/-- The Markov kernel associated with the cyclic lazy walk transition matrix. -/
abbrev cyclicLazyWalkKernel (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Kernel (Fin N) (Fin N) :=
  discreteMatrixKernel (cyclicLazyWalkTransitionMatrix N r)

/-- The uniform probability distribution on the finite cyclic state space `Fin N`. -/
def cyclicLazyWalkInvariantDistribution (N : ℕ) (hN : 0 < N) : ProbabilityMeasure (Fin N) :=
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  ⟨(PMF.uniformOfFintype (Fin N)).toMeasure, inferInstance⟩

/-- The explicit spectral radius of the largest nontrivial Fourier mode of the cyclic lazy walk. -/
def cyclicLazyWalkExponentialRate (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  if _ : N ≤ 1 then 0 else Real.sqrt (1 - 4 * r * (1 - r) * Real.sin (Real.pi / N) ^ 2)

-- Proof sketch: this is immediate from the definition of
-- `cyclicLazyWalkTransitionMatrix`.
/-- The cyclic lazy walk matrix is the sum of the jump-to-successor and hold contributions. -/
theorem cyclicLazyWalkTransitionMatrix_apply
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    cyclicLazyWalkTransitionMatrix N r i j =
      (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
        (if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0) := rfl

-- Proof sketch: evaluate `cyclicLazyWalkKernel N r i` on the singleton `{j}`, expand the defining
-- sum of Dirac measures, and keep only the `j`-th summand.
/-- Evaluating the cyclic lazy walk kernel at a singleton recovers the corresponding matrix entry.
-/
theorem cyclicLazyWalkKernel_apply_singleton
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    cyclicLazyWalkKernel N r i {j} = cyclicLazyWalkTransitionMatrix N r i j := sorry

-- Proof sketch: for each row, only the successor and holding terms can contribute; their masses
-- are nonnegative and add up to `1`.
/-- The cyclic lazy walk transition matrix is stochastic. -/
theorem cyclicLazyWalkTransitionMatrix_isStochastic
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsStochasticMatrix (cyclicLazyWalkTransitionMatrix N r) := sorry

/-- The cyclic lazy walk kernel is Markov. -/
instance cyclicLazyWalkKernel.instIsMarkovKernel
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsMarkovKernel (cyclicLazyWalkKernel N r) := by
  simpa [cyclicLazyWalkKernel] using
    (discreteMatrixKernel_isMarkovKernel
      (cyclicLazyWalkTransitionMatrix N r)
      (cyclicLazyWalkTransitionMatrix_isStochastic N r))

-- Proof sketch: positive forward-step probability lets the chain reach every state by repeated
-- cyclic increments, so every state communicates with every other.
/-- The cyclic lazy walk is irreducible as soon as the forward jump probability is positive. -/
theorem cyclicLazyWalk_isIrreducible
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.IsIrreducible (Measure.count : Measure (Fin N)) (cyclicLazyWalkKernel N r) := sorry

-- Proof sketch: each state has a positive one-step return probability through the holding move,
-- so the period of every state is `1`.
/-- The positive holding probability makes the cyclic lazy walk aperiodic. -/
theorem cyclicLazyWalk_isAperiodic
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    IsAperiodic (cyclicLazyWalkKernel N r) := sorry

-- Proof sketch: the uniform PMF on `Fin N` gives every state the same mass, namely the reciprocal
-- of the cardinality of `Fin N`.
/-- The uniform invariant distribution assigns mass `N⁻¹` to each singleton of `Fin N`. -/
theorem cyclicLazyWalkInvariantDistribution_apply_singleton
    (N : ℕ) (i : Fin N) :
    (cyclicLazyWalkInvariantDistribution N (fin_pos i) : Measure (Fin N)) {i} =
      (N : ℝ≥0∞)⁻¹ := sorry

-- Proof sketch: the transition matrix is circulant, so averaging over all starting states is
-- preserved by one step; equivalently, the uniform law is a left eigenvector with eigenvalue `1`.
/-- The uniform distribution on `Fin N` is invariant for the cyclic lazy walk. -/
theorem cyclicLazyWalkInvariantDistribution_isInvariant
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.Invariant (cyclicLazyWalkKernel N r)
      (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) := sorry

-- Proof sketch: the nontrivial Fourier eigenvalues are `1 - r + r ζ` with `ζ^N = 1` and
-- `ζ ≠ 1`; for `2 ≤ N`, their moduli are strictly less than `1`, and the largest
-- one is the declared rate.
/-- The explicit spectral rate of the cyclic lazy walk is strictly smaller than `1` in the
nontrivial lazy regime. -/
theorem cyclicLazyWalkExponentialRate_lt_one
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) :
    cyclicLazyWalkExponentialRate N r < 1 := sorry

-- Proof sketch: diagonalize the circulant kernel by the Fourier basis on `Fin N`; the nontrivial
-- eigenvalues are `1 - r + r ζ`, so their largest modulus is
-- `cyclicLazyWalkExponentialRate N r`; then translate the spectral estimate to the chapter-owner
-- kernel iterate law.
/-- Exercise 18.4.5: for the lazy cyclic random walk on `Fin N` with forward-jump probability
`r ∈ (0,1)`, the walk is irreducible and aperiodic, the uniform distribution is invariant, and the
convergence to equilibrium is exponential with explicit rate
`cyclicLazyWalkExponentialRate N r`. -/

theorem cyclicLazyWalk_exponentialConvergence
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1)
    (μ : ProbabilityMeasure (Fin N)) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          let κn : Kernel (Fin N) (Fin N) := cyclicLazyWalkKernel N r ^ n
          totalVariationDistance
            (⟨κn ∘ₘ (μ : Measure (Fin N)), inferInstance⟩ :
              ProbabilityMeasure (Fin N))
            (cyclicLazyWalkInvariantDistribution N (pos_of_two_le hN))
            ≤ C * (cyclicLazyWalkExponentialRate N r) ^ n := sorry

end ProbabilityTheory
