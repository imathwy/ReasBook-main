import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_17_22 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable (N : ℕ+)

/-- The type-`A` gene frequency corresponding to the Moran count state `i ∈ {0, ..., N}`. -/
def moranFrequency (i : Fin (N + 1)) : ℝ :=
  (i : ℝ) / N

/-- The one-step move probability `x (1 - x)` of the Moran model, written in terms of the
current frequency `x = i / N`. -/
def moranMoveProb : Fin (N + 1) → ℝ≥0∞ :=
  fun i ↦ ENNReal.ofReal <| moranFrequency N i * (1 - moranFrequency N i)

/-- The probability of staying at the same count in the discrete Moran model. -/
def moranStayProb : Fin (N + 1) → ℝ≥0∞ :=
  fun i ↦ ENNReal.ofReal <| (moranFrequency N i) ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ)

/-- Example 17.22: the discrete Moran model with population size `N` has state space
`Fin (N + 1)`, representing the frequencies `{0, 1 / N, ..., 1}`, and one-step transition matrix
given by moving from `i` to `i ± 1` with probability `x (1 - x)` and staying put with
probability `x^2 + (1 - x)^2`, where `x = i / N`. -/
def moranTransitionMatrix : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞
  | i, j =>
      if (j : ℕ) = (i : ℕ) + 1 then moranMoveProb N i
      else if j = i then moranStayProb N i
      else if (i : ℕ) = (j : ℕ) + 1 then moranMoveProb N i
      else 0

-- Proof sketch: for each count state `i`, only the three states `i - 1`, `i`, and `i + 1`
-- contribute; the corresponding probabilities add up to
-- `2 * i * (N - i) / N^2 + (i^2 + (N - i)^2) / N^2 = 1`.
/-- The discrete Moran transition matrix is stochastic. -/
theorem moranTransitionMatrix_isStochasticMatrix :
    IsStochasticMatrix (moranTransitionMatrix N) := sorry

/-- The predictable quadratic variation formula from Example 17.22, written as a process built
from the Moran frequencies. -/
def moranPredictableQuadraticVariation {Ω : Type u}
    (X : ℕ → Ω → Fin (N + 1)) : ℕ → Ω → ℝ :=
  fun n ω ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) *
    Finset.sum (Finset.range n) (fun i ↦
      moranFrequency N (X i ω) * (1 - moranFrequency N (X i ω)))

variable {N}

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Fin (N + 1) → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → Fin (N + 1)}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) P X]

local notation "M" => fun n ω ↦ moranFrequency N (X n ω)
local notation "ℱ" => processFiltration X

-- Proof sketch: use the one-step transition probabilities of the Moran chain to show that the
-- conditional expectation of the next frequency equals the current one.
/-- Any realization of the discrete Moran chain makes the gene-frequency process a martingale. -/
theorem moranFrequency_martingale
    (i : Fin (N + 1)) :
    Martingale M ℱ (P i : Measure Ω) := sorry

-- Proof sketch: verify the Chapter 10 square-variation witness axioms for the explicit Moran sum
-- process by using the frequency martingale and the one-step increment computation from Example
-- 17.22.
/-- Example 17.22: for a realization of the discrete Moran chain, the explicit Moran sum process
is a square-variation process of the frequency martingale. This is the
source-facing bridge to the chapter owner object `⟨M⟩[ℱ, μ]`. -/
theorem moranPredictableQuadraticVariation_isSquareVariationProcess
    (i : Fin (N + 1)) :
    IsSquareVariationProcess ℱ (P i : Measure Ω) M (moranPredictableQuadraticVariation N X) :=
  sorry

-- Proof sketch: apply the Chapter 10 uniqueness bridge from any square-variation witness to the
-- canonical square variation of the martingale `M`.
/-- For a realization of the discrete Moran chain, the canonical square variation of the
frequency martingale agrees almost everywhere with the explicit Moran formula `(17.12)` at each
fixed time. -/
theorem moranPredictableQuadraticVariation_eq
    (i : Fin (N + 1)) (n : ℕ) :
    ⟨M⟩[ℱ, (P i : Measure Ω)] n =ᵐ[(P i : Measure Ω)]
      moranPredictableQuadraticVariation N X n := sorry

end

end ProbabilityTheory
