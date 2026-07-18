import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Example_9_13
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable section

section

variable {Y : ℕ → Ω → ℝ}
variable (hY_meas : ∀ n, Measurable (Y n))

local notation "S" => partialSum Y

private theorem partialSumStronglyMeasurable
    (hY_meas : ∀ n, Measurable (Y n)) (n : ℕ) : StronglyMeasurable (S n) :=
  (partialSum_measurable Y hY_meas n).stronglyMeasurable

local notation "ℱY" =>
  Filtration.natural S (partialSumStronglyMeasurable hY_meas)

section

variable [IsProbabilityMeasure μ]

-- Proof sketch: reuse the upstream cumulative-sum martingale owner theorem for centered
-- independent increments on a probability space, then transport from the increment filtration to
-- the natural filtration of the partial-sum process.
/-- Example 10.6 (1): if `Y₁, Y₂, …` are independent, centered, integrable real random variables
on a probability space, then the partial-sum process `Xₙ = Y₁ + ⋯ + Yₙ` is a martingale for its
natural filtration. In the canonical `0`-based Lean indexing, the textbook process is
`partialSum Y`. -/
theorem independentCenteredPartialSums_martingale
    (hY_int : ∀ n, Integrable (Y n) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    Martingale S ℱY μ := sorry

end

-- Proof sketch: deduce square integrability of each finite partial sum from the square
-- integrability of the increments and the finite-sum expansion of the process.
/-- Example 10.6 (2): if the increments are square integrable, then each partial sum `Xₙ` is
square integrable. -/
theorem independentCenteredPartialSums_squareIntegrable
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) :
    ∀ n, Integrable (fun ω ↦ (S n ω) ^ 2) μ := sorry

local notation "A" => fun n ↦ fun _ ↦ ∑ i ∈ Finset.range n, ∫ ξ, (Y i ξ) ^ 2 ∂μ

-- Proof sketch: the variance-sum process is deterministic, so it is adapted one step in advance
-- and hence predictable for the natural filtration of the partial sums; no independence,
-- centeredness, or integrability hypotheses are needed here.
/-- Example 10.6 (3): the deterministic variance-sum process
`Aₙ = ∑_{i=1}^n E[Yᵢ^2]` is predictable for the natural filtration of the partial sums. -/
theorem independentCenteredPartialSums_deterministicSquareVariation_predictable :
    IsStronglyPredictable ℱY A := by
  refine IsStronglyPredictable.of_measurable_add_one stronglyMeasurable_const fun _ ↦ ?_
  exact stronglyMeasurable_const

section

variable [IsProbabilityMeasure μ]

-- Proof sketch: combine the partial-sum martingale statement with the chapter's square-variation
-- owner abstraction, then identify the predictable compensator of the squared process with the
-- deterministic second-moment sum singled out in the example.
/-- The deterministic variance-sum process
`Aₙ = ∑_{i=1}^n E[Yᵢ^2]` is the square-variation process of the partial-sum martingale from
Example 10.6. This is the canonical chapter-level packaging of parts (3) and (4). -/
theorem independentCenteredPartialSums_deterministicSquareVariation_isSquareVariationProcess
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    IsSquareVariationProcess ℱY μ S A := sorry

-- Proof sketch: read off the compensated-square martingale from the square-variation owner
-- statement for the deterministic compensator `A`.
/-- Example 10.6 (4): subtracting the deterministic variance-sum process from `Xₙ^2` yields a
martingale. This is the compensated squared process from the textbook example. -/
theorem independentCenteredPartialSums_squareMinusDeterministicSquareVariation_martingale
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    Martingale (fun n ω ↦ (S n ω) ^ 2 - A n ω) ℱY μ :=
  (independentCenteredPartialSums_deterministicSquareVariation_isSquareVariationProcess
      hY_meas hY_sq_int hY_mean_zero hY_indep).martingale_sq_sub

-- Proof sketch: apply the uniqueness companion for the square-variation owner object to identify
-- the canonical square variation `⟨S⟩[ℱY, μ]` with the deterministic process `A`; this is the
-- source-facing formula for the predictable part of the squared partial sums.
/-- At each fixed time, the canonical square variation `⟨S⟩[ℱY, μ]` of the squared partial-sum
martingale agrees almost everywhere with the deterministic sum of the second moments of the
increments. This is the explicit `Aₙ` formula singled out in the textbook example. -/
theorem independentCenteredPartialSums_squareVariation_ae_eq_deterministicSquareVariation
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    ∀ n, ⟨S⟩[ℱY, μ] n =ᵐ[μ] A n :=
  IsSquareVariationProcess.predictablePart_sq_ae_eq
    (independentCenteredPartialSums_deterministicSquareVariation_isSquareVariationProcess
      hY_meas hY_sq_int hY_mean_zero hY_indep)
    (independentCenteredPartialSums_squareIntegrable hY_sq_int)

end

end
