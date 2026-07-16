import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_58
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_64

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

-- Proof sketch: first prove the claim for step functions that are constant on partition
-- intervals, where the weighted sums become finite linear combinations of the defining
-- convergence in `HasSquareVariationAlongPartition`. Then approximate a continuous `f` on
-- `[0, T]` uniformly by such step functions, use the vanishing mesh of `P`, and pass to the
-- Lebesgue--Stieltjes integral against the chosen representing measure `μV.measure`.
/-- Exercise 21.10.2: if `V` is a chosen square-variation path of `X` along the admissible
partition sequence `P`, then for every continuous `f : [0, ∞) → ℝ` the weighted quadratic
partition sums of `X` along `P` converge on `[0, T]` to the Lebesgue--Stieltjes integral of `f`
against a chosen Stieltjes-measure representation of `V`. -/
theorem tendsto_weightedPartitionQuadraticVariationApproximationUpTo
    (f : NNReal → ℝ) (hf : Continuous f) (X : PathSpace) {V : PathwiseProcess}
    (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (hX : HasSquareVariationAlongPartition X P V) :
    ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo f X P T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, f s ∂μV)) := sorry
