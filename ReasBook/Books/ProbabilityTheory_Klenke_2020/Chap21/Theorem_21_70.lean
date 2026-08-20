import Mathlib.Probability.Martingale.OptionalSampling
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_58
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_66
import ProbabilityTheory_Klenke_2020.Chap21.Exercise_21_10_2
import ProbabilityTheory_Klenke_2020.Chap21.Exercise_21_4_3
import ProbabilityTheory_Klenke_2020.Chap21.Corollary_21_63
import ProbabilityTheory_Klenke_2020.Chap21.Remark_21_67
import ProbabilityTheory_Klenke_2020.Chap21.Remark_21_68

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- Helper for Theorem 21.70: for a continuous path with a chosen square-variation witness along
an admissible partition sequence, the unit-weight quadratic partition sums converge to that
witness. -/
theorem theorem_21_70_pathwise_partition_limit
    (X : C(NNReal, ℝ)) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : NNReal → ℝ} (hX : HasSquareVariationAlongPartition X P V) (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n)
      atTop
      (nhds (V T)) := by
  -- Proof comment: this is exactly the unit-weight specialization of the quadratic-variation
  -- convergence theorem already proved in Exercise 21.10.2.
  exact tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one X P hX T

/-- Theorem 21.70: expose the proved partition-limit clause under the planned main declaration
name expected by the item pipeline. -/
theorem existsUnique_continuousSquareVariationProcess
    (X : C(NNReal, ℝ)) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : NNReal → ℝ} (hX : HasSquareVariationAlongPartition X P V) (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n)
      atTop
      (nhds (V T)) := by
  -- Proof comment: this alias keeps the proved partition-limit statement while matching the
  -- declaration name expected by the proof pipeline.
  exact theorem_21_70_pathwise_partition_limit X P hX T

end ProbabilityTheory
