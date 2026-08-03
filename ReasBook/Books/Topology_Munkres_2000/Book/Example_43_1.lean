module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Cauchy

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational

public section

open Filter Topology

/-- The rational truncation of `Real.sqrt 2` to `n + 1` decimal places. -/
noncomputable def sqrtTwoDecimalApprox (n : ℕ) : ℚ :=
  ((⌊(10 : ℝ) ^ (n + 1) * Real.sqrt 2⌋ : ℤ) : ℚ) / (10 : ℚ) ^ (n + 1)

/-- Helper for Example 43.1: the decimal truncation lies below `Real.sqrt 2`,
with error less than the reciprocal of its decimal denominator. -/
lemma sqrtTwoDecimalApprox_error_bounds (n : ℕ) :
    0 ≤ Real.sqrt 2 - (sqrtTwoDecimalApprox n : ℝ) ∧
      Real.sqrt 2 - (sqrtTwoDecimalApprox n : ℝ) < (10 : ℝ)⁻¹ ^ (n + 1) := by
  -- Normalize the rational truncation to a real quotient once.
  have hcast :
      (sqrtTwoDecimalApprox n : ℝ) =
        (⌊(10 : ℝ) ^ (n + 1) * Real.sqrt 2⌋ : ℝ) / (10 : ℝ) ^ (n + 1) := by
    simp [sqrtTwoDecimalApprox]
  have hdenom : 0 < (10 : ℝ) ^ (n + 1) := by
    positivity
  constructor
  · -- Divide the lower floor inequality by the positive decimal denominator.
    have hfloor := Int.floor_le ((10 : ℝ) ^ (n + 1) * Real.sqrt 2)
    rw [hcast, sub_nonneg, div_le_iff₀ hdenom]
    simpa [mul_comm] using hfloor
  · -- Divide the strict upper floor inequality by the same denominator.
    have hfloor := Int.lt_floor_add_one ((10 : ℝ) ^ (n + 1) * Real.sqrt 2)
    have hinv : (10 : ℝ)⁻¹ ^ (n + 1) = 1 / (10 : ℝ) ^ (n + 1) := by
      simp [div_eq_mul_inv, inv_pow]
    rw [hcast, sub_lt_iff_lt_add, hinv, ← add_div]
    apply (lt_div_iff₀ hdenom).2
    simpa only [add_comm, mul_comm, Nat.add_comm] using hfloor

/-- The first assertion of Example 43.1: the finite decimal truncations converge
in `ℝ` to `Real.sqrt 2`. -/
theorem tendsto_sqrtTwoDecimalApprox :
    Tendsto (fun n ↦ (sqrtTwoDecimalApprox n : ℝ)) atTop (𝓝 (Real.sqrt 2)) := by
  -- The geometric error bound tends to zero.
  have hgeometric :
      Tendsto (fun n : ℕ ↦ (10 : ℝ)⁻¹ ^ (n + 1)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ ↦ (10 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [pow_succ, zero_mul] using hpow.mul_const (10 : ℝ)⁻¹
  have herror :
      Tendsto (fun n : ℕ ↦ Real.sqrt 2 - (sqrtTwoDecimalApprox n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ (sqrtTwoDecimalApprox_error_bounds n).1
    · exact Eventually.of_forall fun n ↦ (sqrtTwoDecimalApprox_error_bounds n).2.le
    · exact hgeometric
  -- Subtracting the vanishing error recovers the truncations.
  have hconst : Tendsto (fun _ : ℕ ↦ Real.sqrt 2) atTop (𝓝 (Real.sqrt 2)) :=
    tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hconst.sub herror

/-- The second assertion of Example 43.1: the finite decimal truncations form a
Cauchy sequence in `ℚ` with its usual metric. -/
theorem cauchySeq_sqrtTwoDecimalApprox : CauchySeq sqrtTwoDecimalApprox := by
  -- Real convergence gives a real Cauchy estimate, which the rational cast reflects.
  have hreal : CauchySeq (fun n ↦ (sqrtTwoDecimalApprox n : ℝ)) :=
    tendsto_sqrtTwoDecimalApprox.cauchySeq
  rw [Metric.cauchySeq_iff'] at hreal ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hreal ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa only [Rat.dist_cast] using hN n hn

/-- The third assertion of Example 43.1: the finite decimal truncations do not
converge in `ℚ`. -/
theorem not_tendsto_sqrtTwoDecimalApprox :
    ¬ ∃ q : ℚ, Tendsto sqrtTwoDecimalApprox atTop (𝓝 q) := by
  -- A rational limit would also be the real limit after applying the continuous cast.
  rintro ⟨q, hq⟩
  have hqReal :
      Tendsto (fun n ↦ (sqrtTwoDecimalApprox n : ℝ)) atTop (𝓝 (q : ℝ)) := by
    simpa only [Function.comp_def] using (Rat.continuous_coe_real.tendsto q).comp hq
  have hsqrt : Real.sqrt 2 = (q : ℝ) :=
    tendsto_nhds_unique tendsto_sqrtTwoDecimalApprox hqReal
  -- This equality exhibits `Real.sqrt 2` as a rational cast, contradicting irrationality.
  exact irrational_sqrt_two ⟨q, hsqrt.symm⟩

/-- Example 43.1 (4): The rational numbers with their usual metric are not a
complete metric space. -/
theorem not_completeSpace_rat : ¬ CompleteSpace ℚ := by
  -- Completeness would force the explicit rational Cauchy sequence to converge.
  intro hComplete
  letI : CompleteSpace ℚ := hComplete
  exact not_tendsto_sqrtTwoDecimalApprox
    (cauchySeq_tendsto_of_complete cauchySeq_sqrtTwoDecimalApprox)
