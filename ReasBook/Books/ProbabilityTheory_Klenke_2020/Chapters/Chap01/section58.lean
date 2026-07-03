import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_58 (from Items/Chap01) -/
open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal Topology

noncomputable section

/-- The primitive `x ↦ ∫_0^x f(t) dt` attached to a real-valued density `f`. -/
def continuousDensityPrimitive (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t in 0..x, f t ∂volume

-- Proof sketch: if `a ≤ b`, rewrite the difference of the two primitives as the interval
-- integral of `f` over `a..b` by the fundamental theorem of calculus, then use the pointwise
-- nonnegativity of `f` to conclude the difference is nonnegative.
theorem continuousDensityPrimitive_monotone (f : ℝ → ℝ) (hf : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    Monotone (continuousDensityPrimitive f) := sorry

/- Example 1.58 (1): Item (i). The Stieltjes measure of the identity distribution function is the
Lebesgue measure on `ℝ`. -/
recall Real.volume_eq_stieltjes_id

-- Proof sketch: compare the two measures on half-open intervals `(a, b]`; the Stieltjes interval
-- formula gives `F b - F a`, and the fundamental theorem of calculus rewrites this as the
-- interval integral of `f`, which is exactly the `withDensity` interval formula from
-- Example 1.30(ix).
/-- Example 1.58 (2): Item (ii). The Lebesgue--Stieltjes measure of the canonical Stieltjes
function built from the primitive `x ↦ ∫ t in 0..x, f t ∂volume` of a continuous nonnegative
density `f` is the measure with density `f` with respect to Lebesgue measure. -/
theorem continuousDensityPrimitive_stieltjesMeasure_eq_withDensity (f : ℝ → ℝ)
    (hf : Continuous f) (hf_nonneg : ∀ x, 0 ≤ f x) :
    ((continuousDensityPrimitive_monotone f hf hf_nonneg).stieltjesFunction).measure =
      volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := sorry

/-- The atomic step function `x ↦ ∑ n αₙ 1_[xₙ,∞)(x)` attached to a summable family of
nonnegative weights. -/
def atomicDistributionStepFunction (x : ℕ → ℝ) (α : ℕ → NNReal) : ℝ → ℝ :=
  fun t ↦ ∑' n, (α n : ℝ) * Set.indicator (Set.Ici (x n)) (fun _ ↦ (1 : ℝ)) t

-- Proof sketch: each summand `t ↦ α n * 1_[x n, ∞)(t)` is monotone because `α n ≥ 0`, and the
-- summability hypothesis allows passage from the termwise monotonicity to monotonicity of the
-- infinite series.
theorem atomicDistributionStepFunction_monotone (x : ℕ → ℝ) (α : ℕ → NNReal)
    (hα : Summable α) :
    Monotone (atomicDistributionStepFunction x α) := sorry

-- Proof sketch: evaluate the weighted Dirac sum and the Stieltjes measure on half-open intervals
-- `(a, b]`; both sides compute the total weight of the atoms in `(a, b]`, and uniqueness of the
-- Stieltjes measure then gives equality.
/-- Example 1.58 (3): Item (iii). The atomic step function
`x ↦ ∑' n, α n * 1_[x n,∞)(x)` is the distribution function of the weighted atomic measure
`∑' n, α n δ_(x n)`. -/
theorem atomicDistributionStepFunction_stieltjesMeasure_eq_sum_dirac
    (x : ℕ → ℝ) (α : ℕ → NNReal)
    (hα : Summable α) :
    ((atomicDistributionStepFunction_monotone x α hα).stieltjesFunction).measure =
      Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n)) := sorry

-- Proof sketch: compute the total mass on `univ` by summing the Dirac masses and use the
-- summability of the nonnegative coefficients to show that this total mass is finite.
instance (x : ℕ → ℝ) (α : ℕ → NNReal) (hα : Summable α) :
    IsFiniteMeasure (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) := by
  sorry

-- Proof sketch: for the forward implication, construct the counting distribution function from the
-- locally finite sequence and verify that its Stieltjes measure is the given counting measure; for
-- the reverse implication, use the finiteness of the Stieltjes mass of bounded intervals to rule
-- out cluster points.
/-- Example 1.58 (4): Item (iv). The counting measure `∑' n, δ_(x n)` is a Lebesgue--Stieltjes
measure exactly when the sequence `(x n)` has no limit point, under the standing σ-finiteness
assumption on the counting measure. -/
theorem countingDiracSum_isLebesgueStieltjes_iff_noLimitPoint (x : ℕ → ℝ)
    (hσ : SigmaFinite (Measure.sum fun n ↦ Measure.dirac (x n))) :
    (∃ F : StieltjesFunction ℝ, F.measure = Measure.sum (fun n ↦ Measure.dirac (x n))) ↔
      ∀ y : ℝ, ¬ MapClusterPt y atTop x := sorry

-- Proof sketch: derive the total mass from `StieltjesFunction.measure_univ`; the hypothesis says
-- that the difference between the right and left tails tends to `1`, so the total mass of `F` is
-- `1`, which is exactly the probability-measure condition.
/-- Example 1.58 (5): Item (v). If `F x - F (-x)` tends to `1` as `x → ∞`, then the associated
Lebesgue--Stieltjes measure is a probability measure. -/
private theorem tendsto_zero_and_one_of_tendsto_sub_comp_neg (F : StieltjesFunction ℝ)
    (h : Tendsto (fun x ↦ F x - F (-x)) atTop (𝓝 1)) :
    Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1) := sorry

theorem stieltjesMeasure_isProbability_of_tendsto_sub_comp_neg (F : StieltjesFunction ℝ)
    (h : Tendsto (fun x ↦ F x - F (-x)) atTop (𝓝 1)) :
    IsProbabilityMeasure F.measure := by
  rcases tendsto_zero_and_one_of_tendsto_sub_comp_neg F h with ⟨h0, h1⟩
  exact F.isProbabilityMeasure h0 h1

end
