

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_13_23 (from Items/Chap13) -/
open Filter MeasureTheory MeasureTheory.FiniteMeasure
open scoped Topology

noncomputable section

private theorem isSubProbabilityMeasure_of_mass_le_one (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) : IsSubProbabilityMeasure (μ : Measure ℝ) := by
  refine ⟨?_⟩
  have hmass : (μ.mass : ENNReal) ≤ 1 := by
    exact_mod_cast hμ
  simpa [FiniteMeasure.ennreal_mass] using hmass

private theorem isDefectiveDistributionFunction_measureDistributionFunction_of_mass_le_one
    (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    IsDefectiveDistributionFunction (measureDistributionFunction μ) :=
  isDefectiveDistributionFunction_measureDistributionFunction μ
    (isSubProbabilityMeasure_of_mass_le_one μ hμ)

-- Proof sketch: specialize the Portmanteau characterization of weak convergence to the rays
-- `(-∞, x]`, whose boundaries are the singletons `{x}`. This identifies weak convergence of
-- sub-probability finite measures with weak convergence of their associated defective
-- distribution functions in the sense of Definition 13.21; the companion theorem
-- `measureDistributionFunction_weakly_converges_to_iff` unfolds that owner predicate into mass
-- convergence plus pointwise convergence at the continuity points of the limit distribution
-- function.
/-- Theorem 13.23: for sub-probability finite measures on `ℝ`, weak convergence is equivalent to
weak convergence of the corresponding defective distribution functions. The companion theorem
`measureDistributionFunction_weakly_converges_to_iff` unfolds this into convergence of the total
masses and pointwise convergence at every continuity point of the limiting distribution
function. -/
theorem tendsto_iff_measureDistributionFunction_tendsto
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1) :
    Tendsto μs atTop (𝓝 μ) ↔
      distribution_function_weakly_converges_to
        (fun n ↦ measureDistributionFunction (μs n))
        (measureDistributionFunction μ) := sorry

-- Proof sketch: for the associated defective distribution functions, Definition 13.21 records
-- continuity-point convergence together with the endpoint limsup inequality; the endpoint values
-- are exactly the total masses by `sSup_range_eq_measure_univ_toReal`, and the auxiliary theorem
-- `tendsto_distribution_function_at_top_value_of_weak_convergence` upgrades the limsup condition
-- to actual convergence of the endpoint values, hence of the masses.
/-- For sub-probability finite measures on `ℝ`, weak convergence of the associated defective
distribution functions is exactly convergence of the total masses together with pointwise
convergence at every continuity point of the limiting distribution function. -/
theorem measureDistributionFunction_weakly_converges_to_iff
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1) :
    distribution_function_weakly_converges_to
      (fun n ↦ measureDistributionFunction (μs n))
      (measureDistributionFunction μ) ↔
      Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) ∧
        ∀ ⦃x : ℝ⦄, ContinuousAt (measureDistributionFunction μ) x →
          Tendsto (fun n ↦ measureDistributionFunction (μs n) x) atTop
            (𝓝 (measureDistributionFunction μ x)) := sorry
