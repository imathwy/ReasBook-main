import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped CompactlySupported Topology

noncomputable section

/-- The `n`-th truncated Lebesgue measure on `ℝ`, obtained by restricting `volume` to `[-n, n]`. -/
def truncatedLebesgueMeasure (n : ℕ) : Measure ℝ :=
  volume.restrict (Set.Icc (-(n : ℝ)) n)

private theorem isFiniteMeasure_truncatedLebesgueMeasure (n : ℕ) :
    IsFiniteMeasure (truncatedLebesgueMeasure n) := by
  simpa [truncatedLebesgueMeasure] using
    (show IsFiniteMeasure (volume.restrict (Set.Icc (-(n : ℝ)) n)) from inferInstance)

/-- The weak-topology owner view of `truncatedLebesgueMeasure`. -/
def truncatedLebesgueFiniteMeasure (n : ℕ) : FiniteMeasure ℝ :=
  ⟨truncatedLebesgueMeasure n, isFiniteMeasure_truncatedLebesgueMeasure n⟩

-- Proof sketch: if `f` is compactly supported, then its support is contained in some compact
-- interval `[-R, R]`. For all sufficiently large `n`, the restriction of Lebesgue measure to
-- `[-n, n]` agrees with Lebesgue measure on the support of `f`, so the test-function integrals are
-- eventually constant and equal to the integral against `volume`.
/-- Exercise 13.2.4 (1): the restrictions of Lebesgue measure to the symmetric intervals `[-n, n]`
converge vaguely to Lebesgue measure on `ℝ`. -/
theorem truncatedLebesgueMeasures_vaguely_converge :
    radonMeasureVaguelyConvergesTo truncatedLebesgueMeasure volume := sorry

-- Proof sketch: weak convergence of finite measures would force convergence of the integrals of the
-- bounded continuous test function `1`, hence convergence of the total masses. But
-- the finite measure `truncatedLebesgueFiniteMeasure n` has mass `2n`,
-- so the masses diverge and no weak limit in `FiniteMeasure ℝ` can exist.
/-- Exercise 13.2.4 (2): the finite measures obtained by restricting Lebesgue measure to `[-n, n]`
do not converge weakly in the finite-measure topology. -/
theorem truncatedLebesgueMeasures_not_weakly_convergent :
    ¬ ∃ μ : FiniteMeasure ℝ,
      Tendsto truncatedLebesgueFiniteMeasure atTop (𝓝 μ) := sorry
