import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

/- Exercise 13.2.5 splits naturally across the chapter's two convergence layers.
- `source-facing`: vague convergence is stated with `radonMeasureVaguelyConvergesTo`.
- `core/canonical`: weak convergence is stated as `Tendsto ... (𝓝 μ)` on `FiniteMeasure ℝ`.
- `bridge/view`: the weak statement uses the owner embedding
  `ProbabilityMeasure.toFiniteMeasure`, while the canonical Dirac owner theorem is
  `tendsto_diracProba_iff_tendsto`.
The only primitive data here is the Dirac sequence `n ↦ δₙ`, so no extra local wrapper API is
introduced. -/

/-- Exercise 13.2.5 (1): the Dirac masses `δ_n` on `ℝ` converge vaguely to the zero measure, in
the canonical sense of `radonMeasureVaguelyConvergesTo`. -/
-- Proof sketch: test against an arbitrary compactly supported continuous function `f`. Its support
-- is contained in some compact set, hence for all sufficiently large `n` one has `f n = 0`. Since
-- `∫ x, f x ∂Measure.dirac (n : ℝ) = f n`, the integrals are eventually zero and therefore tend to
-- the integral against the zero measure.
theorem dirac_nat_vaguely_converges_to_zero :
    radonMeasureVaguelyConvergesTo (fun n ↦ Measure.dirac (n : ℝ)) 0 := sorry

/-- Exercise 13.2.5 (2): the Dirac masses `δ_n` on `ℝ`, viewed in the owner space
`FiniteMeasure ℝ`, do not converge weakly in its canonical weak topology. -/
-- Proof sketch: any weak limit in `FiniteMeasure ℝ` would, by the owner theorem
-- `ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds`, lift to a weak limit of the
-- probability measures `δ_n`. The canonical Dirac owner theorem
-- `tendsto_diracProba_iff_tendsto` would then force `n ↦ (n : ℝ)` to converge in `ℝ`, which is
-- impossible along `atTop`. Hence no finite weak limit exists.
theorem dirac_nat_not_weakly_convergent :
    ¬ ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun n ↦ (diracProba (n : ℝ)).toFiniteMeasure) atTop (𝓝 μ) := sorry
