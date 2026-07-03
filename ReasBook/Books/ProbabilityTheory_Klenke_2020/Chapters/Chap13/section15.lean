

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_15 (from Items/Chap13) -/
open Filter MeasureTheory
open scoped CompactlySupported Topology

universe u

noncomputable section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [LocallyCompactSpace E] [PolishSpace E]

-- Proof sketch: approximate the constant function `1` from below by an increasing sequence in
-- `C_c(E, ℝ)` with values in `[0,1]`, pass to the limit along the vague convergence hypothesis,
-- and compare the resulting suprema with the total masses.
/-- Lemma 13.15: if Radon measures on a locally compact Polish space converge vaguely,
then their total masses are lower semicontinuous. -/
theorem measure_univ_le_liminf_of_vaguely_converges
    {μ : Measure E} {μs : ℕ → Measure E}
    (h : radonMeasureVaguelyConvergesTo μs μ) :
    μ Set.univ ≤ liminf (fun n ↦ μs n Set.univ) atTop := sorry

end
