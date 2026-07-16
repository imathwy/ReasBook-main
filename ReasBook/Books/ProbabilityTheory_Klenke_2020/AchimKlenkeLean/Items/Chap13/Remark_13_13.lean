import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

universe u

variable {E : Type u}

-- Proof sketch: weak convergence is the canonical convergence `Tendsto` on `FiniteMeasure E`.
-- Uniqueness is therefore just the ambient Hausdorff uniqueness of limits in the weak topology on
-- `FiniteMeasure E`.
/-- Remark 13.13 (1): weak convergence of finite measures determines the finite limit measure
uniquely. In particular, the textbook metric Borel statement is an immediate special case. -/
theorem weak_limit_unique [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [T2Space (FiniteMeasure E)]
    {μ ν : FiniteMeasure E} {μs : ℕ → FiniteMeasure E}
    (hμ : Tendsto μs atTop (nhds μ)) (hν : Tendsto μs atTop (nhds ν)) :
    μ = ν :=
  tendsto_nhds_unique hμ hν

-- Proof sketch: use the source-facing owner predicate `radonMeasureVaguelyConvergesTo`. If the
-- same sequence converges vaguely to both `μ` and `ν`, then the compactly supported continuous
-- test integrals agree for both candidates, and Theorem 13.11 (2) separates Radon measures on a
-- locally compact metric space.
/-- Remark 13.13 (2): on a locally compact metric space, a sequence of Radon measures has at most
one vague limit, in the sense that convergence of all compactly supported continuous test
integrals determines the Radon limit measure uniquely. -/
theorem vague_limit_unique_of_locallyCompact [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] {μ ν : Measure E} {μs : ℕ → Measure E}
    (hμ : radonMeasureVaguelyConvergesTo μs μ)
    (hν : radonMeasureVaguelyConvergesTo μs ν) :
    μ = ν := sorry
