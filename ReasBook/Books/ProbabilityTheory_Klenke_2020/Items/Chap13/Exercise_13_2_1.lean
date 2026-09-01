import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 13.2.1: the textbook metric `d_P` on `𝓜_1(E)` is the canonical distance on
`MeasureTheory.LevyProkhorov (ProbabilityMeasure E)`, and mathlib identifies it with the
auxiliary quantity `levyProkhorovDist` on the underlying probability measures. Together with the
next recall, this yields `d_P(μ, ν) = d_P'(μ, ν) = d_P'(ν, μ)` for all `μ, ν ∈ 𝓜_1(E)`. -/
recall MeasureTheory.LevyProkhorov.dist_probabilityMeasure_def

/- Symmetry of the auxiliary quantity `d_P'` is the canonical theorem
`MeasureTheory.levyProkhorovDist_comm`, specialized to probability measures. -/
recall MeasureTheory.levyProkhorovDist_comm
