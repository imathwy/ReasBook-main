import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_73 (from Items/Chap01) -/
/-- Definition 1.73: For a measure space `(Ω, 𝓐, μ)` and a measurable set `Ω'`, the restriction of
`μ` to `Ω'` is the canonical mathlib measure `μ.restrict Ω'`; this is Lean's realization of the
textbook restriction measure on the trace `σ`-algebra `𝓐|_{Ω'}`. -/
recall MeasureTheory.Measure.restrict

/-- If `A` is contained in the restricting set `Ω'`, then the restricted measure agrees with the
original measure on `A`, matching the textbook formula `μ|_{Ω'}(A) = μ(A)`. -/
recall MeasureTheory.Measure.restrict_eq_self
