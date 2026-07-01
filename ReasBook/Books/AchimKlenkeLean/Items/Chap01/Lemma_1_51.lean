import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Lemma 1.51: An outer measure `μ*` is `σ`-additive on its Carathéodory-measurable sets; that
is, if `A : ℕ → Set Ω` is pairwise disjoint and each `A n` is measurable in
`MeasureTheory.OuterMeasure.caratheodory μ*`, then `μ* (⋃ n, A n) = ∑' n, μ* (A n)`. -/
recall MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory
