import FirstOrderMethodsOptimization_Beck_2017.Chap10.Corollary_10_52_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Corollary 10.52 is a `bridge/view` specialization of the ambient-space Chapter 10 smoothability
owner. The reusable canonical theorem is
`convex_lipschitz_is_one_lipschitz_sq_div_two_smoothable_nonneg`; this file keeps the source-facing
real-line statement as a thin specialization. -/

section

/-- Corollary 10.52: if `h : ℝ → ℝ` is convex and globally `ℓ_h`-Lipschitz, then `h` is
nonnegatively `(1, ℓ_h^2 / 2)`-smoothable. The nonnegative owner matches the textbook parameter
`ℓ_h^2 / 2`, which need not be strictly positive. -/
theorem real_convex_lipschitz_is_one_lipschitz_sq_div_two_smoothable_nonneg
    (h : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ h) (ℓh : NNReal) (hlip : LipschitzWith ℓh h) :
    is_smoothable_nonneg h 1 (ℓh ^ (2 : ℕ) / 2) := by
  simpa using
    convex_lipschitz_is_one_lipschitz_sq_div_two_smoothable_nonneg h hconv ℓh hlip

end
