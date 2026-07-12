import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Text 1.0.50 (1): the real line with its usual metric topology is Hausdorff. -/
theorem real_t2Space : T2Space ℝ := inferInstance

/-- Text 1.0.50 (2): the real line with its usual topology is not compact. -/
theorem real_not_compact : ¬ CompactSpace ℝ := by
  simpa [not_compactSpace_iff] using (inferInstance : NoncompactSpace ℝ)
