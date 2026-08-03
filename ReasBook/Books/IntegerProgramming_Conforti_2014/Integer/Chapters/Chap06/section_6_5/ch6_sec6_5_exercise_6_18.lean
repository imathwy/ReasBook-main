import Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_example_6_23
import Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27

-- Declarations for this item will be appended below by the statement pipeline.

section Exercise618

/-- Under the hypotheses of Exercise 6.18, the function `π₂` from Example 6.23 is an extreme
valid function for the one-dimensional pure integer infinite relaxation. -/
instance exercise_6_18_pi2_extreme
    {t f : ℝ} [ht : Fact (0 < t)] [hft : Fact (1 / 2 + t ≤ f)] [hf : Fact (f < 1)] :
    pure_integer_extreme_valid_function_on_R f
      (example_6_23_pi2 t f) := by
  sorry

/-- Exercise 6.18. Assume `t > 0` and `1 / 2 + t ≤ f < 1`. Show that the function `π₂` in
Example 6.23 is extreme. -/
theorem exercise_6_18_pi2_is_extreme
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    pure_integer_extreme_valid_function_on_R f
      (example_6_23_pi2 t f) := by
  letI : Fact (0 < t) := ⟨ht⟩
  letI : Fact (1 / 2 + t ≤ f) := ⟨hft⟩
  letI : Fact (f < 1) := ⟨hf⟩
  infer_instance

end Exercise618
