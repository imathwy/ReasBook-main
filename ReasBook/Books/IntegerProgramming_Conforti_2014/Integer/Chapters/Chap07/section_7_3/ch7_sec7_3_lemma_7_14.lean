import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7
import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9
import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma714

open SequenceIndependentLifting

/- Lemma 7.14 is the `source-facing` theorem asserting that the flow-cover lifting function with
the canonical excess `flow_cover_excess a b Finset.univ` is superadditive on `[0, b]`.
Exercise 7.16 reuses this exact statement as a `bridge/view` recall, so the owner declaration
lives here in Section 7.3 rather than downstream in the exercise file. -/
/-- Lemma 7.14. The flow-cover lifting function with excess
`flow_cover_excess a b Finset.univ` is superadditive on `[0, b]`. -/
theorem flow_cover_lifting_function_is_superadditive_on_Icc
    {t : ℕ} (b : ℝ) (a : Fin t → ℝ) :
    is_superadditive_on_Icc
      (flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) a) b := sorry

end Lemma714
