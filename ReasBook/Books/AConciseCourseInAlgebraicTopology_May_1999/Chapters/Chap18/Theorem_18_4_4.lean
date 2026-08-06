import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped TopCat

-- No project-local or mathlib owner currently packages this Borsuk-Ulam statement for the chosen
-- sphere model, so the main entry stays source-facing over `𝕊 n`, with an unbundled `Continuous`
-- companion for downstream use.

/-- Theorem 18.4.4. Borsuk-Ulam theorem: every continuous map `S^n → ℝ^n` identifies some
antipodal pair. -/
theorem exists_image_eq_image_neg_of_continuousMap_sphere (n : ℕ)
    (f : C(𝕊 n, EuclideanSpace ℝ (Fin n))) :
    ∃ x : 𝕊 n, f x = f (-x) := sorry

/-- Theorem 18.4.4, unbundled form: every continuous map `S^n → ℝ^n` identifies some antipodal
pair. -/
theorem exists_image_eq_image_neg_of_continuous {n : ℕ}
    {f : 𝕊 n → EuclideanSpace ℝ (Fin n)} (hf : Continuous f) :
    ∃ x : 𝕊 n, f x = f (-x) := by
  simpa using exists_image_eq_image_neg_of_continuousMap_sphere n ⟨f, hf⟩
