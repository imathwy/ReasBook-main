import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TopCat

-- Semantic recall: `Function.Odd` is the canonical odd-map predicate for the antipodal symmetry
-- on the established sphere owner `𝕊 n`.

/-- Corollary 18.4.5. A continuous odd map `S^m → S^n` can exist only when `m ≤ n`. -/
theorem sourceDim_le_targetDim_of_exists_antipodalSphereMap {m n : ℕ}
    (h_exists : ∃ f : C(𝕊 m, 𝕊 n), Function.Odd f) :
    m ≤ n := by
  by_contra hmn
  exact not_exists_antipodalSphereMap (Nat.lt_of_not_ge hmn) h_exists

/-- A specific continuous odd map `S^m → S^n` forces `m ≤ n`. -/
theorem sourceDim_le_targetDim_of_antipodalSphereMap {m n : ℕ}
    (f : C(𝕊 m, 𝕊 n)) (hf : Function.Odd f) :
    m ≤ n :=
  sourceDim_le_targetDim_of_exists_antipodalSphereMap ⟨f, hf⟩
