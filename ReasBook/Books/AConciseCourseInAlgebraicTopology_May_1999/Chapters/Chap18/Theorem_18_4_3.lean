import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped TopCat

-- Semantic recall via `lean_leansearch` only surfaced the generic owner `TopCat.sphere`; the
-- local project sphere owner `𝕊 n` fixes the textbook notation, while `Function.Odd` is the
-- canonical oddness predicate for maps commuting with the antipodal involution.

/-- Theorem 18.4.3. If `m > n`, then there is no antipodal map `S^m → S^n`;
in particular this covers the source case `m > n ≥ 1`. -/
theorem not_exists_antipodalSphereMap {m n : ℕ} (hmn : n < m) :
    ¬ ∃ f : C(𝕊 m, 𝕊 n), Function.Odd f := sorry
