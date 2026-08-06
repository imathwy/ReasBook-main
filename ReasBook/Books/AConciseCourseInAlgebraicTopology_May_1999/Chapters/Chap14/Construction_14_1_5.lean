import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

-- No canonical unbased-homology owner for adjoining a disjoint basepoint is currently available
-- in the project or imported mathlib surface. This file therefore keeps the source-facing owner
-- directly as the reduced homology of `X₊`.

/-- Construction 14.1.5. For an unbased space `X`, adjoining a disjoint basepoint defines the
associated homology object `E_q(X)` as the reduced homology `Ẽ_q(X₊)`, formalized here as
`reducedHomology E q X₊`. -/
noncomputable abbrev homology
    (E : ℤ → (X : TopCat) → Set X → Type v)
    (q : ℤ) (X : TopCat) : Type v :=
  reducedHomology E q X₊

/-- Unfolding `homology` identifies the unbased homology object `E_q(X)` with the reduced
homology of the based space obtained by adjoining a disjoint basepoint to `X`. -/
@[simp] theorem homology_def
    (E : ℤ → (X : TopCat) → Set X → Type v)
    (q : ℤ) (X : TopCat) :
    homology E q X = reducedHomology E q X₊ := rfl
