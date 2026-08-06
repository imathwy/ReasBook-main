import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v

-- The source defines reduced homology of a based space as the corresponding relative homology
-- group with respect to the singleton containing the chosen basepoint.

/-- Definition 14.1.2. For a based space `X`, modeled as an object of `BasedSpace`, the
reduced homology `Ẽ_q(X)` is the relative homology of `X.right` with respect to the singleton
containing its chosen basepoint. -/
noncomputable def reducedHomology
    (E : ℤ → (X : TopCat) → Set X → Type v)
    (q : ℤ) (X : BasedSpace) : Type v :=
  E q X.right ({underTopBasepoint X} : Set X.right)

/-- Unfolding `reducedHomology` identifies it with the ambient relative homology theory evaluated
on the singleton basepoint subset. -/
@[simp] theorem reducedHomology_def
    (E : ℤ → (X : TopCat) → Set X → Type v)
    (q : ℤ) (X : BasedSpace) :
    reducedHomology E q X =
      E q X.right ({underTopBasepoint X} : Set X.right) := rfl
