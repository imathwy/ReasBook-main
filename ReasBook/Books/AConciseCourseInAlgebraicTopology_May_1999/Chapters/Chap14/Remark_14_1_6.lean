import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_5

/-
Remark 14.1.6. Construction 14.1.5 records the source-side setup used in this chapter through the
adjoin-basepoint operation `X ↦ adjoinBasepoint X` from unbased spaces to based spaces, modeled in
this project as `Under (⊤_ TopCat)`.

(1) An unreduced cone construction on unbased spaces should therefore be compared against the
reduced cone construction obtained after adjoining a disjoint basepoint.

(2) Likewise, an unreduced cofiber construction on maps of unbased spaces should be compared
against the corresponding reduced cofiber construction after adjoining a disjoint basepoint.

Until the chapter fixes concrete unreduced cone and cofiber functors, this remark is kept as a
recall block rather than as a wrapper alias for arbitrary natural-isomorphism data.
-/
#check adjoinBasepoint
