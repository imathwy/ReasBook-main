import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2

open scoped ComplexKTheory HomotopyClasses

-- Chapter 24 exposes the compact-space owner `complexKTheory X`, and Chapter 8 exposes the
-- pointed domain and codomain surfaces `adjoinBasepoint (TopCat.of X)` and
-- `basedHomotopyClasses`. What the current repository still does not expose is a concrete public
-- based-space owner for `BU × ℤ`, together with the specialized comparison
-- `K(X) ≃ Ho*[(TopCat.of X)₊, BU × ℤ]` for compact `X`.

/- Corollary 24.1.6. If `X` is compact, then complex `K`-theory is represented by pointed
homotopy classes from the adjoined based space `(TopCat.of X)₊` into `BU × ℤ`:
`K(X) ≃ Ho*[(TopCat.of X)₊, BU × ℤ]`.

The current repository has the source-side owners `complexKTheory`, `TopCat.of`,
`adjoinBasepoint`, and `basedHomotopyClasses`, but it does not yet provide a concrete public
based-space owner for `BU × ℤ` or a specialized representability theorem identifying these
surfaces. This corollary is therefore kept as a labeled recall block rather than as a wrapper over
arbitrary chosen representability data. -/
#check complexKTheory
#check TopCat.of
#check adjoinBasepoint
#check basedHomotopyClasses
#check CompactSpace
