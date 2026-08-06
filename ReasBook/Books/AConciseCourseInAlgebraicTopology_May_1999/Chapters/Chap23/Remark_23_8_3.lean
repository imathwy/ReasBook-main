import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_8_2

-- Semantic recall: Chapter 23 already exposes vector-bundle classification as the three canonical
-- special-case bijections `realPlaneBundleClassifyingMap_bijective`,
-- `orientedRealPlaneBundleClassifyingMap_bijective`, and
-- `complexPlaneBundleClassifyingMap_bijective`. The general principal-bundle owner explaining why
-- these are special cases is `universalPrincipalBundle_classifying_bijective`.

/-
Remark 23.8.3. Classifying vector bundles is a special case of
`universalPrincipalBundle_classifying_bijective`. In the current chapter API, that specialization
is already recorded by the vector-bundle classification bijections
`realPlaneBundleClassifyingMap_bijective`,
`orientedRealPlaneBundleClassifyingMap_bijective`, and
`complexPlaneBundleClassifyingMap_bijective` for real, oriented real, and complex `n`-plane
bundles respectively.
-/
recall realPlaneBundleClassifyingMap_bijective
recall orientedRealPlaneBundleClassifyingMap_bijective
recall complexPlaneBundleClassifyingMap_bijective
recall universalPrincipalBundle_classifying_bijective
