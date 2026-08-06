import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Construction_23_2_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_5_4

-- Semantic recall via `lean_leansearch` did not surface a more canonical imported owner for the
-- textbook slogan connecting the Thom isomorphism directly to characteristic classes. In the
-- local Chapter 23 API, the bridge is already split into the Thom-isomorphism theorem
-- `thom_isomorphism_theorem`, its source-facing map `thomIsomorphismMap`, and the
-- universal-bundle evaluation bijection
-- `characteristicClassEvalOnUniversalBundle_bijective`, whose source-facing Construction 23.2.4
-- corollary is `existsUnique_characteristicClass_of_universalClass` with pullback companion
-- `CharacteristicClass.pullbackValue_eq_map_of_evalOnUniversalBundle_eq`. This remark is
-- therefore best recorded as a labeled recall block.

/- Remark 23.5.6. The Thom isomorphism is the bridge from vector bundles to cohomological
characteristic classes: Theorem 23.5.4 supplies the Thom-isomorphism comparison for a bundle with
a Thom class, while Construction 23.2.4 packages cohomology classes on the classifying space as
uniquely determined characteristic classes with the expected pullback formula. -/
#check thomIsomorphismMap
#check thom_isomorphism_theorem
#check characteristicClassEvalOnUniversalBundle_bijective
#check existsUnique_characteristicClass_of_universalClass
#check CharacteristicClass.pullbackValue_eq_map_of_evalOnUniversalBundle_eq
