import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Theorem_16_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Theorem_16_2_4

-- Semantic recall via `lean_leansearch`: `SSet.toTop` and `TopCat.toSSet` are the canonical
-- owners for the functorial CW approximation `Γ X`, while
-- `gammaRealizationCellularChainComplexIsoSingular` and
-- `singularRealizationEvaluation_isWeakEquivalence` already encode that its cellular chains model
-- the singular chains of `X` and that the canonical map `Γ X ⟶ X` is a weak equivalence.

variable (X : TopCat)

/- Remark 16.2.5. The preceding results are already formalized in the current chapter as the
functorial CW approximation `gammaRealization X = Γ X`, together with the statements that `Γ X`
admits a CW-complex structure whose cellular chains recover the singular chains of `X` and that
the canonical map `Γ X ⟶ X` is a weak equivalence. This remark is therefore recorded as a labeled
reuse of those existing Chapter 16 owners. -/
#check (gammaRealization X : TopCat)

#check gammaRealization_existsCWComplexWithNondegenerateCells
#check gammaRealizationCellularChainComplexIsoSingular
#check singularRealizationEvaluation_isWeakEquivalence
