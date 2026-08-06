import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Theorem_16_2_3

-- Semantic recall via `lean_leansearch`: `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq`
-- is the canonical alternating-face-map description of the singular differential, while the
-- source-facing comparison owner `IsGammaRealizationCellularChainComparison` and its
-- chapter-local `IsGammaRealizationCellularChainComparison.cellGroupIso`,
-- `IsGammaRealizationCellularChainComparison.singularChainDegreeIso`, and
-- `IsGammaRealizationCellularChainComparison.singularChainIso` unpack the specific comparison data
-- carried by `hcomparison`.

/- Proof step 16.3.4. For a chosen CW structure on `Γ X` whose `n`-cells are indexed by the
nondegenerate singular `n`-simplices of `X`, the comparison data in
`IsGammaRealizationCellularChainComparison X hΓ hcell cellularChains` is the chapter-local API
that transports the cellular differential on `Γ X` to the singular differential on `X`. By
Construction 16.1.6, that singular differential is the alternating sum of the face operators,
formalized by `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq`. -/
#check IsGammaRealizationCellularChainComparison
#check IsGammaRealizationCellularChainComparison.cellGroupIso
#check IsGammaRealizationCellularChainComparison.singularChainDegreeIso
#check IsGammaRealizationCellularChainComparison.singularChainIso
#check AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
