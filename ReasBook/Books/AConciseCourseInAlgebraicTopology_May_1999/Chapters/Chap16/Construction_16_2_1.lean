import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.GammaRealization

open CategoryTheory

-- Semantic recall via `lean_leansearch`: `TopCat.toSSet` and `SSet.toTop` in
-- `Mathlib.AlgebraicTopology.SingularSet` are the canonical owners for the total singular complex
-- and its geometric realization in the current Lean environment.

variable (X : TopCat)

noncomputable section

/- Construction 16.2.1. By Definition 16.1.3, the total singular complex of `X` is formalized by
`TopCat.toSSet.obj X`, whose `n`-simplices are the singular simplices `Δ^n → X`; by Definition
16.1.2, its face and degeneracy maps come from the standard simplex face and degeneracy maps.
Its geometric realization `Γ X` is therefore canonically formalized by `gammaRealization X =
SSet.toTop.obj (TopCat.toSSet.obj X)`, and the induced maps are `gammaRealizationMap f =
SSet.toTop.map (TopCat.toSSet.map f)`. This is the realization built from the disjoint union of
the products `S_n X × Δ^n` modulo the face and degeneracy identifications. -/
#check (TopCat.toSSet.obj X : SSet)
#check (gammaRealization X : TopCat)
#check @gammaRealizationMap

end
