import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced unrelated abstract quotient and cohomology
-- APIs. Local Chapter 14/18 precedent already fixes the canonical collapse quotient
-- `collapseSubsetBasedPairMap` and the cohomology-theory owner `PairCohomologyTheory`, so this
-- item is stated directly on the contravariant map induced by the quotient pair map.

/-- Theorem 19.1.3: if `i : A ↪ X` is a cofibration and `A` is nonempty so that the collapse
quotient carries the collapsed basepoint, then the quotient map of pairs
`(X, A) ⟶ (X/A, *)` induces an isomorphism
`Ẽ^q(X/A) ⟶ E^q(X, A)` in every degree `q`. -/
instance cofibrationQuotientCohomologyMap_isIso
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} {A : Set X} (hA : A.Nonempty)
    (hi : IsCofibration (subsetInclusion A)) :
    IsIso ((H q).map (collapseSubsetBasedPairMap X A hA).op) := sorry
