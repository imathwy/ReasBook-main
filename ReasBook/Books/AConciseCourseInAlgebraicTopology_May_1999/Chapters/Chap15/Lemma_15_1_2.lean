import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Definition_15_1_1

open scoped TopCat Topology Topology.Homotopy

universe u

local notation "BasedSpace" => CategoryTheory.Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch` surfaced only generic additive-hom infrastructure, so
-- this item uses the Chapter 15 canonical owner already introduced in `Definition_15_1_1`.

section

/- Lemma 15.1.2: for every positive degree `n ≥ 1`, the Hurewicz map `h` is a homomorphism.
In the Chapter 15 API, this is the canonical additive-homomorphism surface
`hurewiczHomomorphism`. -/
recall hurewiczHomomorphism
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (n : ℕ) (X : BasedSpace) [Nonempty (Fin n)]
    [HasHurewiczComparison n X] (i_n : SphereHomologyGenerator H n) :
    Additive (π_ n X.right (underTopBasepoint X)) →+ basedReducedHomology H (n : ℤ) X

end
