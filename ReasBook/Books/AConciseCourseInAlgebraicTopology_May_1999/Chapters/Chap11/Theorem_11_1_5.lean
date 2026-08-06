import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CollapseSubsetPair

open scoped Topology

universe u

noncomputable section

-- Semantic recall via `lean_leansearch`: no source-exact owner for the homotopy-excision quotient
-- map surfaced in the current environment. Local Chapter 6/9/11/13 precedent already fixes the
-- relevant owners: `IsCofibration`, `IsNEquivalence`, `SpacePair.Hom.IsNEquivalence`, and the
-- quotient model `collapseSubsetType`; the canonical quotient-pair owner is
-- `collapseSubsetPairMap`.

variable {X : Type u} [TopologicalSpace X]

/-- Theorem 11.1.5 (1): if the cofibration inclusion `A ↪ X` is an `((n : ℕ) - 1)`-equivalence
and both `A` and `X` satisfy the source-facing `(n - 2)`-connectedness hypotheses from the text
(namely `Nonempty` when `n = 1`, and otherwise `Nonempty` together with
`NConnectedSpace ((n : ℕ) - 2)`), then the quotient map of pairs `(X, A) ⟶ (X/A, *)` is a
`(2 * (n : ℕ) - 2)`-equivalence. -/
theorem quotientPairMap_isNEquivalence (A : Set X) (n : ℕ+)
    (hA_nonempty : A.Nonempty)
    (hA_connected : match (n : ℕ) with
      | 0 => True
      | 1 => True
      | m + 2 => NConnectedSpace m A)
    (hX_nonempty : Nonempty X)
    (hX_connected : match (n : ℕ) with
      | 0 => True
      | 1 => True
      | m + 2 => NConnectedSpace m X)
    (hi : IsCofibration (subsetInclusion A))
    (hEq : IsNEquivalence ((n : ℕ) - 1) (subsetInclusion A)) :
    SpacePair.Hom.IsNEquivalence (2 * (n : ℕ) - 2) (collapseSubsetPairMap A hA_nonempty) := sorry

/-- Theorem 11.1.5 (2): if the cofibration inclusion `A ↪ X` is an `((n : ℕ) - 1)`-equivalence
and `A`, `X` are each nonempty and `((n : ℕ) - 1)`-connected, then the quotient map of pairs
`(X, A) ⟶ (X/A, *)` is a `(2 * (n : ℕ) - 1)`-equivalence. -/
theorem quotientPairMap_isNEquivalence_of_nConnected (A : Set X) (n : ℕ+)
    (hA_nonempty : A.Nonempty)
    (hA_connected : NConnectedSpace ((n : ℕ) - 1) A)
    (hX_nonempty : Nonempty X)
    (hX_connected : NConnectedSpace ((n : ℕ) - 1) X)
    (hi : IsCofibration (subsetInclusion A))
    (hEq : IsNEquivalence ((n : ℕ) - 1) (subsetInclusion A)) :
    SpacePair.Hom.IsNEquivalence (2 * (n : ℕ) - 1) (collapseSubsetPairMap A hA_nonempty) := sorry
