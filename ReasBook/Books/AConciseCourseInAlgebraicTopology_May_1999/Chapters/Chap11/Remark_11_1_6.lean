import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Theorem_11_1_5

open scoped Topology

universe u

noncomputable section

-- Semantic recall via `lean_leansearch`: no tighter mathlib owner for this interpretive
-- homotopy-excision consequence surfaced in the current environment. Chapter 11 already packages
-- the quotient-pair excision theorem in `quotientPairMap_isNEquivalence` and
-- `quotientPairMap_isNEquivalence_of_nConnected`, while
-- `SpacePair.Hom.IsNEquivalence.relativeBijective` is the canonical extraction API for the
-- induced relative-homotopy bijections below the equivalence range.

variable {X : Type u} [TopologicalSpace X]

/-- Remark 11.1.6. Under the hypotheses of Theorem 11.1.5 (1), the quotient map of pairs
`(X, A) ⟶ (X / A, *)` induces bijections on relative homotopy groups in every positive degree
strictly below `2 * (n : ℕ) - 2`. -/
theorem quotientPairMap_relativeHomotopyGroup_bijective
    (A : Set X) (n : ℕ+)
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
    (hEq : IsNEquivalence ((n : ℕ) - 1) (subsetInclusion A))
    (c : A) {q : ℕ+} (hq : (q : ℕ) < 2 * (n : ℕ) - 2) :
    Function.Bijective ((collapseSubsetPairMap A hA_nonempty).relativeHomotopyGroupMap q c) := by
  let hExcision :=
    quotientPairMap_isNEquivalence A n hA_nonempty hA_connected hX_nonempty hX_connected hi hEq
  exact hExcision.relativeBijective c hq

/-- Remark 11.1.6. Under the stronger `((n : ℕ) - 1)`-connectedness hypotheses of
Theorem 11.1.5 (2), the quotient map of pairs `(X, A) ⟶ (X / A, *)` induces bijections on
relative homotopy groups in every positive degree strictly below `2 * (n : ℕ) - 1`. -/
theorem quotientPairMap_relativeHomotopyGroup_bijective_of_nConnected
    (A : Set X) (n : ℕ+)
    (hA_nonempty : A.Nonempty)
    (hA_connected : NConnectedSpace ((n : ℕ) - 1) A)
    (hX_nonempty : Nonempty X)
    (hX_connected : NConnectedSpace ((n : ℕ) - 1) X)
    (hi : IsCofibration (subsetInclusion A))
    (hEq : IsNEquivalence ((n : ℕ) - 1) (subsetInclusion A))
    (c : A) {q : ℕ+} (hq : (q : ℕ) < 2 * (n : ℕ) - 1) :
    Function.Bijective ((collapseSubsetPairMap A hA_nonempty).relativeHomotopyGroupMap q c) := by
  let hExcision :=
    quotientPairMap_isNEquivalence_of_nConnected A n hA_nonempty hA_connected hX_nonempty
      hX_connected hi hEq
  exact hExcision.relativeBijective c hq
