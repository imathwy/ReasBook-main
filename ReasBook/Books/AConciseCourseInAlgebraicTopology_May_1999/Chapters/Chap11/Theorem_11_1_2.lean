import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_3_2

universe u

-- Semantic recall via `lean_leansearch`: no closer mathlib owner for this excision statement
-- surfaced in the environment. Local Chapter 10/11 precedent already fixes the source-faithful
-- owners: `Triad.IsExcisive` for excisive triads, `NConnectedPair` for pair connectedness, and
-- the Chapter 11 triad pair/inclusion owner from `Definition_11_3_2` for the map
-- `(A, C) ⟶ (X, B)`.

variable {X : Type u} [TopologicalSpace X]

/-- Theorem 11.1.2: homotopy excision. For an excisive triad `(X; A, B)`, if the pairs
`(A, C)` and `(B, C)` with `C = A ∩ B` are `((m : ℕ) - 1)`- and `((n : ℕ) - 1)`-connected, then
the inclusion `(A, C) ⟶ (X, B)` is a `((m : ℕ) + (n : ℕ) - 2)`-equivalence. -/
theorem homotopyExcision (T : Triad X) (m n : ℕ+)
    (hExcisive : T.IsExcisive)
    (hA : NConnectedPair ((m : ℕ) - 1) T.leftIntersectionSubspace)
    (hB : NConnectedPair ((n : ℕ) - 1) T.rightIntersectionSubspace) :
    SpacePair.Hom.IsNEquivalence ((m : ℕ) + (n : ℕ) - 2) (triadSubspaceInclusion T) := sorry
