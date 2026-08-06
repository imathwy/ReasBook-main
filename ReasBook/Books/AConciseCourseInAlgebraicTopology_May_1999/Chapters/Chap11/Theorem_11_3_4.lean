import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Theorem_11_1_2

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: no current mathlib owner for triad-relative homotopy
-- excision vanishing surfaced in the environment. Local Chapter 10/11 precedent already fixes
-- the source-faithful owners `Triad.IsExcisive`, `NConnectedPair`, and `triadHomotopyGroup`.

/-- Theorem 11.3.4: under the hypotheses of homotopy excision, the triad homotopy group
`π_q(X; A, B)` is trivial for every basepoint `x ∈ A ∩ B` and every degree `q` with
`2 ≤ q ≤ (m : ℕ) + (n : ℕ) - 2`. -/
theorem triadHomotopyGroup_subsingleton_of_homotopyExcision
    (T : Triad X) (x : T.intersection) (m n : ℕ+) (q : ℕ)
    (hq₂ : 2 ≤ q) (hqmn : q ≤ (m : ℕ) + (n : ℕ) - 2)
    (hExcisive : T.IsExcisive)
    [hA : NConnectedPair ((m : ℕ) - 1) T.leftIntersectionSubspace]
    [hB : NConnectedPair ((n : ℕ) - 1) T.rightIntersectionSubspace] :
    Subsingleton (triadHomotopyGroup T x q hq₂) := sorry
