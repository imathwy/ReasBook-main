import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_1

noncomputable section

universe u w

open scoped Topology Topology.Homotopy

/-- Theorem 11.2.2 (1): if `X` is nondegenerately based and `(n - 1)`-connected, then suspension
induces a bijection `π_ q(X) → π_ (q + 1)(ΣX)` for every `q < 2 * n - 1`. -/
theorem freudenthalSuspension_bijective
    (n : ℕ+) (X : PointedCompactlyGenerated.{u, w})
    [WellPointedSpace X]
    [NConnectedSpace ((n : ℕ) - 1) X.toCompactlyGenerated]
    (q : ℕ) (hq : q < 2 * (n : ℕ) - 1) :
    Function.Bijective (suspensionPiMap q X) := sorry

/-- In positive degree, Theorem 11.2.2 (1) can be read on the canonical group-hom owner
`suspensionHomomorphism q X`. -/
theorem freudenthalSuspensionHomomorphism_bijective
    (n : ℕ+) (X : PointedCompactlyGenerated.{u, w})
    [WellPointedSpace X]
    [NConnectedSpace ((n : ℕ) - 1) X.toCompactlyGenerated]
    (q : ℕ) [NeZero q] (hq : q < 2 * (n : ℕ) - 1) :
    Function.Bijective (suspensionHomomorphism q X) := by
  change Function.Bijective (suspensionPiMap q X)
  exact freudenthalSuspension_bijective n X q hq

/-- Theorem 11.2.2 (2): if `X` is nondegenerately based and `(n - 1)`-connected, then suspension
induces a surjection `π_ (2 * n - 1)(X) → π_ (2 * n)(ΣX)` in the top degree `q = 2 * n - 1`. -/
theorem freudenthalSuspension_surjective
    (n : ℕ+) (X : PointedCompactlyGenerated.{u, w})
    [WellPointedSpace X]
    [NConnectedSpace ((n : ℕ) - 1) X.toCompactlyGenerated] :
    Function.Surjective (suspensionPiMap (2 * (n : ℕ) - 1) X) := sorry
