import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Definition_15_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory
open Topology

universe u

-- Chapter 15 already owns the canonical skeletal pair `(X^n, X^(n - 1))` as
-- `axiomaticCellularChainPair X n`, with `X^(-1)` represented by `∅` through
-- `previousCellularSkeleton X 0 = ∅`. Definition 19.5.1 therefore reuses that pair owner and
-- evaluates a Chapter 18 `PairCohomologyTheory` on it.

/-- Definition 19.5.1. For a pair cohomology theory `H^*(-; π)` and a CW complex `X`, the
axiomatic cellular cochains in degree `n` are the relative cohomology group
`H^n(X^n, X^(n - 1); π)`. -/
abbrev axiomaticCellularCochains
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    AddCommGrpCat :=
  (H (n : ℤ)).obj (Opposite.op (axiomaticCellularChainPair X n))

/-- Unfolding `axiomaticCellularCochains` identifies it with the evaluation of `H^n(-; π)` on the
skeletal pair `(X^n, X^(n - 1))`. -/
@[simp] theorem axiomaticCellularCochains_def
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    axiomaticCellularCochains H X n =
      (H (n : ℤ)).obj (Opposite.op (axiomaticCellularChainPair X n)) :=
  rfl
