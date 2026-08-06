import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Tactic.Recall
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_5_1

universe u

noncomputable section

open CategoryTheory

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` and
-- `AlgebraicTopology.singularHomologyFunctor` are the canonical homotopy and homology owners in
-- mathlib, while Construction 16.5.1 provides the classifying-space owner
-- `groupClassifyingSpace`.

/- Remark 16.5.5. Construction 16.5.1 already turns a topological group `G` into the space
`groupClassifyingSpace G`. The present remark is motivational rather than a precise theorem: the
point is that one studies homotopy and homology invariants of this space to recover
group-theoretic information, so this item is recorded as a labeled recall block around the
existing classifying-space owner and the canonical invariant APIs. -/
recall groupClassifyingSpace
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : TopCat

recall HomotopyGroup.Pi
recall AlgebraicTopology.singularHomologyFunctor

section

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The `n`-th homotopy group of the classifying space `BG` at a basepoint `x`. -/
abbrev groupClassifyingSpaceHomotopyGroup (n : ℕ) (x : groupClassifyingSpace G) :=
  HomotopyGroup.Pi n (groupClassifyingSpace G) x

/-- Singular homology of `BG` with coefficients in `R`. -/
abbrev groupClassifyingSpaceSingularHomology
    {C : Type*} [Category C] [Limits.HasCoproducts C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) : C :=
  ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj (groupClassifyingSpace G)

end

end
