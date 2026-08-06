import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4

open Topology
open Topology.RelCWComplex

universe u

-- Semantic recall via `lean_leansearch`: no source-exact quotient-CW theorem surfaced in the
-- current mathlib snapshot. This file therefore reuses the repository's canonical collapse
-- quotient owner `collapseSubsetType` and expresses the source-specified quotient cell structure
-- as a predicate on CW structures carried by `X / A`.

namespace Topology.RelCWComplex

/-- A CW structure on `X / A` is compatible with the relative cells of `(X, A)` if its `0`-cells
consist of the collapsed vertex, when `A` is nonempty, together with the relative `0`-cells, and
its positive-degree cells are indexed by the relative cells of `(X, A)`. -/
def IsQuotientCWComplex
    {X : Type u} [TopologicalSpace X] (A : Set X)
    [RelCWComplex (Set.univ : Set X) A]
    (cw : CWComplex (Set.univ : Set (collapseSubsetType X A))) : Prop :=
  Nonempty (cw.cell 0 ≃ (PLift A.Nonempty ⊕ cell (Set.univ : Set X) 0)) ∧
    ∀ n : ℕ, Nonempty (cw.cell (n + 1) ≃ cell (Set.univ : Set X) (n + 1))

namespace IsQuotientCWComplex

variable {X : Type u} [TopologicalSpace X] {A : Set X}
variable [RelCWComplex (Set.univ : Set X) A]
variable {cw : CWComplex (Set.univ : Set (collapseSubsetType X A))}

/-- In a quotient-compatible CW structure, the `0`-cells are indexed by the collapsed vertex,
when present, together with the relative `0`-cells. -/
theorem zero (h : IsQuotientCWComplex A cw) :
    Nonempty (cw.cell 0 ≃ (PLift A.Nonempty ⊕ cell (Set.univ : Set X) 0)) :=
  h.1

/-- In a quotient-compatible CW structure, the positive-degree cells are indexed by the relative
cells of `(X, A)`. -/
theorem succ (h : IsQuotientCWComplex A cw) (n : ℕ) :
    Nonempty (cw.cell (n + 1) ≃ cell (Set.univ : Set X) (n + 1)) :=
  h.2 n

end IsQuotientCWComplex
end Topology.RelCWComplex

/-- Lemma 10.2.1. If `(X, A)` is a relative CW complex, then the quotient `X / A`, formalized as
`collapseSubsetType X A`, admits a CW structure whose `0`-cells are indexed by the single
collapsed vertex coming from `A`, when `A` is nonempty, together with the relative `0`-cells, and
whose positive-degree cells are indexed by the relative cells of `(X, A)`. -/
theorem quotientHasCWComplexWithRelativeCells
    (X : Type u) [TopologicalSpace X] (A : Set X)
    [RelCWComplex (Set.univ : Set X) A] :
    ∃ cw : CWComplex (Set.univ : Set (collapseSubsetType X A)),
      IsQuotientCWComplex A cw := sorry

/-- The quotient `X / A` of a relative CW complex `(X, A)` is a CW complex. -/
theorem quotientIsCWComplex
    (X : Type u) [TopologicalSpace X] (A : Set X)
    [RelCWComplex (Set.univ : Set X) A] :
    Nonempty (CWComplex (Set.univ : Set (collapseSubsetType X A))) := by
  rcases quotientHasCWComplexWithRelativeCells X A with ⟨cw, _⟩
  exact ⟨cw⟩
