module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.CWComplexBasic

public section

universe u

/-
`RelCWComplex` is the canonical owner for relative CW attachments. Definition 10.1.3 only
recalls the standard characteristic maps, cells, and skeleta already provided there.
-/

namespace Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]

/- Definition 10.1.3: in mathlib's `RelCWComplex` API, the relative attachment data is given by
the characteristic maps `map (n + 1) i`, the corresponding closed cells
`closedCell (n + 1) i`, and, under Hausdorff hypotheses, the canonical relative `n`-skeleton
`skeleton C (n : ℕ∞)`. -/

section

variable (n : ℕ) (i : cell C (n + 1))

/- The characteristic map of the `(n + 1)`-cell indexed by `i`. -/
#check map (n + 1) i

/- The corresponding closed `(n + 1)`-cell in the ambient space. -/
#check closedCell (n + 1) i

end

section

variable [T2Space X]
variable (n : ℕ)

/- The canonical relative `n`-skeleton of the CW attachment. -/
#check skeleton C (n : ℕ∞)

/- The next relative skeleton is obtained by adjoining the closed `(n + 1)`-cells to the fixed
relative `n`-skeleton of `C`. -/
theorem skeleton_succ_eq_skeleton_union_iUnion_closedCell :
    skeleton C (n + 1 : ℕ∞) =
      (skeleton C (n : ℕ∞) : Set X) ∪ ⋃ (j : cell C (n + 1)), closedCell (n + 1) j := by
  symm
  exact skeleton_union_iUnion_closedCell_eq_skeleton_succ n

end

end Topology.RelCWComplex
