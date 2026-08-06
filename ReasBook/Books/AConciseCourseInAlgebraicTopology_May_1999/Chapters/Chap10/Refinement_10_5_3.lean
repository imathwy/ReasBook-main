import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_5_1
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.CWComplex.Classical.Basic

open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex.cell` is the canonical owner for the
-- cells of a chosen classical CW structure, while Chapter 10 records a chosen approximation map by
-- the owner `IsCWApproximation γ`. The source refinement therefore keeps that approximation owner
-- and adds a chosen classical structure on the same space to state the `0`-cell and
-- low-dimensional vanishing clauses.

namespace Topology.CWComplex

/-- A chosen classical CW structure has no cells in positive dimensions at most `n` when each
`q`-cell type is empty for `1 ≤ q ≤ n`. -/
def NoCellsLE {X : Type u} [TopologicalSpace X] {C : Set X} (cw : CWComplex C) (n : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ n → IsEmpty (cw.cell q)

/-- A `NoCellsLE` hypothesis can be used directly to eliminate low-dimensional positive cells. -/
theorem noCellsLE_isEmptyCell {X : Type u} [TopologicalSpace X] {C : Set X} {cw : CWComplex C}
    {n q : ℕ} (h_noCells : cw.NoCellsLE n) (hq₁ : 1 ≤ q) (hqn : q ≤ n) :
    IsEmpty (cw.cell q) :=
  h_noCells q hq₁ hqn

/-- If a classical CW structure has no positive-dimensional cells up to `n`, then it also has no
positive-dimensional cells up to any smaller bound. -/
theorem NoCellsLE.mono {X : Type u} [TopologicalSpace X] {C : Set X} {cw : CWComplex C}
    {m n : ℕ} (h_noCells : cw.NoCellsLE n) (hmn : m ≤ n) :
    cw.NoCellsLE m := fun q hq₁ hqm ↦ h_noCells q hq₁ (Nat.le_trans hqm hmn)

end Topology.CWComplex

/-- Refinement 10.5.3: if `X` is `n`-connected with `n ≥ 1`, then one can choose a CW
approximation `approx : CWApproximation X` whose source has exactly one `0`-cell and no `q`-cells
for `1 ≤ q ≤ n`. -/
theorem exists_cwApproximation_uniqueVertex_noCells
    (X : TopCat.{u}) (n : ℕ) [NConnectedSpace n X] (hX₀ : Nonempty X) (hn : 1 ≤ n) :
    ∃ approx : CWApproximation X,
      ∃ cw : Topology.CWComplex (Set.univ : Set approx.Γ),
        Nat.card (cw.cell 0) = 1 ∧
          cw.NoCellsLE n := sorry
