import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set
open scoped Topology

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for based
-- homotopy groups, `SimplyConnectedSpace` is the source-facing simple-connectivity owner, and
-- Chapter 10's `NConnectedSpace 1 X` is the local repository bridge for the same hypothesis. No
-- existing Serre-style infinitude theorem for this remark was found in the current workspace, so
-- the source is recorded as a direct theorem skeleton together with a `1`-connected companion.

section

variable {X : Type u} [TopologicalSpace X]
variable [Topology.CWComplex (univ : Set X)]
variable [Topology.CWComplex.Finite (univ : Set X)]

/-- Remark 10.3.6: a simply connected finite CW complex that is not contractible has infinitely
many nontrivial higher homotopy groups `π_ q X x`. This is the source-faithful Serre-style
content behind the remark that Whitehead's theorem is unexpectedly strong in this range. -/
theorem infinite_nontrivial_higherHomotopyGroups_of_finite_simplyConnected_noncontractible_CWComplex
    [SimplyConnectedSpace X] (x : X) (h_not_contractible : ¬ ContractibleSpace X) :
    Set.Infinite { q : ℕ | 1 < q ∧ ¬ Subsingleton (π_ q X x) } := sorry

/-- The same Serre-style conclusion under the repository's `1`-connectedness owner. -/
theorem infinite_nontrivial_higherHomotopyGroups_of_finite_oneConnected_noncontractible_CWComplex
    [NConnectedSpace 1 X] (x : X) (h_not_contractible : ¬ ContractibleSpace X) :
    Set.Infinite { q : ℕ | 1 < q ∧ ¬ Subsingleton (π_ q X x) } := by
  let _ : Nonempty X := ⟨x⟩
  let _ : SimplyConnectedSpace X := inferInstance
  exact
    infinite_nontrivial_higherHomotopyGroups_of_finite_simplyConnected_noncontractible_CWComplex
      x h_not_contractible

end
