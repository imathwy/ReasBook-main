module

public import Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

open Filter
open scoped Topology

universe u

namespace SimplyConnectedSpace

/-- Exercise 82.1: Every simply connected space is semilocally simply connected. -/
instance instSemilocallySimplyConnectedSpace (X : Type u) [TopologicalSpace X]
    [SimplyConnectedSpace X] : SemilocallySimplyConnectedSpace X := by
  constructor
  intro x
  refine ⟨Set.univ, univ_mem, ?_⟩
  ext g
  exact Subsingleton.elim _ _

end SimplyConnectedSpace
