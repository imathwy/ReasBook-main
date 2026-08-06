import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.GroupTheory.Index
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1

open scoped Manifold Topology

noncomputable section

-- Semantic recall via `lean_leansearch`: mathlib provides `SimplyConnectedSpace`,
-- `FundamentalGroup`, and subgroup-index API, while local Chapter 20 precedent records
-- orientability by `ROrientedManifold` and global orientations by
-- `ROrientedManifold.GlobalOrientation`. This file keeps the source-facing orientability
-- statements and states clause (3) on the canonical quotient of oriented atlases by the
-- same-orientation relation.

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
variable [Fact (Module.finrank ℝ E = n)]

/-- Corollary 20.6.3 (1). If `M` is simply connected, then `M` is orientable. In the chapter-local
API, orientability is expressed by `Nonempty (ROrientedManifold ℤ I n M)`. -/
theorem orientable_of_simplyConnected [SimplyConnectedSpace M] :
    Nonempty (ROrientedManifold ℤ I n M) := sorry

/-- Under simple connectedness, the orientability witness is available to typeclass search as a
`Nonempty` instance. -/
instance instNonemptyROrientedManifoldOfSimplyConnected [SimplyConnectedSpace M] :
    Nonempty (ROrientedManifold ℤ I n M) :=
  orientable_of_simplyConnected

section

variable [ConnectedSpace M]

/-- Corollary 20.6.3 (2). If, for a basepoint `x : M`, the group `FundamentalGroup M x` has no
subgroup of index `2`, then `M` is orientable. On a connected manifold, this is the usual unbased
condition that `π₁(M)` has no subgroup of index `2`. -/
theorem orientable_of_no_indexTwoSubgroup
    (x : M) (h_no_index_two : ∀ H : Subgroup (FundamentalGroup M x), H.index ≠ 2) :
    Nonempty (ROrientedManifold ℤ I n M) := sorry

/-- Corollary 20.6.3 (2), unbased form: if every basepoint fundamental group of the connected
manifold `M` has no subgroup of index `2`, then `M` is orientable. -/
theorem orientable_of_no_indexTwoSubgroup_unbased
    (h_no_index_two : ∀ x : M, ∀ H : Subgroup (FundamentalGroup M x), H.index ≠ 2) :
    Nonempty (ROrientedManifold ℤ I n M) := by
  classical
  let x : M := Classical.choice inferInstance
  exact orientable_of_no_indexTwoSubgroup x (h_no_index_two x)

/-- Corollary 20.6.3 (3). If `M` is orientable, then it has exactly two global orientations. In
the current repository, a global orientation is formalized canonically as a
`ROrientedManifold.GlobalOrientation ℤ I n M`, i.e. an oriented-atlas class modulo the
same-orientation relation. -/
theorem hasExactlyTwoOrientations_of_orientable
    (h_orientable : Nonempty (ROrientedManifold ℤ I n M)) :
    ∃ o : ROrientedManifold.GlobalOrientation ℤ I n M,
      ROrientedManifold.GlobalOrientation.opposite o ≠ o ∧
        ∀ o' : ROrientedManifold.GlobalOrientation ℤ I n M,
          o' = o ∨ o' = ROrientedManifold.GlobalOrientation.opposite o := sorry

end

end
