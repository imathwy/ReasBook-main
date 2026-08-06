import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_4

universe w

namespace Topology.CWComplex

/-- A chosen CW structure on the whole space supplies the Hausdorffness needed to evaluate the
canonical dimension owner `Topology.RelCWComplex.dimLE`. This stays private here so the
source-facing item can use the bridge without depending on Chapter 10's later helper module. -/
private theorem t2SpaceOfUnivCWComplex
    {X : Type w} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] : T2Space X := by
  sorry

/-- A chosen CW structure `cw` on `X` has dimension at most `n` when, after installing `cw` as
the ambient CW-complex instance, the canonical owner
`Topology.RelCWComplex.dimLE (Set.univ : Set X) n` holds. This is a bridge for source-facing
existence statements that quantify over explicit CW structures. -/
abbrev dimLE {X : Type w} [TopologicalSpace X]
    (cw : CWComplex (Set.univ : Set X)) (n : ℕ) : Prop :=
  -- Local instance justification (noncanonical choice): this bridge evaluates the canonical
  -- `Topology.RelCWComplex.dimLE` owner on the explicitly chosen CW structure `cw`.
  letI : CWComplex (Set.univ : Set X) := cw
  letI : T2Space X := t2SpaceOfUnivCWComplex
  Topology.RelCWComplex.dimLE (Set.univ : Set X) n

/-- If a CW structure on `X` has dimension at most `1` in the canonical sense
`Topology.RelCWComplex.dimLE (Set.univ : Set X) 1`, then every cell type in dimension `n > 1`
is empty. -/
theorem isEmpty_cell_of_one_lt_of_dimLE_one {X : Type w} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] (h_dim : Topology.RelCWComplex.dimLE (Set.univ : Set X) 1) :
    ∀ n : ℕ, 1 < n → IsEmpty (cell (Set.univ : Set X) n) := by
  intro n hn
  refine ⟨fun j ↦ ?_⟩
  have h_disjoint :
      Disjoint (skeleton (Set.univ : Set X) 1 : Set X) (openCell n j) :=
    disjoint_skeleton_openCell (by exact_mod_cast hn)
  have h_mem_skeleton : map n j 0 ∈ (skeleton (Set.univ : Set X) 1 : Set X) := by
    exact h_dim.symm ▸ (by simp : map n j 0 ∈ (Set.univ : Set X))
  have h_mem_open : map n j 0 ∈ openCell n j := map_zero_mem_openCell n j
  exact (Set.disjoint_left.1 h_disjoint h_mem_skeleton h_mem_open).elim

end Topology.CWComplex
