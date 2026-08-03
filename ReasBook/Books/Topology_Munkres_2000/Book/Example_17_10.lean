module

public import Topology_Munkres_2000.Book.Example_12_1.ThreePointTopology
public import Mathlib.Topology.Separation.Hausdorff

public section

open Filter

/- Example 17.10 (1): In a Hausdorff space, and hence in `ℝ` and `ℝ × ℝ`,
a sequence cannot converge to two different points. -/
#check tendsto_nhds_unique

namespace ThreePointTopology

/-- Helper for Example 17.10: every nonempty open set in the Figure 17.3 topology
contains `ThreePoint.b`. -/
private lemma b_mem_of_isOpen_of_nonempty {s : Set ThreePoint}
    (hs : (topology .bAndABAndBC).IsOpen s) (hne : s.Nonempty) : ThreePoint.b ∈ s := by
  -- Reduce openness to the five displayed open sets and inspect each possibility.
  have hlisted := (isOpen_iff .bAndABAndBC s).mp hs
  rw [mem_openSets_bAndABAndBC_iff] at hlisted
  rcases hlisted with rfl | rfl | rfl | rfl | rfl
  · exact (Set.not_nonempty_empty hne).elim
  · simp
  · simp
  · simp
  · simp

/-- Helper for Example 17.10: `ThreePoint.b` specializes to every point in the
Figure 17.3 topology. -/
private lemma b_specializes_everyPoint (x : ThreePoint) :
    @Specializes ThreePoint (topology .bAndABAndBC) ThreePoint.b x := by
  -- An open neighborhood of `x` is nonempty, hence contains `b`.
  rw [@specializes_iff_forall_open ThreePoint (topology .bAndABAndBC)]
  intro s hs hx
  exact b_mem_of_isOpen_of_nonempty hs ⟨x, hx⟩

/-- Example 17.10 (2): The constant sequence at `b` converges to every point of
`ThreePoint`, and therefore in particular to `a`, `b`, and `c`. -/
theorem tendsto_const_b (x : ThreePoint) :
    Tendsto (fun _ : ℕ ↦ ThreePoint.b) atTop
      (Displayed.neighborhoods .bAndABAndBC x) := by
  -- Constant convergence to `pure b` weakens along the specialization inequality.
  rw [Displayed.neighborhoods_eq]
  exact tendsto_const_pure.mono_right
    ((@specializes_iff_pure ThreePoint (topology .bAndABAndBC) ThreePoint.b x).mp
      (b_specializes_everyPoint x))

end ThreePointTopology
