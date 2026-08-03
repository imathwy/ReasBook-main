module

public import Topology_Munkres_2000.Book.Lemma_23_1
public import Topology_Munkres_2000.Book.Example_23_5.ReciprocalGraph
public import Topology_Munkres_2000.Book.Exercise_17_20.RealPlane

public section

open Set
open scoped Set.Notation

namespace RealPlane

/-- The union of the real `x`-axis and the positive reciprocal graph. -/
def xAxisWithPositiveReciprocalGraph : Set (ℝ × ℝ) :=
  xAxis ∪ positiveReciprocalGraph

/-- Helper for Example 23.5: The positive reciprocal graph is the product-one
locus with nonnegative first coordinate. -/
lemma positiveReciprocalGraph_eq_productOne_inter_nonnegativeFst :
    positiveReciprocalGraph =
      {p : ℝ × ℝ | p.1 * p.2 = 1} ∩ {p : ℝ × ℝ | 0 ≤ p.1} := by
  -- Remove division pointwise, retaining the half-space condition that selects
  -- the positive branch of the product-one locus.
  ext p
  simp only [mem_positiveReciprocalGraph, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro hp
    have hp_ne : p.1 ≠ 0 := ne_of_gt hp.1
    refine ⟨?_, le_of_lt hp.1⟩
    rw [hp.2, one_div, mul_inv_cancel₀ hp_ne]
  · intro hp
    have hp_ne : p.1 ≠ 0 := by
      intro hp_zero
      rw [hp_zero, zero_mul] at hp
      exact zero_ne_one hp.1
    have hp_pos : 0 < p.1 := lt_of_le_of_ne hp.2 (Ne.symm hp_ne)
    refine ⟨hp_pos, ?_⟩
    apply (eq_div_iff hp_ne).2
    simpa only [mul_comm] using hp.1

/-- Helper for Example 23.5: The positive reciprocal graph is closed in the
real plane. -/
lemma positiveReciprocalGraph_isClosed : IsClosed positiveReciprocalGraph := by
  -- The division-free normal form is an intersection of two closed continuous loci.
  rw [positiveReciprocalGraph_eq_productOne_inter_nonnegativeFst]
  exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
    (isClosed_le continuous_const continuous_fst)

/-- Helper for Example 23.5: The real `x`-axis is disjoint from the positive
reciprocal graph. -/
lemma xAxis_disjoint_positiveReciprocalGraph :
    Disjoint xAxis positiveReciprocalGraph := by
  -- A reciprocal-graph point has positive height, whereas every axis point has height zero.
  rw [disjoint_left]
  intro p hp_axis hp_graph
  have hp_axis_zero : p.2 = 0 := (mem_xAxis_iff p).mp hp_axis
  have hp_graph_spec := (mem_positiveReciprocalGraph p).mp hp_graph
  have hp_height_pos : 0 < p.2 := by
    rw [hp_graph_spec.2]
    exact one_div_pos.mpr hp_graph_spec.1
  rw [hp_axis_zero] at hp_height_pos
  exact (lt_irrefl 0 hp_height_pos).elim

/-- Helper for Example 23.5: Neither indicated subset contains an ambient limit point of
the other. -/
theorem xAxis_reciprocalGraph_avoid_derivedSet :
    Disjoint xAxis (derivedSet positiveReciprocalGraph) ∧
      Disjoint positiveReciprocalGraph (derivedSet xAxis) := by
  -- Closedness confines each derived set to its defining component.
  have hgraph_derived : derivedSet positiveReciprocalGraph ⊆ positiveReciprocalGraph :=
    (isClosed_iff_derivedSet_subset positiveReciprocalGraph).mp
      positiveReciprocalGraph_isClosed
  have haxis_eq : xAxis = {p : ℝ × ℝ | p.2 = 0} := by
    ext p
    rw [mem_xAxis_iff]
    rfl
  have haxis_closed : IsClosed xAxis := by
    rw [haxis_eq]
    exact isClosed_eq continuous_snd continuous_const
  have haxis_derived : derivedSet xAxis ⊆ xAxis :=
    (isClosed_iff_derivedSet_subset xAxis).mp haxis_closed
  -- Restrict the established disjointness along those two inclusions.
  constructor
  · exact xAxis_disjoint_positiveReciprocalGraph.mono_right hgraph_derived
  · exact xAxis_disjoint_positiveReciprocalGraph.symm.mono_right haxis_derived

/-- Helper for Example 23.5: The indicated subsets form a separation of their union. -/
theorem xAxis_reciprocalGraph_isSeparation :
    (xAxisWithPositiveReciprocalGraph ↓∩ xAxis).IsSeparation
      (xAxisWithPositiveReciprocalGraph ↓∩ positiveReciprocalGraph) := by
  -- Supply one point in each component and the defining covering equation.
  have haxis_nonempty : xAxis.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    rw [mem_xAxis_iff]
  have hgraph_nonempty : positiveReciprocalGraph.Nonempty := by
    refine ⟨(1, 1), ?_⟩
    rw [mem_positiveReciprocalGraph]
    norm_num
  have hunion : xAxis ∪ positiveReciprocalGraph =
      xAxisWithPositiveReciprocalGraph := by
    rfl
  -- Lemma 23.1 converts mutual ambient limit-point avoidance into a separation.
  exact (Set.isSeparation_preimage_val_iff_disjoint_derivedSet
    xAxis_disjoint_positiveReciprocalGraph haxis_nonempty hgraph_nonempty hunion).mpr
      xAxis_reciprocalGraph_avoid_derivedSet

/-- Example 23.5: The union of the real `x`-axis and positive reciprocal graph
is not preconnected. -/
theorem xAxisWithPositiveReciprocalGraph_not_isPreconnected :
    ¬ IsPreconnected xAxisWithPositiveReciprocalGraph := by
  -- A preconnected subtype admits no separation, contradicting the one above.
  intro hpreconnected
  have hpreconnected_space : PreconnectedSpace xAxisWithPositiveReciprocalGraph :=
    isPreconnected_iff_preconnectedSpace.mp hpreconnected
  have hno_separation :
      ¬ ∃ U V : Set xAxisWithPositiveReciprocalGraph, U.IsSeparation V :=
    (preconnectedSpace_iff_no_separation xAxisWithPositiveReciprocalGraph).mp
      hpreconnected_space
  apply hno_separation
  exact ⟨xAxisWithPositiveReciprocalGraph ↓∩ xAxis,
    xAxisWithPositiveReciprocalGraph ↓∩ positiveReciprocalGraph,
    xAxis_reciprocalGraph_isSeparation⟩

end RealPlane
