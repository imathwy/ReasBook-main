module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Theorem_78_1.TriangleEdgeTopology
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Perfect

public section

universe u

namespace Topology

/-- Helper for Theorem 78.1: every open neighborhood in a topological surface
contains an open neighborhood whose puncture is connected. -/
theorem exists_open_puncturedConnected_subset
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    {O : Set X} {x : X} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧ IsConnected (U \ {x}) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) x x
  have hchartNhds : chartAt (EuclideanSpace ℝ (Fin 2)) x ''
      (O ∩ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) ∈ nhds c := by
    -- The chart sends the chosen ambient neighborhood to a neighborhood of
    -- the coordinate representative of `x`.
    apply (chartAt (EuclideanSpace ℝ (Fin 2)) x).image_mem_nhds
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) x)
    exact Filter.inter_mem (hO.mem_nhds hxO)
      (chart_source_mem_nhds (EuclideanSpace ℝ (Fin 2)) x)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hchartNhds
  let e := (OpenPartialHomeomorph.univBall c r).trans
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
  let U := e '' Set.univ
  have hesource : e.source = Set.univ := by
    ext y
    simp only [e, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.univBall_source, Set.mem_inter_iff, Set.mem_univ,
      true_and, Set.mem_preimage]
    have hyball : OpenPartialHomeomorph.univBall c r y ∈ Metric.ball c r := by
      rw [← OpenPartialHomeomorph.univBall_target c hr]
      exact (OpenPartialHomeomorph.univBall c r).map_source (by simp)
    obtain ⟨z, hz, hzy⟩ := hrsub hyball
    rw [← hzy]
    exact iff_true_intro
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).map_source hz.2)
  have hezero : e 0 = x := by
    -- The radial ball chart sends zero to the chart coordinate of `x`, and
    -- the manifold chart inverse then returns `x`.
    simp only [e, OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.univBall_apply_zero, c]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).left_inv
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) x)
  have hUOpen : IsOpen U := by
    -- Since the composite chart has full source, its image is its open target.
    unfold U
    rw [← hesource, e.image_source_eq_target]
    exact e.open_target
  have hxU : x ∈ U := by
    rw [← hezero]
    exact ⟨0, Set.mem_univ 0, rfl⟩
  have hUO : U ⊆ O := by
    rintro y ⟨z, -, hzy⟩
    have hzball : OpenPartialHomeomorph.univBall c r z ∈ Metric.ball c r := by
      rw [← OpenPartialHomeomorph.univBall_target c hr]
      exact (OpenPartialHomeomorph.univBall c r).map_source (by simp)
    obtain ⟨q, hq, hqz⟩ := hrsub hzball
    have heq : e z = q := by
      calc
        e z = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
            (OpenPartialHomeomorph.univBall c r z) := rfl
        _ = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
            (chartAt (EuclideanSpace ℝ (Fin 2)) x q) := congrArg _ hqz.symm
        _ = q := (chartAt (EuclideanSpace ℝ (Fin 2)) x).left_inv hq.2
    rw [← hzy, heq]
    exact hq.1
  have hpuncture : U \ {x} = e '' (Set.univ \ {0}) := by
    -- Injectivity of the local homeomorphism lets image commute with deleting
    -- the distinguished point.
    change (e '' Set.univ) \ {x} = e '' (Set.univ \ {0})
    rw [Set.image_sdiff]
    · rw [Set.image_singleton, hezero]
    · intro y z hyz
      exact e.injOn (hesource ▸ Set.mem_univ y)
        (hesource ▸ Set.mem_univ z) hyz
  have hplanePuncture : IsConnected
      ((Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {0}) := by
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [← Module.finrank_eq_rank]
      norm_num
    have hset : (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {0} =
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_univ, true_and,
        Set.mem_singleton_iff, Set.mem_compl_iff]
    rw [hset]
    exact isConnected_compl_singleton_of_one_lt_rank hrank 0
  have hUConnected : IsConnected (U \ {x}) := by
    -- Transport connectedness of the punctured plane through the composite
    -- ball and manifold chart.
    rw [hpuncture]
    exact hplanePuncture.image e
      (e.continuousOn.mono fun y _ ↦ hesource ▸ Set.mem_univ y)
  exact ⟨U, hUOpen, hxU, hUO, hUConnected⟩

end Topology

namespace CurvedTriangle

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 78.1: every ambient open neighborhood of a point of a
curved triangle contains a different point of the same triangle. -/
theorem exists_mem_open_ne_of_mem_carrier (triangle : CurvedTriangle X)
    {v : X} (hv : v ∈ triangle.carrier) {U : Set X}
    (hU : IsOpen U) (hvU : v ∈ U) :
    ∃ y : X, y ∈ U ∧ y ∈ triangle.carrier ∧ y ≠ v := by
  have hmodelConnected : IsConnected triangle.model.closedInterior := by
    rw [← triangle.model.convexHull_eq_closedInterior]
    exact (convex_convexHull ℝ (Set.range triangle.model.points)).isConnected
      ((Set.range_nonempty triangle.model.points).mono
        (subset_convexHull ℝ (Set.range triangle.model.points)))
  letI : ConnectedSpace triangle.model.closedInterior :=
    isConnected_iff_connectedSpace.mp hmodelConnected
  let first : triangle.model.closedInterior :=
    ⟨triangle.model.points 0, triangle.model.point_mem_closedInterior 0⟩
  let second : triangle.model.closedInterior :=
    ⟨triangle.model.points 1, triangle.model.point_mem_closedInterior 1⟩
  have hfirstSecond : first ≠ second := by
    intro h
    have hpoints : triangle.model.points 0 = triangle.model.points 1 :=
      congrArg Subtype.val h
    exact (triangle.model.independent.injective.ne (by decide)) hpoints
  letI : Nontrivial triangle.model.closedInterior :=
    ⟨⟨first, second, hfirstSecond⟩⟩
  let q : triangle.model.closedInterior := triangle.chart.symm ⟨v, hv⟩
  let V : Set triangle.model.closedInterior :=
    (fun z ↦ (triangle.chart z : X)) ⁻¹' U
  have hVOpen : IsOpen V := by
    exact hU.preimage (continuous_subtype_val.comp triangle.chart.continuous)
  have hchartQ : (triangle.chart q : X) = v := by
    exact congrArg Subtype.val (triangle.chart.apply_symm_apply ⟨v, hv⟩)
  have hqV : q ∈ V := by
    rw [Set.mem_preimage, hchartQ]
    exact hvU
  have hpreperfect := PerfectSpace.univ_preperfect q (Set.mem_univ q)
  rw [accPt_iff_nhds] at hpreperfect
  obtain ⟨z, hz, hzq⟩ :=
    hpreperfect V (hVOpen.mem_nhds hqV)
  refine ⟨triangle.chart z, hz.1, (triangle.chart z).property, ?_⟩
  -- Injectivity of the triangle chart turns equality in the ambient space
  -- back into equality with the selected model point.
  intro hzv
  apply hzq
  apply triangle.chart.injective
  apply Subtype.ext
  exact hzv.trans hchartQ.symm

end CurvedTriangle

namespace Triangulation

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 78.1: triangles containing a fixed surface point are
connected within its vertex star by pairwise overlaps away from that point. -/
theorem vertexStarConnectedWithin
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangulation : Triangulation X) (v : X)
    (i j : Fin triangulation.card)
    (hi : v ∈ (triangulation.triangle i).carrier)
    (hj : v ∈ (triangulation.triangle j).carrier) :
    Relation.ReflTransGen
      (fun a b ↦ v ∈ (triangulation.triangle a).carrier ∧
        v ∈ (triangulation.triangle b).carrier ∧
          (((triangulation.triangle a).carrier ∩
            (triangulation.triangle b).carrier) \ {v}).Nonempty) i j := by
  classical
  let adjacent : Fin triangulation.card → Fin triangulation.card → Prop :=
    fun a b ↦ v ∈ (triangulation.triangle a).carrier ∧
      v ∈ (triangulation.triangle b).carrier ∧
        (((triangulation.triangle a).carrier ∩
          (triangulation.triangle b).carrier) \ {v}).Nonempty
  change Relation.ReflTransGen adjacent i j
  by_contra hchain
  let reachable : Set (Fin triangulation.card) :=
    {k | v ∈ (triangulation.triangle k).carrier ∧
      Relation.ReflTransGen adjacent i k}
  let excluded : Set X :=
    ⋃ k : {k : Fin triangulation.card //
        v ∉ (triangulation.triangle k).carrier},
      (triangulation.triangle k.1).carrier
  have hExcludedClosed : IsClosed excluded := by
    dsimp only [excluded]
    exact isClosed_iUnion_of_finite fun k ↦
      (triangulation.triangle k.1).isClosed_carrier
  have hvExcluded : v ∉ excluded := by
    intro hv
    obtain ⟨k, hvk⟩ := Set.mem_iUnion.mp hv
    exact k.2 hvk
  obtain ⟨U, hUOpen, hvU, hUExcluded, hUPuncturedConnected⟩ :=
    Topology.exists_open_puncturedConnected_subset
      hExcludedClosed.isOpen_compl hvExcluded
  let left : Set X :=
    ⋃ k : {k : Fin triangulation.card // k ∈ reachable},
      (triangulation.triangle k.1).carrier
  let right : Set X :=
    ⋃ k : {k : Fin triangulation.card //
        v ∈ (triangulation.triangle k).carrier ∧ k ∉ reachable},
      (triangulation.triangle k.1).carrier
  have hLeftClosed : IsClosed left := by
    dsimp only [left]
    exact isClosed_iUnion_of_finite fun k ↦
      (triangulation.triangle k.1).isClosed_carrier
  have hRightClosed : IsClosed right := by
    dsimp only [right]
    exact isClosed_iUnion_of_finite fun k ↦
      (triangulation.triangle k.1).isClosed_carrier
  have hPuncturedCover : U \ {v} ⊆ left ∪ right := by
    intro y hy
    have hyCover : y ∈ ⋃ k, (triangulation.triangle k).carrier := by
      rw [triangulation.cover]
      exact Set.mem_univ y
    obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hyCover
    have hvk : v ∈ (triangulation.triangle k).carrier := by
      by_contra hvk
      exact hUExcluded hy.1 (Set.mem_iUnion.mpr ⟨⟨k, hvk⟩, hyk⟩)
    by_cases hreachable : k ∈ reachable
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨k, hreachable⟩, hyk⟩)
    · exact Or.inr
        (Set.mem_iUnion.mpr ⟨⟨k, hvk, hreachable⟩, hyk⟩)
  have hPuncturedDisjoint : (U \ {v}) ∩ (left ∩ right) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hyPunctured, hyLeft, hyRight⟩
    obtain ⟨a, hya⟩ := Set.mem_iUnion.mp hyLeft
    obtain ⟨b, hyb⟩ := Set.mem_iUnion.mp hyRight
    have hab : adjacent a.1 b.1 := by
      exact ⟨a.2.1, b.2.1, y, ⟨⟨hya, hyb⟩, hyPunctured.2⟩⟩
    exact b.2.2 ⟨b.2.1, Relation.ReflTransGen.tail a.2.2 hab⟩
  have hleftReach : i ∈ reachable := ⟨hi, Relation.ReflTransGen.refl⟩
  have hjNotReach : j ∉ reachable := by
    exact fun hjReach ↦ hchain hjReach.2
  obtain ⟨yi, hyiU, hyiCarrier, hyiv⟩ :=
    (triangulation.triangle i).exists_mem_open_ne_of_mem_carrier hi hUOpen hvU
  have hyiPunctured : yi ∈ U \ {v} :=
    ⟨hyiU, by simpa only [Set.mem_singleton_iff]⟩
  have hyiLeft : yi ∈ left :=
    Set.mem_iUnion.mpr ⟨⟨i, hleftReach⟩, hyiCarrier⟩
  obtain ⟨yj, hyjU, hyjCarrier, hyjv⟩ :=
    (triangulation.triangle j).exists_mem_open_ne_of_mem_carrier hj hUOpen hvU
  have hyjPunctured : yj ∈ U \ {v} :=
    ⟨hyjU, by simpa only [Set.mem_singleton_iff]⟩
  have hyjRight : yj ∈ right :=
    Set.mem_iUnion.mpr ⟨⟨j, hj, hjNotReach⟩, hyjCarrier⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      hUPuncturedConnected.isPreconnected left right hLeftClosed hRightClosed
        hPuncturedCover hPuncturedDisjoint) with hleft | hright
  · have : yj ∈ (U \ {v}) ∩ (left ∩ right) :=
      ⟨hyjPunctured, hleft hyjPunctured, hyjRight⟩
    rw [hPuncturedDisjoint] at this
    exact this.elim
  · have : yi ∈ (U \ {v}) ∩ (left ∩ right) :=
      ⟨hyiPunctured, hyiLeft, hright hyiPunctured⟩
    rw [hPuncturedDisjoint] at this
    exact this.elim

/-- Helper for Theorem 78.1: forgetting the vertex-star membership carried by
each step leaves the overlap-chain formulation used by the presentation proof. -/
theorem vertexStarConnected
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangulation : Triangulation X) (v : X)
    (i j : Fin triangulation.card)
    (hi : v ∈ (triangulation.triangle i).carrier)
    (hj : v ∈ (triangulation.triangle j).carrier) :
    Relation.ReflTransGen
      (fun a b ↦ (((triangulation.triangle a).carrier ∩
        (triangulation.triangle b).carrier) \ {v}).Nonempty) i j := by
  -- The source-facing chain stays within the vertex star; erase those two
  -- membership certificates while preserving every off-vertex overlap.
  have hmono :
      (fun a b : Fin triangulation.card ↦
        v ∈ (triangulation.triangle a).carrier ∧
          v ∈ (triangulation.triangle b).carrier ∧
            (((triangulation.triangle a).carrier ∩
              (triangulation.triangle b).carrier) \ {v}).Nonempty) ≤
        (fun a b ↦ (((triangulation.triangle a).carrier ∩
          (triangulation.triangle b).carrier) \ {v}).Nonempty) := by
    intro a b h
    exact h.2.2
  exact Relation.ReflTransGen.mono hmono i j
    (triangulation.vertexStarConnectedWithin v i j hi hj)

end Triangulation
