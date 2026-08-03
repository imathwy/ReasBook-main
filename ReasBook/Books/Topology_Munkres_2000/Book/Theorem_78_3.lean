module

public import Topology_Munkres_2000.Book.Theorem_78_3.WithHoles
public import Topology_Munkres_2000.Book.Theorem_78_3.BoundaryRank
public import Topology_Munkres_2000.Book.Theorem_78_3.BoundaryIncidence
public import Topology_Munkres_2000.Book.Theorem_78_2
public import Topology_Munkres_2000.Book.Theorem_77_1
public import Topology_Munkres_2000.Book.Definition_78_1.Triangulation
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_74_5.OrientablePasting
public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Topology_Munkres_2000.Book.Definition_74_6.Presentation
public import Topology_Munkres_2000.Book.Definition_78_3
public import Topology_Munkres_2000.Book.Exercise_78_2
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import all Topology_Munkres_2000.Book.Definition_78_1.Triangulation

open scoped Manifold SurfaceBoundary

public section

universe u v w

namespace Surface.HoleCharts

/-- Helper for Theorem 78.3: postcomposition by a homeomorphism preserves the
pairwise disjointness of the targets of a family of hole charts. -/
theorem pairwiseDisjoint_target_mapHomeomorph
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    {k : ℕ} (charts : HoleCharts X k) (e : X ≃ₜ Z) :
    Set.univ.PairwiseDisjoint
      (fun i ↦ ((charts i).transHomeomorph e).target) := by
  -- Rewrite transported targets as inverse images and preserve their disjointness.
  intro i hi j hj hij
  simp only [Function.onFun, OpenPartialHomeomorph.transHomeomorph_target]
  exact (charts.pairwiseDisjoint_target hi hj hij).preimage e.symm

/-- Helper for Theorem 78.3: transport a family of hole charts through a
homeomorphism of the ambient surface. -/
def mapHomeomorph
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    {k : ℕ} (charts : HoleCharts X k) (e : X ≃ₜ Z) : HoleCharts Z k :=
  ⟨fun i ↦ (charts i).transHomeomorph e, charts.source_eq,
    pairwiseDisjoint_target_mapHomeomorph charts e⟩

/-- Helper for Theorem 78.3: the disks removed after transporting hole charts
are exactly the image of the originally removed disks. -/
theorem removedDisks_mapHomeomorph
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    {k : ℕ} (charts : HoleCharts X k) (e : X ≃ₜ Z) :
    removedDisks (charts.mapHomeomorph e) = e '' removedDisks charts := by
  -- Compare membership by exposing the chosen chart and the point in its small disk.
  ext z
  simp only [Surface.mem_removedDisks, Set.mem_image]
  constructor
  · rintro ⟨i, x, hx, hxz⟩
    refine ⟨charts i x, ⟨i, x, hx, rfl⟩, ?_⟩
    exact hxz
  · rintro ⟨x, ⟨i, y, hy, hyx⟩, hxz⟩
    refine ⟨i, y, hy, ?_⟩
    exact (congrArg e hyx).trans hxz

/-- Helper for Theorem 78.3: avoiding the removed disks is preserved when the
ambient surface and its hole charts are transported by a homeomorphism. -/
theorem not_mem_removedDisks_mapHomeomorph
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    {k : ℕ} (charts : HoleCharts X k) (e : X ≃ₜ Z) (x : X) :
    x ∉ removedDisks charts ↔
      e x ∉ removedDisks (charts.mapHomeomorph e) := by
  -- Use the image formula and cancel the ambient equivalence at the chosen point.
  rw [removedDisks_mapHomeomorph]
  constructor
  · intro hx he
    obtain ⟨y, hy, hyx⟩ := he
    have hxy : y = x := e.injective hyx
    rw [hxy] at hy
    exact hx hy
  · intro he hx
    exact he ⟨x, hx, rfl⟩

end Surface.HoleCharts

namespace Surface

/-- Helper for Theorem 78.3: an `X`-with-`k`-holes remains such after replacing
the ambient surface by a homeomorphic one. -/
theorem isWithHoles_mapHomeomorph
    {Y : Type u} {X : Type v} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace Z]
    {k : ℕ} (e : X ≃ₜ Z) : IsWithHoles Y X k → IsWithHoles Y Z k := by
  intro h
  obtain ⟨charts, ⟨hY⟩⟩ := (isWithHoles_iff Y X k).mp h
  -- Restrict the ambient homeomorphism to the two complements, then compose witnesses.
  have hcomplement :
      withHoles charts ≃ₜ withHoles (charts.mapHomeomorph e) :=
    e.subtype (fun x ↦ charts.not_mem_removedDisks_mapHomeomorph e x)
  have hresult : Nonempty (Y ≃ₜ withHoles (charts.mapHomeomorph e)) :=
    ⟨hY.trans hcomplement⟩
  exact (isWithHoles_iff Y Z k).mpr ⟨charts.mapHomeomorph e, hresult⟩

/-- Helper for Theorem 78.3: `IsWithHoles Y X k` depends only on the
homeomorphism type of the ambient surface `X`. -/
theorem isWithHoles_congr_right
    {Y : Type u} {X : Type v} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace Z]
    {k : ℕ} (e : X ≃ₜ Z) :
    IsWithHoles Y X k ↔ IsWithHoles Y Z k := by
  -- Transport forward with `e` and backward with its inverse.
  constructor
  · exact isWithHoles_mapHomeomorph e
  · exact isWithHoles_mapHomeomorph e.symm

end Surface

namespace Topology

/-- Helper for Theorem 78.3: the image of a continuous injective planar patch
in a topological surface with boundary contains an ambient neighborhood of each
of its points. -/
private theorem exists_openNeighborhood_subset_range_of_planarEmbedding
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (EuclideanHalfSpace 2) Y] [IsManifold (𝓡∂ 2) 0 Y]
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (f : U → Y) (hfContinuous : Continuous f)
    (hfInjective : Function.Injective f) (p : U) :
    ∃ V : Set Y, IsOpen V ∧ f p ∈ V ∧ V ⊆ Set.range f := by
  let chart : OpenPartialHomeomorph Y (EuclideanHalfSpace 2) :=
    chartAt (EuclideanHalfSpace 2) (f p)
  have hfpSource : f p ∈ chart.source := by
    exact mem_chart_source (EuclideanHalfSpace 2) (f p)
  let domain : Set U := f ⁻¹' chart.source
  have hdomainOpen : IsOpen domain := by
    exact chart.open_source.preimage hfContinuous
  let inclusion : domain → EuclideanSpace ℝ (Fin 2) :=
    (Subtype.val : U → EuclideanSpace ℝ (Fin 2)) ∘
      (Subtype.val : domain → U)
  have hInclusionOpen : IsOpenEmbedding inclusion := by
    -- The restricted inclusion is open because both the planar domain and the
    -- chart-source preimage are open.
    dsimp only [inclusion]
    exact hU.isOpenEmbedding_subtypeVal.comp
      hdomainOpen.isOpenEmbedding_subtypeVal
  let domainEquiv : domain ≃ₜ Set.range inclusion :=
    hInclusionOpen.isEmbedding.toHomeomorph
  let coordinateMap : domain → EuclideanHalfSpace 2 :=
    fun q ↦ chart (f q.1)
  have hCoordinateContinuous : Continuous coordinateMap := by
    -- Restrict the surface chart to points whose images lie in its source.
    exact chart.continuousOn.comp_continuous
      (hfContinuous.comp continuous_subtype_val) (fun q ↦ q.2)
  let planarMap : Set.range inclusion → EuclideanSpace ℝ (Fin 2) :=
    fun q ↦ (𝓡∂ 2) (coordinateMap (domainEquiv.symm q))
  have hPlanarContinuous : Continuous planarMap := by
    exact (𝓡∂ 2).continuous.comp
      (hCoordinateContinuous.comp domainEquiv.symm.continuous)
  have hPlanarInjective : Function.Injective planarMap := by
    intro q r hqr
    apply domainEquiv.symm.injective
    apply Subtype.ext
    apply hfInjective
    apply chart.injOn
      (domainEquiv.symm q).2 (domainEquiv.symm r).2
    apply EuclideanHalfSpace.ext
    exact hqr
  have hPlanarRangeOpen : IsOpen (Set.range planarMap) :=
    (invarianceOfDomainPlane hInclusionOpen.isOpen_range planarMap
      hPlanarContinuous hPlanarInjective).isOpen_range
  let chartSubset : Set (EuclideanHalfSpace 2) :=
    (𝓡∂ 2) ⁻¹' Set.range planarMap
  have hChartSubsetOpen : IsOpen chartSubset := by
    exact hPlanarRangeOpen.preimage (𝓡∂ 2).continuous
  have hChartSubsetTarget : chartSubset ⊆ chart.target := by
    intro a ha
    obtain ⟨q, hq⟩ := ha
    let d : domain := domainEquiv.symm q
    have haCoordinate : a = coordinateMap d := by
      apply EuclideanHalfSpace.ext
      exact hq.symm
    -- Every point of the planar image comes from the chosen chart source.
    rw [haCoordinate]
    exact chart.map_source d.2
  have hImageOpen : IsOpen (chart.symm '' chartSubset) :=
    chart.isOpen_image_symm_of_subset_target hChartSubsetOpen hChartSubsetTarget
  refine ⟨chart.symm '' chartSubset, hImageOpen, ?_, ?_⟩
  · let pDomain : domain := ⟨p, hfpSource⟩
    let pRange : Set.range inclusion := domainEquiv pDomain
    have hpChartSubset : chart (f p) ∈ chartSubset := by
      refine ⟨pRange, ?_⟩
      dsimp only [planarMap, pRange]
      rw [domainEquiv.symm_apply_apply]
    exact ⟨chart (f p), hpChartSubset, chart.left_inv hfpSource⟩
  · rintro y ⟨a, ha, rfl⟩
    obtain ⟨q, hq⟩ := ha
    let d : domain := domainEquiv.symm q
    have haCoordinate : a = coordinateMap d := by
      apply EuclideanHalfSpace.ext
      exact hq.symm
    refine ⟨d.1, ?_⟩
    rw [haCoordinate]
    exact (chart.left_inv d.2).symm

end Topology

/-- Helper for Theorem 78.3: a vertex of a curved triangle lies on exactly the
two edges whose opposite-vertex index is different from its own. -/
private theorem CurvedTriangle.vertex_mem_edge_iff
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (vertexIndex edgeIndex : Fin 3) :
    triangle.vertex vertexIndex ∈ triangle.edge edgeIndex ↔
      vertexIndex ≠ edgeIndex := by
  -- Pull edge membership back through the triangle chart to the corresponding
  -- closed face of the affine model.
  rw [triangle.edge_eq_chart_image_modelEdge edgeIndex]
  constructor
  · rintro ⟨point, hpoint, hvertex⟩
    have hmodelPoint :
        triangle.model.points vertexIndex =
          (point : EuclideanSpace ℝ (Fin 2)) := by
      unfold CurvedTriangle.vertex at hvertex
      have hpointEq :
          point =
            ⟨triangle.model.points vertexIndex,
              triangle.model.point_mem_closedInterior vertexIndex⟩ :=
        triangle.chart.injective (Subtype.ext hvertex)
      exact (congrArg Subtype.val hpointEq).symm
    rw [triangle.modelEdge_def edgeIndex] at hpoint
    change (point : EuclideanSpace ℝ (Fin 2)) ∈
      (triangle.model.faceOpposite edgeIndex).closedInterior at hpoint
    rw [← hmodelPoint] at hpoint
    exact triangle.model.point_mem_closedInterior_faceOpposite_iff.mp hpoint
  · intro hne
    let point : triangle.model.closedInterior :=
      ⟨triangle.model.points vertexIndex,
        triangle.model.point_mem_closedInterior vertexIndex⟩
    refine ⟨point, ?_, ?_⟩
    · rw [triangle.modelEdge_def edgeIndex]
      exact triangle.model.point_mem_closedInterior_faceOpposite_iff.mpr hne
    · rfl

/-- Helper for Theorem 78.3: the relative interior of a curved edge is the
vertex-free chart image of the interior of its model face. -/
private def CurvedTriangle.openEdge
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) : Set X :=
  ((fun y : triangle.model.closedInterior ↦ (triangle.chart y : X)) ''
      (Subtype.val ⁻¹' (triangle.model.faceOpposite i).interior)) \
    Set.range triangle.vertex

/-- Helper for Theorem 78.3: every relative open edge lies in its corresponding
closed curved edge. -/
private theorem CurvedTriangle.openEdge_subset_edge
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) : triangle.openEdge i ⊆ triangle.edge i := by
  -- Route correction: use the model-face interior directly because the imported
  -- curved-triangle API does not expose a computation rule for `vertex`.
  rw [CurvedTriangle.openEdge, triangle.edge_eq_chart_image_modelEdge i]
  rintro x ⟨⟨y, hyInterior, rfl⟩, _⟩
  refine ⟨y, ?_, rfl⟩
  rw [triangle.modelEdge_def i]
  exact (triangle.model.faceOpposite i).interior_subset_closedInterior hyInterior

/-- Helper for Theorem 78.3: a point of a curved edge that is not a vertex of
the triangle belongs to the relative open edge. -/
private theorem CurvedTriangle.mem_openEdge_of_mem_edge_of_ne_vertex
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) {x : X} (hx : x ∈ triangle.edge i)
    (hxVertex : ∀ k : Fin 3, x ≠ triangle.vertex k) :
    x ∈ triangle.openEdge i := by
  rw [triangle.edge_eq_chart_image_modelEdge i] at hx
  obtain ⟨y, hyEdge, hyx⟩ := hx
  have hyNeEndpoint (j : Fin 2) :
      (y : EuclideanSpace ℝ (Fin 2)) ≠
        (triangle.model.faceOpposite i).points j := by
    intro hyj
    let k : Fin 3 := Fin.succAbove i j
    have hfacePoint :
        (triangle.model.faceOpposite i).points j = triangle.model.points k := by
      rw [triangle.model.faceOpposite_point_eq_point_succAbove]
      norm_num [k]
    have hyVertex : x = triangle.vertex k := by
      calc
        x = (triangle.chart y : X) := hyx.symm
        _ = (triangle.chart
              ⟨triangle.model.points k,
                triangle.model.point_mem_closedInterior k⟩ : X) := by
          apply congrArg (fun z : triangle.model.closedInterior ↦
            (triangle.chart z : X))
          apply Subtype.ext
          exact hyj.trans hfacePoint
        _ = triangle.vertex k := rfl
    exact hxVertex k hyVertex
  have hyInterior :
      (y : EuclideanSpace ℝ (Fin 2)) ∈
        (triangle.model.faceOpposite i).interior := by
    rw [triangle.modelEdge_def i] at hyEdge
    rw [Affine.Simplex.mem_interior_iff_sbtw]
    exact ⟨Affine.Simplex.mem_closedInterior_iff_wbtw.mp hyEdge,
      hyNeEndpoint 0, hyNeEndpoint 1⟩
  -- The interior witness gives image membership, while the hypothesis excludes
  -- precisely the vertex range removed in the definition of `openEdge`.
  refine ⟨⟨y, hyInterior, hyx⟩, ?_⟩
  rintro ⟨k, hk⟩
  exact hxVertex k hk.symm

/-- Helper for Theorem 78.3: a relative open-edge point cannot have an ambient
neighborhood inside one triangle when a Euclidean chart passes through it. -/
private theorem CurvedTriangle.not_exists_openNeighborhood_subset_carrier_of_mem_openEdge_of_chart
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) {x : X} (hx : x ∈ triangle.openEdge i)
    (surfaceChart : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 2)))
    (hxSource : x ∈ surfaceChart.source) :
    ¬ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ triangle.carrier := by
  rintro ⟨U, hUOpen, hxU, hUCarrier⟩
  obtain ⟨y, hyFaceInterior, hyChart⟩ := hx.1
  let W : Set X := surfaceChart.source ∩ U
  have hWOpen : IsOpen W := surfaceChart.open_source.inter hUOpen
  have hWSource : W ⊆ surfaceChart.source := Set.inter_subset_left
  have hxW : x ∈ W := ⟨hxSource, hxU⟩
  let D : Set (EuclideanSpace ℝ (Fin 2)) := surfaceChart '' W
  have hDOpen : IsOpen D :=
    surfaceChart.isOpen_image_of_subset_source hWOpen hWSource
  have hDTarget : D ⊆ surfaceChart.target := by
    rintro z ⟨q, hq, rfl⟩
    exact surfaceChart.map_source hq.1
  have hSymmMemW (z : D) : surfaceChart.symm z.1 ∈ W := by
    obtain ⟨q, hq, hqz⟩ := z.2
    have hsymm : surfaceChart.symm z.1 = q := by
      rw [← hqz, surfaceChart.left_inv hq.1]
    rwa [hsymm]
  have hSymmMemCarrier (z : D) :
      surfaceChart.symm z.1 ∈ triangle.carrier :=
    hUCarrier (hSymmMemW z).2
  let toCarrier : D → triangle.carrier :=
    fun z ↦ ⟨surfaceChart.symm z.1, hSymmMemCarrier z⟩
  have hSymmContinuous :
      Continuous (fun z : D ↦ surfaceChart.symm z.1) := by
    exact surfaceChart.continuousOn_symm.comp_continuous continuous_subtype_val
      (fun z ↦ hDTarget z.2)
  have hToCarrierContinuous : Continuous toCarrier := by
    exact hSymmContinuous.subtype_mk hSymmMemCarrier
  let f : D → EuclideanSpace ℝ (Fin 2) :=
    fun z ↦ (triangle.chart.symm (toCarrier z) : EuclideanSpace ℝ (Fin 2))
  have hfContinuous : Continuous f := by
    exact continuous_subtype_val.comp
      (triangle.chart.symm.continuous.comp hToCarrierContinuous)
  have hfInjective : Function.Injective f := by
    intro z w hzw
    have hclosed : triangle.chart.symm (toCarrier z) =
        triangle.chart.symm (toCarrier w) := Subtype.ext hzw
    have hcarrier : toCarrier z = toCarrier w := by
      calc
        toCarrier z = triangle.chart (triangle.chart.symm (toCarrier z)) :=
          (triangle.chart.apply_symm_apply (toCarrier z)).symm
        _ = triangle.chart (triangle.chart.symm (toCarrier w)) :=
          congrArg triangle.chart hclosed
        _ = toCarrier w := triangle.chart.apply_symm_apply (toCarrier w)
    have hambient : surfaceChart.symm z.1 = surfaceChart.symm w.1 :=
      congrArg Subtype.val hcarrier
    apply Subtype.ext
    exact surfaceChart.symm.injOn (hDTarget z.2) (hDTarget w.2) hambient
  have hRangeOpen : IsOpen (Set.range f) :=
    (invarianceOfDomainPlane hDOpen f hfContinuous hfInjective).isOpen_range
  have hRangeSubset : Set.range f ⊆ triangle.model.closedInterior := by
    rintro _ ⟨z, rfl⟩
    exact (triangle.chart.symm (toCarrier z)).property
  let p : D := ⟨surfaceChart x, ⟨x, hxW, rfl⟩⟩
  have hToCarrierP : toCarrier p = ⟨x, hUCarrier hxU⟩ := by
    apply Subtype.ext
    exact surfaceChart.left_inv hxSource
  have hToCarrierChart : toCarrier p = triangle.chart y := by
    apply Subtype.ext
    exact (congrArg Subtype.val hToCarrierP).trans hyChart.symm
  have hfp : f p = (y : EuclideanSpace ℝ (Fin 2)) := by
    unfold f
    rw [hToCarrierChart, triangle.chart.symm_apply_apply]
  have hfpTopologicalInterior : f p ∈ interior triangle.model.closedInterior :=
    interior_maximal hRangeSubset hRangeOpen (Set.mem_range_self p)
  have hspan : affineSpan ℝ (Set.range triangle.model.points) = ⊤ :=
    triangle.model.span_eq_top (by simp)
  have hySimplexInterior :
      (y : EuclideanSpace ℝ (Fin 2)) ∈ triangle.model.interior := by
    rw [triangle.model.interior_eq_topologicalInterior_closedInterior hspan]
    rwa [hfp] at hfpTopologicalInterior
  -- The chart would put the edge point in both the simplex interior and its face.
  exact Set.disjoint_left.mp
    (triangle.model.disjoint_interior_closedInterior_faceOpposite i)
      hySimplexInterior
      ((triangle.model.faceOpposite i).interior_subset_closedInterior
        hyFaceInterior)

/-- Helper for Theorem 78.3: a point in the relative interior of an opposite
face is distinct from every vertex of the ambient triangle. -/
private theorem Affine.Simplex.faceOpposite_interior_ne_point
    {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (simplex : Affine.Simplex ℝ P 2) (i : Fin 3) {p : P}
    (hp : p ∈ (simplex.faceOpposite i).interior) (k : Fin 3) :
    p ≠ simplex.points k := by
  -- Separate the opposite vertex by the face span and the remaining vertices
  -- by the fact that endpoints do not lie in a one-simplex interior.
  intro hpk
  by_cases hki : k = i
  · subst k
    have hpSpan : p ∈ affineSpan ℝ (Set.range (simplex.faceOpposite i).points) :=
      (simplex.faceOpposite i).closedInterior_subset_affineSpan
        ((simplex.faceOpposite i).interior_subset_closedInterior hp)
    exact simplex.points_notMem_affineSpan_faceOpposite i (hpk ▸ hpSpan)
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hki
    have hpoint : (simplex.faceOpposite i).points j = simplex.points k := by
      rw [simplex.faceOpposite_point_eq_point_succAbove]
      norm_num
      exact congrArg simplex.points hj
    have hpEndpoint : simplex.points k ∈ (simplex.faceOpposite i).interior := by
      rwa [← hpk]
    rw [← hpoint] at hpEndpoint
    exact (simplex.faceOpposite i).point_notMem_interior j hpEndpoint

/-- Helper for Theorem 78.3: every strict affine edge parameter maps into the
relative open edge. -/
private theorem CurvedTriangle.modelEdgePoint_mem_openEdge_of_mem_Ioo
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) (t : unitInterval) (ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    (triangle.chart (triangle.modelEdgePoint i t) : X) ∈ triangle.openEdge i := by
  have hInterior :
      (triangle.modelEdgePoint i t : EuclideanSpace ℝ (Fin 2)) ∈
        (triangle.model.faceOpposite i).interior :=
    (triangle.modelEdgePoint_mem_faceOpposite_interior_iff i t).mpr ht
  refine ⟨⟨triangle.modelEdgePoint i t, hInterior, rfl⟩, ?_⟩
  -- Injectivity of the triangle chart reduces exclusion of vertices to the
  -- corresponding affine-simplex fact.
  rintro ⟨k, hk⟩
  have hchart :
      triangle.chart (triangle.modelEdgePoint i t) =
        triangle.chart
          ⟨triangle.model.points k, triangle.model.point_mem_closedInterior k⟩ := by
    apply Subtype.ext
    unfold CurvedTriangle.vertex at hk
    exact hk.symm
  have hmodel := congrArg Subtype.val (triangle.chart.injective hchart)
  exact triangle.model.faceOpposite_interior_ne_point i hInterior k hmodel

/-- Helper for Theorem 78.3: a closed curved edge is contained in the closure
of its relative open edge. -/
private theorem CurvedTriangle.edge_subset_closure_openEdge
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) : triangle.edge i ⊆ closure (triangle.openEdge i) := by
  let strictParameters : Set unitInterval :=
    Subtype.val ⁻¹' Set.Ioo (0 : ℝ) 1
  have hcoeStrict :
      ((↑) : unitInterval → ℝ) '' strictParameters = Set.Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro ht
      exact ⟨⟨t, ⟨ht.1.le, ht.2.le⟩⟩, ht, rfl⟩
  have hstrictDense : Dense strictParameters := by
    -- The strict interval is dense in the closed unit interval.
    rw [Subtype.dense_iff, hcoeStrict, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hstrictMaps : Set.MapsTo
      (fun t : unitInterval ↦
        (triangle.chart (triangle.modelEdgePoint i t) : X))
      strictParameters (triangle.openEdge i) := by
    intro t ht
    exact triangle.modelEdgePoint_mem_openEdge_of_mem_Ioo i t ht
  -- Every closed-edge parameter is a limit of strict parameters, and
  -- continuity transports that convergence into the ambient space.
  intro x hx
  obtain ⟨t, htx⟩ := hx
  rw [← htx]
  exact map_mem_closure
    (f := fun t : unitInterval ↦
      (triangle.chart (triangle.modelEdgePoint i t) : X))
    (continuous_subtype_val.comp
      (triangle.chart.continuous.comp (triangle.continuous_modelEdgePoint i)))
    (hstrictDense t) hstrictMaps

/-- Helper for Theorem 78.3: interiors of distinct opposite faces of a real
triangle are disjoint from the other closed face. -/
private theorem Affine.Simplex.disjoint_interior_faceOpposite_closedInterior_faceOpposite_of_ne
    {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (simplex : Affine.Simplex ℝ P 2) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (simplex.faceOpposite i).interior
      (simplex.faceOpposite j).closedInterior := by
  rw [Set.disjoint_left]
  intro p hpInterior hpClosed
  have hpSpan : p ∈ affineSpan ℝ (Set.range simplex.points) :=
    simplex.affineSpan_faceOpposite_le i
      ((simplex.faceOpposite i).closedInterior_subset_affineSpan
        ((simplex.faceOpposite i).interior_subset_closedInterior hpInterior))
  obtain ⟨weights, hsum, hp⟩ :=
    eq_affineCombination_of_mem_affineSpan_of_fintype hpSpan
  rw [hp] at hpInterior hpClosed
  have hjzero : weights j = 0 :=
    (simplex.affineCombination_mem_affineSpan_faceOpposite_iff hsum).mp
      ((simplex.faceOpposite j).closedInterior_subset_affineSpan hpClosed)
  -- On the interior of the face opposite `i`, every remaining barycentric
  -- coordinate, in particular the distinct coordinate `j`, is positive.
  unfold Affine.Simplex.faceOpposite at hpInterior
  have hpositive :=
    (simplex.affineCombination_mem_interior_face_iff_pos _ hsum).mp hpInterior
  have hjmem : j ∈ ({i}ᶜ : Finset (Fin 3)) := by
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact hij.symm
  exact (ne_of_gt (hpositive.1 j hjmem)) hjzero

/-- Helper for Theorem 78.3: the relative interior of one curved edge is
disjoint from every distinct closed edge of the same triangle. -/
private theorem CurvedTriangle.disjoint_openEdge_edge_of_ne
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (triangle.openEdge i) (triangle.edge j) := by
  rw [Set.disjoint_left]
  intro x hxOpen hxEdge
  obtain ⟨⟨y, hyInterior, hyx⟩, _⟩ := hxOpen
  rw [triangle.edge_eq_chart_image_modelEdge j] at hxEdge
  obtain ⟨z, hzClosed, hzx⟩ := hxEdge
  have hyz : y = z := by
    apply triangle.chart.injective
    apply Subtype.ext
    exact hyx.trans hzx.symm
  rw [triangle.modelEdge_def j] at hzClosed
  rw [hyz] at hyInterior
  exact Set.disjoint_left.mp
    (triangle.model.disjoint_interior_faceOpposite_closedInterior_faceOpposite_of_ne hij)
      hyInterior hzClosed

/-- Helper for Theorem 78.3: the open cell of a curved triangle is dense in
its carrier, viewed in the ambient Hausdorff space. -/
private theorem CurvedTriangle.carrier_subset_closure_openCell
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (triangle : CurvedTriangle X) :
    triangle.carrier ⊆ closure triangle.openCell := by
  have hspan :
      affineSpan ℝ (Set.range triangle.model.points) = ⊤ :=
    triangle.model.span_eq_top (by simp)
  have hconvex : Convex ℝ triangle.model.closedInterior := by
    rw [← triangle.model.convexHull_eq_closedInterior]
    exact convex_convexHull ℝ (Set.range triangle.model.points)
  have hclosedSpan : affineSpan ℝ triangle.model.closedInterior = ⊤ := by
    rw [← triangle.model.convexHull_eq_closedInterior, affineSpan_convexHull]
    exact hspan
  have hnonemptyInterior :
      (interior triangle.model.closedInterior).Nonempty :=
    (hconvex.interior_nonempty_iff_affineSpan_eq_top).mpr hclosedSpan
  have hinterior :
      triangle.model.interior = interior triangle.model.closedInterior :=
    triangle.model.interior_eq_topologicalInterior_closedInterior hspan
  have hmodelClosure :
      closure triangle.model.interior = triangle.model.closedInterior := by
    rw [hinterior,
      hconvex.closure_interior_eq_closure_of_nonempty_interior hnonemptyInterior,
      triangle.model.isClosed_closedInterior.closure_eq]
  let modelOpen : Set triangle.model.closedInterior :=
    Subtype.val ⁻¹' triangle.model.interior
  have hcoeModelOpen :
      ((↑) : triangle.model.closedInterior → EuclideanSpace ℝ (Fin 2)) ''
          modelOpen = triangle.model.interior := by
    -- The algebraic interior already lies in the closed model triangle.
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, triangle.model.interior_subset_closedInterior hy⟩, hy, rfl⟩
  have hmodelDense : Dense modelOpen := by
    -- Ambient density restricts to density in the closed-triangle subtype.
    rw [Subtype.dense_iff, hcoeModelOpen, hmodelClosure]
  have hcarrierDense :
      Dense (triangle.chart '' modelOpen) :=
    triangle.chart.surjective.denseRange.dense_image
      triangle.chart.continuous hmodelDense
  have hopenCellDense :
      Dense (Subtype.val ⁻¹' triangle.openCell : Set triangle.carrier) := by
    -- The triangle chart identifies the dense model interior with the open cell.
    rw [triangle.preimage_openCell_eq_chart_image_modelInterior]
    exact hcarrierDense
  have hcoeOpenCell :
      ((↑) : triangle.carrier → X) ''
          (Subtype.val ⁻¹' triangle.openCell : Set triangle.carrier) =
        triangle.openCell := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, triangle.openCell_subset_carrier hx⟩, hx, rfl⟩
  -- Translate subtype density back to the ambient closure statement.
  rw [Subtype.dense_iff, hcoeOpenCell] at hopenCellDense
  exact hopenCellDense

/-- Helper for Theorem 78.3: the boundary of a topological surface with boundary
is closed, including at differentiability order zero. -/
private theorem Surface.isClosed_boundary_of_topologicalManifold
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] : IsClosed (∂Y : Set Y) := by
  -- The complement consists exactly of points lying in some Euclidean chart source.
  rw [← isOpen_compl_iff]
  have hcomplement :
      (∂Y : Set Y)ᶜ =
        ⋃ e : OpenPartialHomeomorph Y (EuclideanSpace ℝ (Fin 2)), e.source := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    rw [mem_surfaceBoundary_iff_noEuclideanChart]
    simp only [not_not]
  -- Arbitrary unions of the open chart sources are open.
  rw [hcomplement]
  exact isOpen_iUnion fun e ↦ e.open_source

namespace Surface.boundary

/-- Helper for Theorem 78.3: no point of the boundary one-manifold of a
topological surface is isolated. -/
private theorem not_isOpen_singleton_of_surfaceBoundary
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (x : ∂Y) : ¬ IsOpen ({x} : Set (∂Y)) := by
  let boundaryChart := chartAt (EuclideanSpace ℝ (Fin 1)) x
  have hxSource : x ∈ boundaryChart.source :=
    mem_chart_source (EuclideanSpace ℝ (Fin 1)) x
  have hsingletonSource : ({x} : Set (∂Y)) ⊆ boundaryChart.source := by
    simpa only [Set.singleton_subset_iff]
  intro hsingletonOpen
  have himageOpen : IsOpen (boundaryChart '' ({x} : Set (∂Y))) :=
    boundaryChart.isOpen_image_of_subset_source hsingletonOpen hsingletonSource
  rw [Set.image_singleton] at himageOpen
  exact not_isOpen_singleton (boundaryChart x) himageOpen

/-- Helper for Theorem 78.3: the boundary one-manifold of a topological
surface is a perfect space. -/
private instance instPerfectSpaceSurfaceBoundary
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y] :
    PerfectSpace (∂Y) := by
  rw [perfectSpace_iff_forall_not_isolated]
  intro x
  rw [Filter.neBot_iff]
  intro hbot
  exact not_isOpen_singleton_of_surfaceBoundary x
    ((isOpen_singleton_iff_punctured_nhds x).mpr hbot)

end Surface.boundary

namespace Triangulation

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]

/-- Helper for Theorem 78.3: the triangles incident to an edge occurrence are
exactly those whose carriers contain the whole selected edge. -/
private def incidentTriangles (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) : Set (Fin triangulation.card) :=
  {r | (triangulation.triangle i).edge j ⊆
    (triangulation.triangle r).carrier}

omit [ChartedSpace (EuclideanHalfSpace 2) Y] in
/-- Helper for Theorem 78.3: the incident triangles of an edge occurrence form
a finite set. -/
private theorem incidentTriangles_finite (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) :
    (triangulation.incidentTriangles i j).Finite := by
  -- The incident set is contained in the finite triangulation index type.
  exact Set.toFinite _

omit [ChartedSpace (EuclideanHalfSpace 2) Y] in
/-- Helper for Theorem 78.3: the triangle containing an edge occurrence is
itself incident to that edge. -/
private theorem self_mem_incidentTriangles (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) :
    i ∈ triangulation.incidentTriangles i j := by
  -- The selected closed edge lies in the carrier of its owning triangle.
  exact (triangulation.triangle i).edge_subset j

omit [ChartedSpace (EuclideanHalfSpace 2) Y] in
/-- Helper for Theorem 78.3: every edge occurrence has positive
incident-triangle rank. -/
private theorem incidentTriangles_ncard_pos (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) :
    0 < (triangulation.incidentTriangles i j).ncard := by
  -- Finiteness turns the owning triangle witness into strict positivity of `ncard`.
  rw [Set.ncard_pos (triangulation.incidentTriangles_finite i j)]
  exact ⟨i, triangulation.self_mem_incidentTriangles i j⟩

omit [ChartedSpace (EuclideanHalfSpace 2) Y] in
/-- Helper for Theorem 78.3: at a point in an open edge, carrier membership is
equivalent to membership in the edge's fixed incident-triangle set. -/
private theorem mem_carrier_iff_mem_incidentTriangles_of_mem_openEdge
    (triangulation : Triangulation Y) (i : Fin triangulation.card) (j : Fin 3)
    (x : Y) (hx : x ∈ (triangulation.triangle i).openEdge j)
    (r : Fin triangulation.card) :
    x ∈ (triangulation.triangle r).carrier ↔
      r ∈ triangulation.incidentTriangles i j := by
  constructor
  · intro hxr
    change (triangulation.triangle i).edge j ⊆
      (triangulation.triangle r).carrier
    by_cases hir : i = r
    · subst r
      exact (triangulation.triangle i).edge_subset j
    have hxEdge : x ∈ (triangulation.triangle i).edge j :=
      (triangulation.triangle i).openEdge_subset_edge j hx
    have hxi : x ∈ (triangulation.triangle i).carrier :=
      (triangulation.triangle i).edge_subset j hxEdge
    have hxIntersection : x ∈ (triangulation.triangle i).carrier ∩
        (triangulation.triangle r).carrier := ⟨hxi, hxr⟩
    rcases triangulation.intersection_spec i r hir with
      hdisjoint | hvertex | hsharedEdge
    · exact False.elim (Set.disjoint_left.mp hdisjoint hxi hxr)
    · obtain ⟨vertexI, _, hintersection, _⟩ :=
        (CurvedTriangle.sharesVertex_iff _ _).mp hvertex
      rw [hintersection] at hxIntersection
      have hxvertex : x = (triangulation.triangle i).vertex vertexI :=
        Set.mem_singleton_iff.mp hxIntersection
      -- The explicit vertex-free clause in `openEdge` rules out this intersection.
      exact False.elim (hx.2 ⟨vertexI, hxvertex.symm⟩)
    · obtain ⟨edgeI, _, hintersection, _⟩ :=
        (CurvedTriangle.sharesEdge_iff _ _).mp hsharedEdge
      have hxSharedEdge : x ∈ (triangulation.triangle i).edge edgeI := by
        rw [← hintersection]
        exact hxIntersection
      have hedge : edgeI = j := by
        by_contra hne
        exact Set.disjoint_left.mp
          ((triangulation.triangle i).disjoint_openEdge_edge_of_ne (Ne.symm hne))
            hx hxSharedEdge
      subst edgeI
      -- The common-intersection equation now puts the whole selected edge in
      -- the carrier of the other incident triangle.
      intro y hy
      have hyIntersection : y ∈ (triangulation.triangle i).carrier ∩
          (triangulation.triangle r).carrier := by
        rw [hintersection]
        exact hy
      exact hyIntersection.2
  · intro hr
    change (triangulation.triangle i).edge j ⊆
      (triangulation.triangle r).carrier at hr
    -- An open-edge point lies on the closed edge, so incidence applies directly.
    exact hr ((triangulation.triangle i).openEdge_subset_edge j hx)

omit [ChartedSpace (EuclideanHalfSpace 2) Y] in
/-- Helper for Theorem 78.3: a distinct triangle incident to an open-edge
occurrence meets its owner in exactly that edge, with compatible affine edge
parameters. -/
private theorem exists_compatibleSharedEdge_of_mem_incidentTriangles
    (triangulation : Triangulation Y) (i : Fin triangulation.card) (j : Fin 3)
    (x : Y) (hx : x ∈ (triangulation.triangle i).openEdge j)
    (r : Fin triangulation.card) (hir : i ≠ r)
    (hr : r ∈ triangulation.incidentTriangles i j) :
    ∃ edgeR : Fin 3,
      (triangulation.triangle i).carrier ∩
          (triangulation.triangle r).carrier =
        (triangulation.triangle i).edge j ∧
      (triangulation.triangle i).carrier ∩
          (triangulation.triangle r).carrier =
        (triangulation.triangle r).edge edgeR ∧
      (triangulation.triangle i).EdgesCompatible
        (triangulation.triangle r) j edgeR := by
  have hxEdge : x ∈ (triangulation.triangle i).edge j :=
    (triangulation.triangle i).openEdge_subset_edge j hx
  have hxi : x ∈ (triangulation.triangle i).carrier :=
    (triangulation.triangle i).edge_subset j hxEdge
  have hxr : x ∈ (triangulation.triangle r).carrier :=
    (triangulation.mem_carrier_iff_mem_incidentTriangles_of_mem_openEdge
      i j x hx r).mpr hr
  have hxIntersection : x ∈ (triangulation.triangle i).carrier ∩
      (triangulation.triangle r).carrier := ⟨hxi, hxr⟩
  -- The common open-edge point excludes disjoint and vertex-only intersections.
  rcases triangulation.intersection_spec i r hir with
    hdisjoint | hvertex | hsharedEdge
  · exact False.elim (Set.disjoint_left.mp hdisjoint hxi hxr)
  · obtain ⟨vertexI, _, hintersection, _⟩ :=
      (CurvedTriangle.sharesVertex_iff _ _).mp hvertex
    rw [hintersection] at hxIntersection
    have hxvertex : x = (triangulation.triangle i).vertex vertexI :=
      Set.mem_singleton_iff.mp hxIntersection
    exact False.elim (hx.2 ⟨vertexI, hxvertex.symm⟩)
  · obtain ⟨edgeI, edgeR, hintersectionI, hedgeEq⟩ :=
      (CurvedTriangle.sharesEdge_iff _ _).mp hsharedEdge
    have hxSharedEdge : x ∈ (triangulation.triangle i).edge edgeI := by
      rw [← hintersectionI]
      exact hxIntersection
    have hedgeI : edgeI = j := by
      by_contra hne
      exact Set.disjoint_left.mp
        ((triangulation.triangle i).disjoint_openEdge_edge_of_ne (Ne.symm hne))
          hx hxSharedEdge
    subst edgeI
    have hintersectionR :
        (triangulation.triangle i).carrier ∩
            (triangulation.triangle r).carrier =
          (triangulation.triangle r).edge edgeR :=
      hintersectionI.trans hedgeEq
    refine ⟨edgeR, hintersectionI, hintersectionR, ?_⟩
    -- The triangulation stores compatibility for the two normalized edge indices.
    exact triangulation.sharedEdgeCompatible i r hir j edgeR
      hintersectionI hintersectionR

/-- Helper for Theorem 78.3: two distinct triangles incident to an open edge
produce an injective planar patch through the chosen edge point. -/
private theorem existsPlanarEmbeddingAt_of_distinct_mem_incidentTriangles
    (triangulation : Triangulation Y) (i : Fin triangulation.card) (j : Fin 3)
    (x : Y) (hx : x ∈ (triangulation.triangle i).openEdge j)
    (r : Fin triangulation.card) (hir : i ≠ r)
    (hr : r ∈ triangulation.incidentTriangles i j) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      ∃ p : U, ∃ f : U → Y,
        Continuous f ∧ Function.Injective f ∧ f p = x ∧
          Set.range f ⊆ (triangulation.triangle i).carrier ∪
            (triangulation.triangle r).carrier := by
  obtain ⟨edgeR, hintersectionI, hintersectionR, hcompatible⟩ :=
    triangulation.exists_compatibleSharedEdge_of_mem_incidentTriangles
      i j x hx r hir hr
  obtain ⟨y, hyInterior, hyx⟩ := hx.1
  have hyModelEdge :
      (y : EuclideanSpace ℝ (Fin 2)) ∈
        (triangulation.triangle i).modelEdge j := by
    rw [(triangulation.triangle i).modelEdge_def j]
    exact ((triangulation.triangle i).model.faceOpposite j)
      |>.interior_subset_closedInterior hyInterior
  obtain ⟨t, ht⟩ :=
    (Set.ext_iff.mp
      ((triangulation.triangle i).range_modelEdgePoint_val j) y).mpr hyModelEdge
  have htInterior :
      ((triangulation.triangle i).modelEdgePoint j t :
          EuclideanSpace ℝ (Fin 2)) ∈
        ((triangulation.triangle i).model.faceOpposite j).interior := by
    have ht' :
        ((triangulation.triangle i).modelEdgePoint j t :
          EuclideanSpace ℝ (Fin 2)) = (y : EuclideanSpace ℝ (Fin 2)) := ht
    rw [ht']
    exact hyInterior
  have htStrict : (t : ℝ) ∈ Set.Ioo 0 1 :=
    ((triangulation.triangle i)
      |>.modelEdgePoint_mem_faceOpposite_interior_iff j t).mp htInterior
  have hpoint :
      ((triangulation.triangle i).chart
        ((triangulation.triangle i).modelEdgePoint j t) : Y) = x := by
    -- The range witness `t` represents the original model point `y`.
    calc
      ((triangulation.triangle i).chart
          ((triangulation.triangle i).modelEdgePoint j t) : Y) =
          ((triangulation.triangle i).chart y : Y) := by
            apply congrArg (fun z :
              (triangulation.triangle i).model.closedInterior ↦
                ((triangulation.triangle i).chart z : Y))
            exact Subtype.ext ht
      _ = x := hyx
  obtain ⟨U, hUOpen, p, f, hfContinuous, hfInjective, hfp, hfrange⟩ :=
    (triangulation.triangle i)
      |>.existsPlanarEmbeddingAtOfCompatibleSharedEdge
        (triangulation.triangle r) j edgeR hintersectionI hintersectionR
        hcompatible t htStrict
  -- Retain the two-carrier range control for the incidence bound below.
  exact ⟨U, hUOpen, p, f, hfContinuous, hfInjective, hfp.trans hpoint, hfrange⟩

omit [ChartedSpace (EuclideanHalfSpace 2) Y] in
/-- Helper for Theorem 78.3: an open-edge point has an ambient open
neighborhood covered exactly by the carriers incident to that edge. -/
private theorem exists_openNeighborhood_eq_iUnion_incidentCarriers
    [T2Space Y] (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) (x : Y)
    (hx : x ∈ (triangulation.triangle i).openEdge j) :
    ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧
      U = ⋃ r : triangulation.incidentTriangles i j,
        U ∩ (triangulation.triangle r.1).carrier := by
  let excluded : Set Y :=
    ⋃ r : {r : Fin triangulation.card //
        r ∉ triangulation.incidentTriangles i j},
      (triangulation.triangle r.1).carrier
  have hExcludedClosed : IsClosed excluded := by
    dsimp only [excluded]
    exact isClosed_iUnion_of_finite fun r ↦
      (triangulation.triangle r.1).isClosed_carrier
  have hxExcluded : x ∉ excluded := by
    intro hxExcluded
    obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hxExcluded
    have hrIncident : r.1 ∈ triangulation.incidentTriangles i j :=
      (triangulation.mem_carrier_iff_mem_incidentTriangles_of_mem_openEdge
        i j x hx r.1).mp hxr
    exact r.2 hrIncident
  refine ⟨excludedᶜ, hExcludedClosed.isOpen_compl, hxExcluded, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    have hyCover : y ∈ ⋃ r, (triangulation.triangle r).carrier := by
      rw [triangulation.cover]
      exact Set.mem_univ y
    obtain ⟨r, hyr⟩ := Set.mem_iUnion.mp hyCover
    by_cases hr : r ∈ triangulation.incidentTriangles i j
    · exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hy, hyr⟩
    · exact False.elim (hy (Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hyr⟩))
  · intro y hy
    obtain ⟨r, hyU, _⟩ := Set.mem_iUnion.mp hy
    exact hyU

omit [ChartedSpace (EuclideanHalfSpace 2) Y] in
/-- Helper for Theorem 78.3: if an open-edge point has an ambient open
neighborhood covered by two triangle carriers, then at most two triangles are
incident to that edge. -/
private theorem incidentTriangles_ncard_le_two_of_pairNeighborhood
    [T2Space Y] (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) (x : Y)
    (hx : x ∈ (triangulation.triangle i).openEdge j)
    (first second : Fin triangulation.card) (U : Set Y)
    (hUOpen : IsOpen U) (hxU : x ∈ U)
    (hUCarrier : U ⊆
      (triangulation.triangle first).carrier ∪
        (triangulation.triangle second).carrier) :
    (triangulation.incidentTriangles i j).ncard ≤ 2 := by
  have hIncidentSubset :
      triangulation.incidentTriangles i j ⊆ ({first, second} : Set _) := by
    intro r hr
    by_contra hrPair
    have hrNe : r ≠ first ∧ r ≠ second := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hrPair
    have hxr : x ∈ (triangulation.triangle r).carrier :=
      (triangulation.mem_carrier_iff_mem_incidentTriangles_of_mem_openEdge
        i j x hx r).mpr hr
    have hxClosure : x ∈ closure (triangulation.triangle r).openCell :=
      (triangulation.triangle r).carrier_subset_closure_openCell hxr
    have hIntersection :
        (U ∩ (triangulation.triangle r).openCell).Nonempty :=
      (mem_closure_iff.mp hxClosure) U hUOpen hxU
    obtain ⟨y, hyU, hyOpenCell⟩ := hIntersection
    -- A point of the dense third open cell must enter one of the two covering
    -- carriers, contradicting disjointness of distinct triangulation cells.
    rcases hUCarrier hyU with hyFirst | hySecond
    · exact Set.disjoint_left.mp
        (triangulation.disjoint_openCell_carrier_of_ne r first hrNe.1)
          hyOpenCell hyFirst
    · exact Set.disjoint_left.mp
        (triangulation.disjoint_openCell_carrier_of_ne r second hrNe.2)
          hyOpenCell hySecond
  -- The incident set injects into a set containing no more than two indices.
  calc
    (triangulation.incidentTriangles i j).ncard ≤
        ({first, second} : Set (Fin triangulation.card)).ncard :=
      Set.ncard_le_ncard hIncidentSubset
    _ ≤ 2 := by
      by_cases hfirstSecond : first = second
      · subst second
        simp
      · rw [Set.ncard_pair hfirstSecond]

/-- Helper for Theorem 78.3: no more than two triangulation triangles can be
incident to a point in the relative interior of an edge. -/
private theorem incidentTriangles_ncard_le_two_of_mem_openEdge
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y]
    (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) (x : Y)
    (hx : x ∈ (triangulation.triangle i).openEdge j) :
    (triangulation.incidentTriangles i j).ncard ≤ 2 := by
  classical
  by_cases hsecond : ∃ r ∈ triangulation.incidentTriangles i j, i ≠ r
  · obtain ⟨r, hrIncident, hir⟩ := hsecond
    obtain ⟨U, hUOpen, p, f, hfContinuous, hfInjective, hfp, hfrange⟩ :=
      triangulation.existsPlanarEmbeddingAt_of_distinct_mem_incidentTriangles
        i j x hx r hir hrIncident
    obtain ⟨V, hVOpen, hfpV, hVrange⟩ :=
      Topology.exists_openNeighborhood_subset_range_of_planarEmbedding
        hUOpen f hfContinuous hfInjective p
    rw [hfp] at hfpV
    -- Invariance of domain promotes the planar patch to an ambient
    -- two-carrier neighborhood, which bounds the incident rank.
    exact triangulation.incidentTriangles_ncard_le_two_of_pairNeighborhood
      i j x hx i r V hVOpen hfpV (hVrange.trans hfrange)
  · have hsubset :
        triangulation.incidentTriangles i j ⊆ ({i} : Set _) := by
      intro r hr
      have hri : r = i := by
        by_contra hne
        exact hsecond ⟨r, hr, Ne.symm hne⟩
      simpa only [Set.mem_singleton_iff] using hri
    -- If no distinct incident triangle exists, the incident set is a singleton.
    calc
      (triangulation.incidentTriangles i j).ncard ≤ ({i} : Set _).ncard :=
        Set.ncard_le_ncard hsubset
      _ ≤ 2 := by simp

/-- Helper for Theorem 78.3: a surface-boundary point in the relative interior
of a triangulation edge has incident-triangle rank one. -/
private theorem incidentTriangles_ncard_eq_one_of_mem_surfaceBoundary_of_mem_openEdge
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) (x : Y)
    (hx : x ∈ (triangulation.triangle i).openEdge j)
    (hxBoundary : x ∈ (∂Y : Set Y)) :
    (triangulation.incidentTriangles i j).ncard = 1 := by
  classical
  have hpositive := triangulation.incidentTriangles_ncard_pos i j
  have hatMostTwo :=
    triangulation.incidentTriangles_ncard_le_two_of_mem_openEdge i j x hx
  by_contra hne
  have htwo : (triangulation.incidentTriangles i j).ncard = 2 := by
    omega
  have honeLt : 1 < (triangulation.incidentTriangles i j).ncard := by
    omega
  obtain ⟨r, hrIncident, hri⟩ :=
    (triangulation.incidentTriangles i j).exists_ne_of_one_lt_ncard honeLt i
  obtain ⟨U, hUOpen, p, f, hfContinuous, hfInjective, hfp, _⟩ :=
    triangulation.existsPlanarEmbeddingAt_of_distinct_mem_incidentTriangles
      i j x hx r hri.symm hrIncident
  have hnotBoundary :=
    Topology.planarEmbeddingAt_not_mem_surfaceBoundary
      hUOpen f hfContinuous hfInjective p
  -- The two-page collar passes through `x`, contradicting its boundary membership.
  rw [hfp] at hnotBoundary
  exact hnotBoundary hxBoundary

/-- Helper for Theorem 78.3: an open-edge point lies on the surface boundary
exactly when that edge has one incident triangle. -/
private theorem mem_surfaceBoundary_of_mem_openEdge_iff_incidentTriangles_ncard_eq_one
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3) (x : Y)
    (hx : x ∈ (triangulation.triangle i).openEdge j) :
    x ∈ (∂Y : Set Y) ↔
      (triangulation.incidentTriangles i j).ncard = 1 := by
  classical
  -- Route correction: replace the blocked abstract boundary-circle classification
  -- with the local incidence invariant needed by the finite cycle construction.
  constructor
  · -- Boundary points have rank one by the already established two-page obstruction.
    exact triangulation.incidentTriangles_ncard_eq_one_of_mem_surfaceBoundary_of_mem_openEdge
      i j x hx
  · intro hcard
    by_contra hxBoundary
    obtain ⟨surfaceChart, hxSource⟩ :
        ∃ e : OpenPartialHomeomorph Y (EuclideanSpace ℝ (Fin 2)),
          x ∈ e.source := by
      simpa only [mem_surfaceBoundary_iff_noEuclideanChart, not_not] using
        hxBoundary
    have hIncidentEq : triangulation.incidentTriangles i j = {i} := by
      obtain ⟨only, honly⟩ := Set.ncard_eq_one.mp hcard
      have hiOnly : i = only := by
        exact Set.mem_singleton_iff.mp
          (honly ▸ triangulation.self_mem_incidentTriangles i j)
      exact honly.trans (congrArg (fun r ↦ ({r} : Set _)) hiOnly.symm)
    obtain ⟨U, hUOpen, hxU, hUeq⟩ :=
      triangulation.exists_openNeighborhood_eq_iUnion_incidentCarriers i j x hx
    have hUCarrier : U ⊆ (triangulation.triangle i).carrier := by
      intro y hy
      have hyUnion : y ∈ ⋃ r : triangulation.incidentTriangles i j,
          U ∩ (triangulation.triangle r.1).carrier := by
        rwa [← hUeq]
      obtain ⟨r, _, hyr⟩ := Set.mem_iUnion.mp hyUnion
      have hri : r.1 = i := by
        exact Set.mem_singleton_iff.mp (hIncidentEq ▸ r.2)
      rwa [hri] at hyr
    -- Rank one would trap an ambient neighborhood in a single triangle, which
    -- is impossible in the Euclidean chart supplied by nonboundary membership.
    exact (triangulation.triangle i
      |>.not_exists_openNeighborhood_subset_carrier_of_mem_openEdge_of_chart
        j hx surfaceChart hxSource) ⟨U, hUOpen, hxU, hUCarrier⟩

/-- Helper for Theorem 78.3: boundary points avoiding the finite vertex set of
a triangulation form a dense subset of the surface boundary. -/
private theorem dense_boundaryPoints_not_vertex
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y) :
    Dense {x : ∂Y | ∀ (i : Fin triangulation.card) (j : Fin 3),
      x.1 ≠ (triangulation.triangle i).vertex j} := by
  classical
  let boundaryVertices : Set (∂Y) :=
    {x | ∃ (i : Fin triangulation.card) (j : Fin 3),
      x.1 = (triangulation.triangle i).vertex j}
  have hverticesFinite : boundaryVertices.Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · apply (Set.finite_range (fun edge : Fin triangulation.card × Fin 3 ↦
          (triangulation.triangle edge.1).vertex edge.2)).subset
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨i, j, hij⟩ := hx
      exact ⟨(i, j), hij.symm⟩
    · exact Subtype.val_injective.injOn
  have hcomplement :
      {x : ∂Y | ∀ (i : Fin triangulation.card) (j : Fin 3),
          x.1 ≠ (triangulation.triangle i).vertex j} =
        Set.univ \ boundaryVertices := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, true_and,
      boundaryVertices, not_exists]
  rw [hcomplement]
  exact dense_univ.sdiff_finite hverticesFinite

/-- Helper for Theorem 78.3: an occurrence of a triangulation edge is a boundary
edge when its whole carrier lies in the surface boundary. -/
private def IsBoundaryEdge (triangulation : Triangulation Y)
    (edge : Fin triangulation.card × Fin 3) : Prop :=
  (triangulation.triangle edge.1).edge edge.2 ⊆ (∂Y : Set Y)

/-- Helper for Theorem 78.3: incident-triangle rank one forces the whole
closed edge occurrence to lie in the surface boundary. -/
private theorem isBoundaryEdge_of_incidentTriangles_ncard_eq_one
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y)
    (i : Fin triangulation.card) (j : Fin 3)
    (hcard : (triangulation.incidentTriangles i j).ncard = 1) :
    triangulation.IsBoundaryEdge (i, j) := by
  have hopenSubset : (triangulation.triangle i).openEdge j ⊆ (∂Y : Set Y) := by
    intro x hx
    exact (triangulation.mem_surfaceBoundary_of_mem_openEdge_iff_incidentTriangles_ncard_eq_one
      i j x hx).mpr hcard
  have hclosureSubset :
      closure ((triangulation.triangle i).openEdge j) ⊆ (∂Y : Set Y) :=
    closure_minimal hopenSubset Surface.isClosed_boundary_of_topologicalManifold
  -- The closed edge is the closure of its dense relative interior.
  exact (triangulation.triangle i).edge_subset_closure_openEdge j |>.trans
    hclosureSubset

/-- Helper for Theorem 78.3: every nonboundary geometric edge occurrence has
a unique distinct occurrence representing the same closed curved edge. -/
private theorem existsUniqueGeometricEdgeMate_of_not_isBoundaryEdge
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y)
    (edge : Fin triangulation.card × Fin 3)
    (hnotBoundary : ¬ triangulation.IsBoundaryEdge edge) :
    ∃! mate : Fin triangulation.card × Fin 3,
      mate ≠ edge ∧
        (triangulation.triangle mate.1).edge mate.2 =
          (triangulation.triangle edge.1).edge edge.2 := by
  classical
  -- Route correction: determine the global mate from incident rank two before
  -- making any vertex-local choices for the boundary-star decomposition.
  have htClosed : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
    norm_num
  let t : unitInterval := ⟨1 / 2, htClosed⟩
  let x : Y :=
    triangulation.triangle edge.1 |>.chart
      ((triangulation.triangle edge.1).modelEdgePoint edge.2 t)
  have htOpen : (t : ℝ) ∈ Set.Ioo 0 1 := by
    dsimp only [t]
    norm_num
  have hxOpen : x ∈ (triangulation.triangle edge.1).openEdge edge.2 := by
    exact (triangulation.triangle edge.1
      |>.modelEdgePoint_mem_openEdge_of_mem_Ioo edge.2 t htOpen)
  have hincidentCard :
      (triangulation.incidentTriangles edge.1 edge.2).ncard = 2 := by
    have hpositive :=
      triangulation.incidentTriangles_ncard_pos edge.1 edge.2
    have hatMostTwo :=
      triangulation.incidentTriangles_ncard_le_two_of_mem_openEdge
        edge.1 edge.2 x hxOpen
    have hnotOne :
        (triangulation.incidentTriangles edge.1 edge.2).ncard ≠ 1 := by
      intro hone
      exact hnotBoundary
        (triangulation.isBoundaryEdge_of_incidentTriangles_ncard_eq_one
          edge.1 edge.2 hone)
    omega
  have hremainingCard :
      (triangulation.incidentTriangles edge.1 edge.2 \ {edge.1}).ncard = 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem
      (triangulation.self_mem_incidentTriangles edge.1 edge.2), hincidentCard]
  obtain ⟨mateTriangle, hremaining⟩ := Set.ncard_eq_one.mp hremainingCard
  have hmateIncident :
      mateTriangle ∈ triangulation.incidentTriangles edge.1 edge.2 := by
    have hmember : mateTriangle ∈
        triangulation.incidentTriangles edge.1 edge.2 \ {edge.1} := by
      rw [hremaining]
      exact Set.mem_singleton mateTriangle
    exact hmember.1
  have hmateTriangleNe : mateTriangle ≠ edge.1 := by
    have hmember : mateTriangle ∈
        triangulation.incidentTriangles edge.1 edge.2 \ {edge.1} := by
      rw [hremaining]
      exact Set.mem_singleton mateTriangle
    simpa only [Set.mem_singleton_iff] using hmember.2
  obtain ⟨mateEdge, hintersectionOwner, hintersectionMate, hcompatible⟩ :=
    triangulation.exists_compatibleSharedEdge_of_mem_incidentTriangles
      edge.1 edge.2 x hxOpen mateTriangle hmateTriangleNe.symm hmateIncident
  have hmateEdgeEq :
      (triangulation.triangle mateTriangle).edge mateEdge =
        (triangulation.triangle edge.1).edge edge.2 :=
    hintersectionMate.symm.trans hintersectionOwner
  refine ⟨⟨mateTriangle, mateEdge⟩, ?_, ?_⟩
  · -- The remaining incident triangle differs from the owner and carries the
    -- same closed curved edge.
    exact ⟨fun heq ↦ hmateTriangleNe (congrArg Prod.fst heq), hmateEdgeEq⟩
  · rintro ⟨otherTriangle, otherEdge⟩ ⟨hotherNe, hotherEdgeEq⟩
    have hotherIncident :
        otherTriangle ∈ triangulation.incidentTriangles edge.1 edge.2 := by
      change (triangulation.triangle edge.1).edge edge.2 ⊆
        (triangulation.triangle otherTriangle).carrier
      rw [← hotherEdgeEq]
      exact (triangulation.triangle otherTriangle).edge_subset otherEdge
    have hotherTriangleNe : otherTriangle ≠ edge.1 := by
      intro htriangle
      subst otherTriangle
      have hedgeIndex : otherEdge = edge.2 := by
        by_contra hedgeNe
        have hxOtherEdge : x ∈
            (triangulation.triangle edge.1).edge otherEdge := by
          rw [hotherEdgeEq]
          exact (triangulation.triangle edge.1).openEdge_subset_edge edge.2 hxOpen
        exact Set.disjoint_left.mp
          ((triangulation.triangle edge.1).disjoint_openEdge_edge_of_ne
            (Ne.symm hedgeNe)) hxOpen hxOtherEdge
      subst otherEdge
      exact hotherNe rfl
    have hotherRemaining : otherTriangle ∈
        triangulation.incidentTriangles edge.1 edge.2 \ {edge.1} := by
      exact ⟨hotherIncident, by simpa only [Set.mem_singleton_iff]⟩
    have htriangleEq : otherTriangle = mateTriangle := by
      rw [hremaining] at hotherRemaining
      exact Set.mem_singleton_iff.mp hotherRemaining
    subst otherTriangle
    have hxMateOpen : x ∈
        (triangulation.triangle mateTriangle).openEdge mateEdge := by
      obtain ⟨reverse, hreverse⟩ :=
        ((triangulation.triangle edge.1).edgesCompatible_iff
          (triangulation.triangle mateTriangle) edge.2 mateEdge).mp hcompatible
      have hfixed :
          (if reverse then unitInterval.symm t else t) = t := by
        cases reverse
        · rfl
        · apply Subtype.ext
          simp only [if_pos, unitInterval.coe_symm_eq]
          dsimp only [t]
          norm_num
      have hmidpoint := hreverse t
      rw [hfixed] at hmidpoint
      -- Compatibility identifies the two midpoint images, so the second
      -- triangle's own open-edge lemma supplies the desired membership.
      dsimp only [x]
      rw [hmidpoint]
      exact (triangulation.triangle mateTriangle
        |>.modelEdgePoint_mem_openEdge_of_mem_Ioo mateEdge t htOpen)
    have hedgeEq : otherEdge = mateEdge := by
      by_contra hedgeNe
      have hxOtherEdge : x ∈
          (triangulation.triangle mateTriangle).edge otherEdge := by
        rw [hotherEdgeEq]
        exact (triangulation.triangle edge.1).openEdge_subset_edge edge.2 hxOpen
      exact Set.disjoint_left.mp
        ((triangulation.triangle mateTriangle).disjoint_openEdge_edge_of_ne
          (Ne.symm hedgeNe)) hxMateOpen hxOtherEdge
    subst otherEdge
    rfl

/-- Helper for Theorem 78.3: the finite type of boundary-edge occurrences in a
fixed triangulation. -/
private abbrev BoundaryEdge (triangulation : Triangulation Y) :=
  {edge : Fin triangulation.card × Fin 3 // triangulation.IsBoundaryEdge edge}

/-- Helper for Theorem 78.3: the part of a boundary edge regarded as a subset of
the boundary subtype. -/
private def boundaryEdgeCarrier (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) : Set (∂Y) :=
  {x | x.1 ∈ (triangulation.triangle edge.1.1).edge edge.1.2}

/-- Helper for Theorem 78.3: membership in the union of boundary-edge carriers
is exactly pointwise incidence with an edge wholly contained in the boundary. -/
private theorem mem_iUnion_boundaryEdgeCarrier_iff
    (triangulation : Triangulation Y) (x : ∂Y) :
    x ∈ ⋃ edge : triangulation.BoundaryEdge,
        triangulation.boundaryEdgeCarrier edge ↔
      ∃ (i : Fin triangulation.card) (j : Fin 3),
        x.1 ∈ (triangulation.triangle i).edge j ∧
          (triangulation.triangle i).edge j ⊆ (∂Y : Set Y) := by
  -- Unpack a subtype-indexed union into its triangle, edge, and boundary certificate.
  constructor
  · intro hx
    obtain ⟨edge, hxedge⟩ := Set.mem_iUnion.mp hx
    exact ⟨edge.1.1, edge.1.2, hxedge, edge.2⟩
  · rintro ⟨i, j, hxedge, hboundary⟩
    let edge : triangulation.BoundaryEdge := ⟨(i, j), hboundary⟩
    -- Repackage the incidence witness as a boundary-edge occurrence.
    exact Set.mem_iUnion.mpr ⟨edge, hxedge⟩

/-- Helper for Theorem 78.3: pointwise boundary-edge incidence is precisely the
geometric input needed for the boundary-edge carriers to cover the boundary. -/
private theorem iUnion_boundaryEdgeCarrier_eq_univ_of_incidence
    (triangulation : Triangulation Y)
    (hincidence : ∀ x : ∂Y,
      ∃ (i : Fin triangulation.card) (j : Fin 3),
        x.1 ∈ (triangulation.triangle i).edge j ∧
          (triangulation.triangle i).edge j ⊆ (∂Y : Set Y)) :
    (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) = Set.univ := by
  -- Apply the pointwise incidence witness through the union membership normal form.
  apply Set.eq_univ_of_forall
  intro x
  exact (mem_iUnion_boundaryEdgeCarrier_iff triangulation x).mpr (hincidence x)

/-- Helper for Theorem 78.3: one half lies in the unit interval and hence
parametrizes the midpoint of every triangulation edge. -/
private theorem boundaryEdgeMidpointParameter_mem :
    (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
  -- Both endpoint inequalities are elementary numerical facts.
  norm_num

/-- Helper for Theorem 78.3: the common unit-interval parameter used to choose
the midpoint of a boundary edge. -/
private noncomputable def boundaryEdgeMidpointParameter : unitInterval :=
  ⟨1 / 2, boundaryEdgeMidpointParameter_mem⟩

/-- Helper for Theorem 78.3: every parametrized point of a boundary edge belongs
to the surface boundary. -/
private theorem boundaryEdgePoint_mem_boundary
    (triangulation : Triangulation Y) (edge : triangulation.BoundaryEdge)
    (t : unitInterval) :
    ((triangulation.triangle edge.1.1).chart
        ((triangulation.triangle edge.1.1).modelEdgePoint edge.1.2 t)).1 ∈
      (∂Y : Set Y) := by
  -- The selected point is on the curved edge, whose defining property puts it in `∂Y`.
  apply edge.2
  rw [CurvedTriangle.mem_edge_iff]
  exact ⟨t, rfl⟩

/-- Helper for Theorem 78.3: the canonical unit-interval parametrization of a
boundary edge, valued in the boundary subtype. -/
private noncomputable def boundaryEdgePoint (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) (t : unitInterval) : ∂Y :=
  ⟨((triangulation.triangle edge.1.1).chart
      ((triangulation.triangle edge.1.1).modelEdgePoint edge.1.2 t)).1,
    boundaryEdgePoint_mem_boundary triangulation edge t⟩

/-- Helper for Theorem 78.3: the canonical parametrization of a boundary edge
is continuous. -/
private theorem continuous_boundaryEdgePoint (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) :
    Continuous (triangulation.boundaryEdgePoint edge) := by
  -- Route correction: transport the owner-level model-edge continuity through the
  -- chart, rather than unfolding the affine parametrization after both subtype lifts.
  unfold boundaryEdgePoint
  apply Continuous.subtype_mk
  -- Forget the chart codomain subtype after composing the chart with the model edge.
  exact continuous_subtype_val.comp
    ((triangulation.triangle edge.1.1).chart.continuous.comp
      ((triangulation.triangle edge.1.1).continuous_modelEdgePoint edge.1.2))

/-- Helper for Theorem 78.3: the canonical boundary-edge parametrization is
injective. -/
private theorem injective_boundaryEdgePoint (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) :
    Function.Injective (triangulation.boundaryEdgePoint edge) := by
  intro s t hst
  -- Forget the boundary subtype, then cancel the triangle chart and the affine
  -- parametrization in succession.
  have hchart :
      (triangulation.triangle edge.1.1).chart
          ((triangulation.triangle edge.1.1).modelEdgePoint edge.1.2 s) =
        (triangulation.triangle edge.1.1).chart
          ((triangulation.triangle edge.1.1).modelEdgePoint edge.1.2 t) := by
    apply Subtype.ext
    simpa only [boundaryEdgePoint] using
      congrArg (fun z : ∂Y ↦ (z : Y)) hst
  have hmodel :=
    (triangulation.triangle edge.1.1).chart.injective hchart
  exact (triangulation.triangle edge.1.1).injective_modelEdgeValue edge.1.2
    (congrArg Subtype.val hmodel)

/-- Helper for Theorem 78.3: each boundary edge is an embedded copy of the
closed unit interval in the boundary one-manifold. -/
private theorem boundaryEdgePoint_isEmbedding [T2Space Y]
    (triangulation : Triangulation Y) (edge : triangulation.BoundaryEdge) :
    Topology.IsEmbedding (triangulation.boundaryEdgePoint edge) := by
  -- Compactness of the interval and Hausdorffness of the boundary upgrade the
  -- preceding continuous injection to a closed embedding.
  exact ((triangulation.continuous_boundaryEdgePoint edge).isClosedEmbedding
    (triangulation.injective_boundaryEdgePoint edge)).isEmbedding

/-- Helper for Theorem 78.3: a canonical point on each boundary edge. -/
private noncomputable def boundaryEdgeMidpoint (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) : ∂Y :=
  triangulation.boundaryEdgePoint edge boundaryEdgeMidpointParameter

/-- Helper for Theorem 78.3: the topological boundary component containing a
boundary edge's chosen midpoint. -/
private noncomputable def boundaryEdgeComponent (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) : ConnectedComponents (∂Y) :=
  ConnectedComponents.mk (triangulation.boundaryEdgeMidpoint edge)

/-- Helper for Theorem 78.3: two boundary-edge occurrences meet when their
carriers share a boundary point. -/
private def BoundaryEdgesMeet (triangulation : Triangulation Y)
    (first second : triangulation.BoundaryEdge) : Prop :=
  (triangulation.boundaryEdgeCarrier first ∩
    triangulation.boundaryEdgeCarrier second).Nonempty

/-- Helper for Theorem 78.3: meeting of boundary-edge carriers is symmetric. -/
private theorem boundaryEdgesMeet_comm (triangulation : Triangulation Y)
    (first second : triangulation.BoundaryEdge) :
    triangulation.BoundaryEdgesMeet first second ↔
      triangulation.BoundaryEdgesMeet second first := by
  -- Swap the two carrier factors in the intersection.
  rw [BoundaryEdgesMeet, BoundaryEdgesMeet, Set.inter_comm]

/-- Helper for Theorem 78.3: the finite graph joining distinct boundary edges
whose carriers meet. -/
private def boundaryEdgeGraph (triangulation : Triangulation Y) :
    SimpleGraph triangulation.BoundaryEdge :=
  SimpleGraph.fromRel triangulation.BoundaryEdgesMeet

/-- Helper for Theorem 78.3: adjacency in the boundary-edge graph is exactly
distinctness together with a shared boundary point. -/
private theorem boundaryEdgeGraph_adj (triangulation : Triangulation Y)
    (first second : triangulation.BoundaryEdge) :
    triangulation.boundaryEdgeGraph.Adj first second ↔
      first ≠ second ∧ triangulation.BoundaryEdgesMeet first second := by
  -- `fromRel` removes loops; symmetry collapses its two possible relation directions.
  rw [boundaryEdgeGraph, SimpleGraph.fromRel_adj]
  simp only [boundaryEdgesMeet_comm triangulation second first, or_self]

/-- Helper for Theorem 78.3: the chosen midpoint lies in its boundary-edge
carrier. -/
private theorem boundaryEdgeMidpoint_mem_carrier (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) :
    triangulation.boundaryEdgeMidpoint edge ∈
      triangulation.boundaryEdgeCarrier edge := by
  -- Unpack the carrier and use the curved-edge parametrization at one half.
  simp only [boundaryEdgeCarrier, Set.mem_setOf_eq, boundaryEdgeMidpoint]
  rw [CurvedTriangle.mem_edge_iff]
  exact ⟨boundaryEdgeMidpointParameter, rfl⟩

/-- Helper for Theorem 78.3: the canonical parametrization has exactly the
boundary-edge carrier as its range. -/
private theorem range_boundaryEdgePoint (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) :
    Set.range (triangulation.boundaryEdgePoint edge) =
      triangulation.boundaryEdgeCarrier edge := by
  -- Translate both sides through the curved-edge range characterization.
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    simp only [boundaryEdgeCarrier, Set.mem_setOf_eq, boundaryEdgePoint]
    rw [CurvedTriangle.mem_edge_iff]
    exact ⟨t, rfl⟩
  · intro hx
    simp only [boundaryEdgeCarrier, Set.mem_setOf_eq] at hx
    obtain ⟨t, htx⟩ :=
      ((triangulation.triangle edge.1.1).mem_edge_iff edge.1.2 x.1).mp hx
    refine ⟨t, ?_⟩
    apply Subtype.ext
    exact htx.symm

/-- Helper for Theorem 78.3: each boundary-edge carrier is connected. -/
private theorem boundaryEdgeCarrier_isConnected (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) :
    IsConnected (triangulation.boundaryEdgeCarrier edge) := by
  -- Identify the carrier with the continuous image of the connected unit interval.
  rw [← range_boundaryEdgePoint]
  exact isConnected_range (continuous_boundaryEdgePoint triangulation edge)

/-- Helper for Theorem 78.3: each boundary-edge carrier is compact. -/
private theorem boundaryEdgeCarrier_isCompact (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) :
    IsCompact (triangulation.boundaryEdgeCarrier edge) := by
  -- Identify the carrier with the continuous image of the compact unit interval.
  rw [← range_boundaryEdgePoint]
  exact isCompact_range (continuous_boundaryEdgePoint triangulation edge)

/-- Helper for Theorem 78.3: each boundary-edge carrier is closed in the
boundary of a Hausdorff surface. -/
private theorem boundaryEdgeCarrier_isClosed [T2Space Y]
    (triangulation : Triangulation Y) (edge : triangulation.BoundaryEdge) :
    IsClosed (triangulation.boundaryEdgeCarrier edge) := by
  -- Compact subsets of the Hausdorff boundary subspace are closed.
  exact (boundaryEdgeCarrier_isCompact triangulation edge).isClosed

/-- Helper for Theorem 78.3: the finite union of all boundary-edge carriers is
closed in the boundary of a Hausdorff surface. -/
private theorem iUnion_boundaryEdgeCarrier_isClosed [T2Space Y]
    (triangulation : Triangulation Y) :
    IsClosed (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) := by
  -- Finiteness of edge occurrences reduces closedness to the preceding carrier lemma.
  exact isClosed_iUnion_of_finite fun edge ↦
    boundaryEdgeCarrier_isClosed triangulation edge

/-- Helper for Theorem 78.3: the boundary-edge carriers of a finite
triangulation cover the whole surface boundary. -/
private theorem iUnion_boundaryEdgeCarrier_eq_univ
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y) :
    (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) = Set.univ := by
  let vertexFree : Set (∂Y) :=
    {x | ∀ (i : Fin triangulation.card) (j : Fin 3),
      x.1 ≠ (triangulation.triangle i).vertex j}
  have hvertexFreeDense : Dense vertexFree :=
    triangulation.dense_boundaryPoints_not_vertex
  have hvertexFreeSubset :
      vertexFree ⊆ ⋃ edge : triangulation.BoundaryEdge,
        triangulation.boundaryEdgeCarrier edge := by
    intro x hx
    obtain ⟨i, j, hxEdge⟩ :=
      triangulation.exists_edge_of_mem_surfaceBoundary x
    have hxOpen : x.1 ∈ (triangulation.triangle i).openEdge j :=
      (triangulation.triangle i).mem_openEdge_of_mem_edge_of_ne_vertex
        j hxEdge (hx i)
    have hcard : (triangulation.incidentTriangles i j).ncard = 1 :=
      (triangulation.mem_surfaceBoundary_of_mem_openEdge_iff_incidentTriangles_ncard_eq_one
        i j x.1 hxOpen).mp x.2
    have hboundary : triangulation.IsBoundaryEdge (i, j) :=
      triangulation.isBoundaryEdge_of_incidentTriangles_ncard_eq_one i j hcard
    exact (triangulation.mem_iUnion_boundaryEdgeCarrier_iff x).mpr
      ⟨i, j, hxEdge, hboundary⟩
  have hclosureSubset :
      closure vertexFree ⊆ ⋃ edge : triangulation.BoundaryEdge,
        triangulation.boundaryEdgeCarrier edge :=
    closure_minimal hvertexFreeSubset
      (triangulation.iUnion_boundaryEdgeCarrier_isClosed)
  -- Closedness upgrades the cover of the dense vertex-free locus to all points.
  apply Set.eq_univ_of_forall
  intro x
  apply hclosureSubset
  rw [hvertexFreeDense.closure_eq]
  exact Set.mem_univ x

/-- Helper for Theorem 78.3: every point of a boundary-edge carrier represents
the same boundary component as that edge's chosen midpoint. -/
private theorem boundaryEdgeComponent_eq_mk_of_mem (triangulation : Triangulation Y)
    (edge : triangulation.BoundaryEdge) (x : ∂Y)
    (hx : x ∈ triangulation.boundaryEdgeCarrier edge) :
    triangulation.boundaryEdgeComponent edge = ConnectedComponents.mk x := by
  -- Connectedness of the carrier joins the chosen midpoint to the specified point.
  have hxcomponent :
      x ∈ connectedComponent (triangulation.boundaryEdgeMidpoint edge) :=
    (boundaryEdgeCarrier_isConnected triangulation edge).subset_connectedComponent
      (boundaryEdgeMidpoint_mem_carrier triangulation edge) hx
  apply ConnectedComponents.coe_eq_coe.mpr
  exact connectedComponent_eq hxcomponent

/-- Helper for Theorem 78.3: if boundary-edge carriers cover the boundary, then
their chosen midpoints meet every topological boundary component. -/
private theorem boundaryEdgeComponent_surjective_of_cover
    (triangulation : Triangulation Y)
    (hcover : (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) = Set.univ) :
    Function.Surjective triangulation.boundaryEdgeComponent := by
  intro component
  obtain ⟨x, hxcomponent⟩ := ConnectedComponents.surjective_coe component
  -- Choose a covering boundary edge and identify its midpoint component with `component`.
  have hxcover : x ∈ ⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge := by
    rw [hcover]
    exact Set.mem_univ x
  obtain ⟨edge, hxedge⟩ := Set.mem_iUnion.mp hxcover
  refine ⟨edge, ?_⟩
  exact (boundaryEdgeComponent_eq_mk_of_mem triangulation edge x hxedge).trans hxcomponent

/-- Helper for Theorem 78.3: meeting boundary edges lie in the same topological
boundary component. -/
private theorem boundaryEdgeComponent_eq_of_meet (triangulation : Triangulation Y)
    {first second : triangulation.BoundaryEdge}
    (hmeet : triangulation.BoundaryEdgesMeet first second) :
    triangulation.boundaryEdgeComponent first =
      triangulation.boundaryEdgeComponent second := by
  -- A shared point joins both edge midpoints through their connected carriers.
  obtain ⟨x, hxfirst, hxsecond⟩ := hmeet
  have hfirst : x ∈ connectedComponent (triangulation.boundaryEdgeMidpoint first) :=
    (boundaryEdgeCarrier_isConnected triangulation first).subset_connectedComponent
      (boundaryEdgeMidpoint_mem_carrier triangulation first) hxfirst
  have hsecond : x ∈ connectedComponent (triangulation.boundaryEdgeMidpoint second) :=
    (boundaryEdgeCarrier_isConnected triangulation second).subset_connectedComponent
      (boundaryEdgeMidpoint_mem_carrier triangulation second) hxsecond
  apply ConnectedComponents.coe_eq_coe.mpr
  exact (connectedComponent_eq hfirst).trans (connectedComponent_eq hsecond).symm

/-- Helper for Theorem 78.3: adjacent vertices of the boundary-edge graph have
the same topological boundary component. -/
private theorem boundaryEdgeComponent_eq_of_adj (triangulation : Triangulation Y)
    {first second : triangulation.BoundaryEdge}
    (hadj : triangulation.boundaryEdgeGraph.Adj first second) :
    triangulation.boundaryEdgeComponent first =
      triangulation.boundaryEdgeComponent second := by
  -- Adjacency supplies the shared point needed by the connected-carrier argument.
  exact boundaryEdgeComponent_eq_of_meet triangulation
    ((boundaryEdgeGraph_adj triangulation first second).mp hadj).2

/-- Helper for Theorem 78.3: graph reachability cannot leave a topological
boundary component. -/
private theorem boundaryEdgeComponent_eq_of_reachable (triangulation : Triangulation Y)
    {first second : triangulation.BoundaryEdge}
    (hreachable : triangulation.boundaryEdgeGraph.Reachable first second) :
    triangulation.boundaryEdgeComponent first =
      triangulation.boundaryEdgeComponent second := by
  -- Induct along the reflexive-transitive closure of graph adjacency.
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => rfl
  | tail _ hadj ih =>
      exact ih.trans (boundaryEdgeComponent_eq_of_adj triangulation hadj)

/-- Helper for Theorem 78.3: the geometric carrier of a connected component of
the boundary-edge graph is the union of the carriers of its vertices. -/
private def boundaryEdgeGraphComponentCarrier (triangulation : Triangulation Y)
    (component : triangulation.boundaryEdgeGraph.ConnectedComponent) : Set (∂Y) :=
  ⋃ edge : component.supp, triangulation.boundaryEdgeCarrier edge.1

/-- Helper for Theorem 78.3: every geometric boundary-edge graph component has
closed carrier in the boundary of a Hausdorff surface. -/
private theorem boundaryEdgeGraphComponentCarrier_isClosed [T2Space Y]
    (triangulation : Triangulation Y)
    (component : triangulation.boundaryEdgeGraph.ConnectedComponent) :
    IsClosed (triangulation.boundaryEdgeGraphComponentCarrier component) := by
  -- The component has finitely many edge occurrences, each with compact carrier.
  exact isClosed_iUnion_of_finite fun edge ↦
    triangulation.boundaryEdgeCarrier_isClosed edge.1

/-- Helper for Theorem 78.3: distinct boundary-edge graph components have
disjoint geometric carriers. -/
private theorem boundaryEdgeGraphComponentCarrier_disjoint
    (triangulation : Triangulation Y)
    {first second : triangulation.boundaryEdgeGraph.ConnectedComponent}
    (hne : first ≠ second) :
    Disjoint (triangulation.boundaryEdgeGraphComponentCarrier first)
      (triangulation.boundaryEdgeGraphComponentCarrier second) := by
  -- A common point would make its two containing edges equal or adjacent, and
  -- either alternative identifies their graph components.
  refine Set.disjoint_left.mpr ?_
  intro x hxfirst hxsecond
  obtain ⟨firstEdge, hxFirstEdge⟩ := Set.mem_iUnion.mp hxfirst
  obtain ⟨secondEdge, hxSecondEdge⟩ := Set.mem_iUnion.mp hxsecond
  have hcomponent : first = second := by
    by_cases hedges : firstEdge.1 = secondEdge.1
    · exact firstEdge.2.symm.trans
        ((congrArg triangulation.boundaryEdgeGraph.connectedComponentMk hedges).trans
          secondEdge.2)
    · have hadj : triangulation.boundaryEdgeGraph.Adj firstEdge.1 secondEdge.1 :=
        (triangulation.boundaryEdgeGraph_adj firstEdge.1 secondEdge.1).mpr
          ⟨hedges, ⟨x, hxFirstEdge, hxSecondEdge⟩⟩
      exact firstEdge.2.symm.trans
        ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
          secondEdge.2)
  exact hne hcomponent

/-- Helper for Theorem 78.3: the union of the geometric carriers of all graph
components other than a selected component. -/
private def boundaryEdgeGraphOtherComponentCarrier
    (triangulation : Triangulation Y)
    (component : triangulation.boundaryEdgeGraph.ConnectedComponent) : Set (∂Y) :=
  ⋃ other : {other : triangulation.boundaryEdgeGraph.ConnectedComponent //
      other ≠ component},
    triangulation.boundaryEdgeGraphComponentCarrier other.1

/-- Helper for Theorem 78.3: the geometric carrier of all graph components
other than a selected one is closed. -/
private theorem boundaryEdgeGraphOtherComponentCarrier_isClosed [T2Space Y]
    (triangulation : Triangulation Y)
    (component : triangulation.boundaryEdgeGraph.ConnectedComponent) :
    IsClosed (triangulation.boundaryEdgeGraphOtherComponentCarrier component) := by
  -- This is another finite union of the closed component carriers.
  exact isClosed_iUnion_of_finite fun other ↦
    triangulation.boundaryEdgeGraphComponentCarrier_isClosed other.1

/-- Helper for Theorem 78.3: a selected boundary-edge graph component is
geometrically disjoint from the union of all the other components. -/
private theorem boundaryEdgeGraphComponentCarrier_disjoint_other
    (triangulation : Triangulation Y)
    (component : triangulation.boundaryEdgeGraph.ConnectedComponent) :
    Disjoint (triangulation.boundaryEdgeGraphComponentCarrier component)
      (triangulation.boundaryEdgeGraphOtherComponentCarrier component) := by
  -- Reduce membership in the second union to pairwise component disjointness.
  refine Set.disjoint_left.mpr ?_
  intro x hxcomponent hxother
  obtain ⟨other, hxOtherComponent⟩ := Set.mem_iUnion.mp hxother
  exact Set.disjoint_left.mp
    (triangulation.boundaryEdgeGraphComponentCarrier_disjoint other.2.symm)
      hxcomponent hxOtherComponent

/-- Helper for Theorem 78.3: when boundary edges cover the boundary, one graph
component together with all the other graph components covers it as well. -/
private theorem boundaryEdgeGraphComponentCarrier_union_other_eq_univ
    (triangulation : Triangulation Y)
    (hcover : (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) = Set.univ)
    (component : triangulation.boundaryEdgeGraph.ConnectedComponent) :
    triangulation.boundaryEdgeGraphComponentCarrier component ∪
      triangulation.boundaryEdgeGraphOtherComponentCarrier component = Set.univ := by
  -- Assign a covering edge to its graph component, splitting on whether it is
  -- the selected component.
  apply Set.eq_univ_of_forall
  intro x
  have hxcover : x ∈ ⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge := by
    rw [hcover]
    exact Set.mem_univ x
  obtain ⟨edge, hxedge⟩ := Set.mem_iUnion.mp hxcover
  let edgeComponent := triangulation.boundaryEdgeGraph.connectedComponentMk edge
  by_cases heq : edgeComponent = component
  · left
    exact Set.mem_iUnion.mpr ⟨⟨edge, heq⟩, hxedge⟩
  · right
    refine Set.mem_iUnion.mpr ⟨⟨edgeComponent, heq⟩, ?_⟩
    exact Set.mem_iUnion.mpr ⟨⟨edge, rfl⟩, hxedge⟩

/-- Helper for Theorem 78.3: boundary edges whose midpoints lie in the same
topological boundary component are reachable in the boundary-edge graph. -/
private theorem boundaryEdgeGraph_reachable_of_component_eq
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y)
    (hcover : (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) = Set.univ)
    {first second : triangulation.BoundaryEdge}
    (hcomponent : triangulation.boundaryEdgeComponent first =
      triangulation.boundaryEdgeComponent second) :
    triangulation.boundaryEdgeGraph.Reachable first second := by
  let graphComponent :=
    triangulation.boundaryEdgeGraph.connectedComponentMk first
  by_contra hreachable
  have hsecondComponent :
      triangulation.boundaryEdgeGraph.connectedComponentMk second ≠ graphComponent := by
    intro heq
    apply hreachable
    exact SimpleGraph.ConnectedComponent.exact heq.symm
  let selectedCarrier :=
    triangulation.boundaryEdgeGraphComponentCarrier graphComponent
  let otherCarrier :=
    triangulation.boundaryEdgeGraphOtherComponentCarrier graphComponent
  let topologicalComponent :=
    connectedComponent (triangulation.boundaryEdgeMidpoint first)
  have hfirstTopological :
      triangulation.boundaryEdgeMidpoint first ∈ topologicalComponent :=
    mem_connectedComponent
  have hsecondTopological :
      triangulation.boundaryEdgeMidpoint second ∈ topologicalComponent := by
    have hcomponents :
        connectedComponent (triangulation.boundaryEdgeMidpoint first) =
          connectedComponent (triangulation.boundaryEdgeMidpoint second) :=
      ConnectedComponents.coe_eq_coe.mp hcomponent
    change triangulation.boundaryEdgeMidpoint second ∈
      connectedComponent (triangulation.boundaryEdgeMidpoint first)
    rw [hcomponents]
    exact mem_connectedComponent
  have hfirstSelected :
      triangulation.boundaryEdgeMidpoint first ∈ selectedCarrier := by
    exact Set.mem_iUnion.mpr
      ⟨⟨first, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩,
        triangulation.boundaryEdgeMidpoint_mem_carrier first⟩
  have hsecondOther :
      triangulation.boundaryEdgeMidpoint second ∈ otherCarrier := by
    refine Set.mem_iUnion.mpr
      ⟨⟨triangulation.boundaryEdgeGraph.connectedComponentMk second,
        hsecondComponent⟩, ?_⟩
    exact Set.mem_iUnion.mpr
      ⟨⟨second, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩,
        triangulation.boundaryEdgeMidpoint_mem_carrier second⟩
  have hcoverComponent :
      topologicalComponent ⊆ selectedCarrier ∪ otherCarrier := by
    intro x _
    rw [triangulation.boundaryEdgeGraphComponentCarrier_union_other_eq_univ
      hcover graphComponent]
    exact Set.mem_univ x
  have hintersection := isPreconnected_closed_iff.mp
    isPreconnected_connectedComponent selectedCarrier otherCarrier
      (triangulation.boundaryEdgeGraphComponentCarrier_isClosed graphComponent)
      (triangulation.boundaryEdgeGraphOtherComponentCarrier_isClosed graphComponent)
      hcoverComponent
      ⟨triangulation.boundaryEdgeMidpoint first,
        hfirstTopological, hfirstSelected⟩
      ⟨triangulation.boundaryEdgeMidpoint second,
        hsecondTopological, hsecondOther⟩
  obtain ⟨x, _, hxselected, hxother⟩ := hintersection
  exact Set.disjoint_left.mp
    (triangulation.boundaryEdgeGraphComponentCarrier_disjoint_other graphComponent)
      hxselected hxother

/-- Helper for Theorem 78.3: graph reachability of boundary edges is equivalent
to their belonging to the same topological boundary component. -/
private theorem boundaryEdgeGraph_reachable_iff_component_eq
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    (triangulation : Triangulation Y)
    (hcover : (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) = Set.univ)
    {first second : triangulation.BoundaryEdge} :
    triangulation.boundaryEdgeGraph.Reachable first second ↔
      triangulation.boundaryEdgeComponent first =
        triangulation.boundaryEdgeComponent second := by
  -- Combine preservation along graph walks with the connectedness argument above.
  exact ⟨triangulation.boundaryEdgeComponent_eq_of_reachable,
    triangulation.boundaryEdgeGraph_reachable_of_component_eq hcover⟩

end Triangulation

/-- Helper for Theorem 78.3: a boundary with cardinality `k` has its connected
components enumerated by `Fin k`. -/
private theorem boundaryComponentsEquivFin
    (Y : Type u) [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    (k : ℕ) (h_boundary : Cardinal.mk (ConnectedComponents (∂Y)) = k) :
    Nonempty (ConnectedComponents (∂Y) ≃ Fin k) := by
  -- Convert the finite cardinal equality into an explicit component enumeration.
  exact Cardinal.mk_eq_nat_iff.mp h_boundary

/-- Helper for Theorem 78.3: the points in the `i`th enumerated boundary component. -/
private def boundaryComponentFiber
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) (i : Fin k) : Set (∂Y) :=
  {x | components (ConnectedComponents.mk x) = i}

/-- Helper for Theorem 78.3: every enumerated boundary component contains a point. -/
private theorem boundaryComponentFiber_nonempty
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) (i : Fin k) :
    (boundaryComponentFiber components i).Nonempty := by
  -- Lift the requested quotient component to a boundary point and evaluate its index.
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (components.symm i)
  refine ⟨x, ?_⟩
  simp only [boundaryComponentFiber, Set.mem_setOf_eq]
  rw [hx, components.apply_symm_apply]

/-- Helper for Theorem 78.3: an enumerated fiber is the connected component of any
point that it contains. -/
private theorem boundaryComponentFiber_eq_connectedComponent
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) (i : Fin k)
    (x : ∂Y) (hx : components (ConnectedComponents.mk x) = i) :
    boundaryComponentFiber components i = connectedComponent x := by
  -- Compare both sets with the quotient-map fiber of the component represented by `x`.
  rw [← connectedComponents_preimage_singleton]
  ext y
  simp only [boundaryComponentFiber, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · intro hy
    exact components.injective (hy.trans hx.symm)
  · intro hy
    exact congrArg components hy |>.trans hx

/-- Helper for Theorem 78.3: the enumerated boundary fibers are genuine connected sets. -/
private theorem boundaryComponentFiber_isConnected
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) (i : Fin k) :
    IsConnected (boundaryComponentFiber components i) := by
  -- Choose a point in the fiber, identify the fiber with its component, and use connectedness.
  obtain ⟨x, hx⟩ := boundaryComponentFiber_nonempty components i
  rw [boundaryComponentFiber_eq_connectedComponent components i x hx]
  exact isConnected_connectedComponent

/-- Helper for Theorem 78.3: every enumerated boundary component is closed in
the boundary subspace. -/
private theorem boundaryComponentFiber_isClosed
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) (i : Fin k) :
    IsClosed (boundaryComponentFiber components i) := by
  -- Identify the fiber with one connected component, which is always closed.
  obtain ⟨x, hx⟩ := boundaryComponentFiber_nonempty components i
  rw [boundaryComponentFiber_eq_connectedComponent components i x hx]
  exact isClosed_connectedComponent

/-- Helper for Theorem 78.3: every enumerated boundary component is open in
the boundary subspace of a topological surface. -/
private theorem boundaryComponentFiber_isOpen
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) (i : Fin k) :
    IsOpen (boundaryComponentFiber components i) := by
  -- The induced one-manifold structure makes the boundary locally connected,
  -- so each connected component is open.
  letI : LocallyConnectedSpace (∂Y) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) (∂Y)
  obtain ⟨x, hx⟩ := boundaryComponentFiber_nonempty components i
  rw [boundaryComponentFiber_eq_connectedComponent components i x hx]
  exact isOpen_connectedComponent

/-- Helper for Theorem 78.3: every enumerated component of the boundary of a
compact topological surface is compact. -/
private theorem boundaryComponentFiber_isCompact
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [CompactSpace Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) (i : Fin k) :
    IsCompact (boundaryComponentFiber components i) := by
  -- First transfer compactness from the closed ambient boundary to its subtype.
  letI : CompactSpace (∂Y) :=
    isCompact_iff_compactSpace.mp
      Surface.isClosed_boundary_of_topologicalManifold.isCompact
  -- The component is closed in that compact boundary subtype.
  exact (boundaryComponentFiber_isClosed components i).isCompact

/-- Helper for Theorem 78.3: the enumerated boundary fibers form a disjoint cover. -/
private theorem boundaryComponentFiber_partition
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) :
    Set.univ.PairwiseDisjoint (boundaryComponentFiber components) ∧
      ⋃ i, boundaryComponentFiber components i = Set.univ := by
  -- Distinct indices cannot contain the same quotient component.
  constructor
  · intro i _ j _ hij
    refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    simp only [boundaryComponentFiber, Set.mem_setOf_eq] at hxi hxj
    exact hij (hxi.symm.trans hxj)
  · -- Every boundary point belongs to the fiber indexed by its own quotient component.
    ext x
    simp only [Set.mem_iUnion, boundaryComponentFiber, Set.mem_setOf_eq, Set.mem_univ,
      iff_true]
    exact ⟨components (ConnectedComponents.mk x), rfl⟩

/-- Helper for Theorem 78.3: every point of a boundary edge lies in the
enumerated component selected by that edge's midpoint. -/
private theorem Triangulation.boundaryEdgeCarrier_subset_componentFiber
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (triangulation : Triangulation Y)
    (components : ConnectedComponents (∂Y) ≃ Fin k)
    (edge : triangulation.BoundaryEdge) (i : Fin k)
    (hindex : components (triangulation.boundaryEdgeComponent edge) = i) :
    triangulation.boundaryEdgeCarrier edge ⊆
      boundaryComponentFiber components i := by
  -- Connectedness of the edge carrier identifies every represented component
  -- with the component of the chosen midpoint, whose index is fixed by `hindex`.
  intro x hx
  simp only [boundaryComponentFiber, Set.mem_setOf_eq]
  calc
    components (ConnectedComponents.mk x) =
        components (triangulation.boundaryEdgeComponent edge) :=
      congrArg components
        (triangulation.boundaryEdgeComponent_eq_mk_of_mem edge x hx).symm
    _ = i := hindex

/-- Helper for Theorem 78.3: once boundary edges cover the boundary, each
enumerated component is exactly the union of the edge carriers indexed by it. -/
private theorem Triangulation.boundaryComponentFiber_eq_iUnion_edgeCarriers
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (triangulation : Triangulation Y)
    (components : ConnectedComponents (∂Y) ≃ Fin k)
    (hcover : (⋃ edge : triangulation.BoundaryEdge,
      triangulation.boundaryEdgeCarrier edge) = Set.univ) (i : Fin k) :
    boundaryComponentFiber components i =
      ⋃ edge : {edge : triangulation.BoundaryEdge //
          components (triangulation.boundaryEdgeComponent edge) = i},
        triangulation.boundaryEdgeCarrier edge.1 := by
  -- For the forward inclusion, choose a covering edge and recover its index
  -- from the component equality supplied by membership in that carrier.
  apply Set.Subset.antisymm
  · intro x hx
    have hxcover : x ∈ ⋃ edge : triangulation.BoundaryEdge,
        triangulation.boundaryEdgeCarrier edge := by
      rw [hcover]
      exact Set.mem_univ x
    obtain ⟨edge, hxedge⟩ := Set.mem_iUnion.mp hxcover
    have hxindex : components (triangulation.boundaryEdgeComponent edge) = i := by
      have hcomponent :=
        triangulation.boundaryEdgeComponent_eq_mk_of_mem edge x hxedge
      exact congrArg components hcomponent |>.trans hx
    exact Set.mem_iUnion.mpr ⟨⟨edge, hxindex⟩, hxedge⟩
  · -- Each indexed carrier lies in its corresponding component fiber.
    intro x hx
    obtain ⟨edge, hxedge⟩ := Set.mem_iUnion.mp hx
    exact triangulation.boundaryEdgeCarrier_subset_componentFiber
      components edge.1 i edge.2 hxedge

/-- Helper for Theorem 78.3: the incidence defect of a connected finite graph
is at most two when twice the vertex count is the dart count plus that defect. -/
private theorem boundaryDefect_le_two
    {vertexCount edgeCount defect : ℕ}
    (hconnected : vertexCount ≤ edgeCount + 1)
    (hincidence : 2 * vertexCount = 2 * edgeCount + defect) :
    defect ≤ 2 := by
  -- Substitute the incidence identity into the connected-graph rank bound.
  omega

/-- Helper for Theorem 78.3: a positive even incidence defect of a connected
finite graph is exactly two. -/
private theorem boundaryDefect_eq_two
    {vertexCount edgeCount defect : ℕ}
    (hconnected : vertexCount ≤ edgeCount + 1)
    (hincidence : 2 * vertexCount = 2 * edgeCount + defect)
    (hpositive : 0 < defect) (heven : Even defect) :
    defect = 2 := by
  -- The rank calculation gives the upper bound; evenness excludes the sole
  -- remaining positive value below two.
  have hle : defect ≤ 2 := boundaryDefect_le_two hconnected hincidence
  obtain ⟨half, hhalf⟩ := heven
  omega

/-- Helper for Theorem 78.3: a closed capped surface packages the manifold
structure obtained by filling every boundary component, together with the
original surface as the complement of the cap disks. -/
private structure Surface.CappedSurface
    (Y : Type u) [TopologicalSpace Y] (k : ℕ) where
  X : Type u
  [topologicalSpace : TopologicalSpace X]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
  [topologicalManifold : TopologicalManifold 2 X]
  [compactSpace : CompactSpace X]
  [connectedSpace : ConnectedSpace X]
  triangulable : Triangulable X
  holes : Surface.IsWithHoles Y X k

/-- Helper for Theorem 78.3: circle coordinates on every enumerated component
of a surface boundary. -/
private structure Surface.BoundaryCircleData
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    {k : ℕ} (components : ConnectedComponents (∂Y) ≃ Fin k) where
  componentHomeomorph (i : Fin k) :
    StandardSphere.boundary 1 ≃ₜ boundaryComponentFiber components i

/-- Helper for Theorem 78.3: the compact connected components of a surface
boundary admit circle coordinates. -/
private theorem Surface.existsBoundaryCircleData
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    [CompactSpace Y] {k : ℕ}
    (components : ConnectedComponents (∂Y) ≃ Fin k) :
    Nonempty (Surface.BoundaryCircleData components) := by
  -- Build the package componentwise, reducing the remaining obligation to one
  -- explicit circle coordinate for each enumerated boundary component.
  refine ⟨⟨fun i ↦ ?_⟩⟩
  -- Route correction: the import closure has no general compact connected
  -- one-manifold classification theorem.  Extract a cyclic order from the
  -- finite boundary-edge incidence graph, then glue its interval parameters
  -- into this homeomorphism.
  -- TODO: consume the exact-valence theorem from
  -- `Theorem_78_3/FiniteLinearOneManifold.lean`, construct the component cycle,
  -- and use compact-to-Hausdorff continuity to obtain the displayed homeomorphism.
  sorry

/-- Helper for Theorem 78.3: attaching one disk along each enumerated boundary
circle produces a closed triangulable surface whose cap complements recover the
original surface. -/
private theorem Triangulation.existsCappedSurface_of_boundaryCircleData
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    [CompactSpace Y] [ConnectedSpace Y] {k : ℕ}
    (triangulation : Triangulation Y)
    (components : ConnectedComponents (∂Y) ≃ Fin k)
    (data : Surface.BoundaryCircleData components) :
    Nonempty (Surface.CappedSurface Y k) := by
  -- The circle parametrizations specify the attaching maps.  A collar of the
  -- manifold boundary supplies the seam charts and the radial equivalence with
  -- the complement of the cap disks; coning the finite boundary subcomplexes
  -- extends the given triangulation across those disks.
  -- TODO: prove the boundary-collar disk-attachment theorem through a named
  -- adjunction-space interface (inclusions, seam charts, and cap complements).
  sorry

/-- Helper for Theorem 78.3: filling the enumerated polygonal boundary
components of a compact connected triangulated surface produces a compact
connected triangulable closed surface. -/
private theorem Triangulation.existsCappedSurface
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    [CompactSpace Y] [ConnectedSpace Y] {k : ℕ}
    (triangulation : Triangulation Y)
    (components : ConnectedComponents (∂Y) ≃ Fin k) :
    Nonempty (Surface.CappedSurface Y k) := by
  -- First give every boundary component circle coordinates using its compact
  -- connected one-manifold structure.
  obtain ⟨data⟩ := Surface.existsBoundaryCircleData components
  -- Attach the corresponding disks through the capping interface, which also
  -- records the complement homeomorphism needed by `IsWithHoles`.
  exact triangulation.existsCappedSurface_of_boundaryCircleData components data

/-- Helper for Theorem 78.3: a finite triangulation whose boundary components are
enumerated by `Fin k` admits a paired polygonal cap presentation, with the original
surface recovered by deleting the `k` cap disks. -/
private theorem Triangulation.existsPairedEdgePastingWithBoundaryCaps
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    [CompactSpace Y] [ConnectedSpace Y] {k : ℕ}
    (triangulation : Triangulation Y)
    (components : ConnectedComponents (∂Y) ≃ Fin k) :
    ∃ (n : ℕ) (S : Type) (poly : CyclicPolygon n) (pasting : poly.EdgePasting S),
      pasting.PairsEdges ∧ Surface.IsWithHoles Y pasting.Realization k := by
  -- First isolate all seam topology and cap triangulation in the capped-surface package.
  obtain ⟨capped⟩ := triangulation.existsCappedSurface components
  letI : TopologicalSpace capped.X := capped.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) capped.X := capped.chartedSpace
  letI : TopologicalManifold 2 capped.X := capped.topologicalManifold
  letI : CompactSpace capped.X := capped.compactSpace
  letI : ConnectedSpace capped.X := capped.connectedSpace
  -- Consolidate the closed capped triangulation into one paired polygon.
  obtain ⟨n, S, poly, pasting, hpairs, ⟨e⟩⟩ :=
    compactConnectedTriangulableSurface_homeomorphic_polygonalPasting
      capped.X capped.triangulable
  refine ⟨n, S, poly, pasting, hpairs, ?_⟩
  -- Transport the retained complement of the cap disks through that homeomorphism.
  exact (Surface.isWithHoles_congr_right e).mp capped.holes

/-- Helper for Theorem 78.3: capping all boundary components of a compact
triangulated surface yields a paired polygonal realization whose deleted cap
disks recover the original surface. -/
private theorem existsPairedEdgePastingWithHoles
    (Y : Type u) [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    [CompactSpace Y] [ConnectedSpace Y] (k : ℕ)
    (h_triangulable : Triangulable Y)
    (h_boundary : Cardinal.mk (ConnectedComponents (∂Y)) = k) :
    ∃ (n : ℕ) (S : Type) (poly : CyclicPolygon n) (pasting : poly.EdgePasting S),
      pasting.PairsEdges ∧ Surface.IsWithHoles Y pasting.Realization k := by
  -- Fix the finite triangulation and the exact indexing of its boundary cycles.
  obtain ⟨triangulation⟩ := (triangulable_iff Y).mp h_triangulable
  obtain ⟨components⟩ := boundaryComponentsEquivFin Y k h_boundary
  -- Route correction: construct the capped surface from the stabilized boundary cycles;
  -- polygon consolidation can then be delegated to the now-available Theorem 78.2 API.
  exact triangulation.existsPairedEdgePastingWithBoundaryCaps components

/-- Theorem 78.3. A compact connected triangulable topological `2`-manifold with
boundary having exactly `k` components is homeomorphic to a sphere, a positive-fold
torus, or a positive-fold projective plane with `k` holes. -/
theorem compactConnectedTriangulableSurfaceWithBoundary_classification
    (Y : Type u) [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y] [SecondCountableTopology Y]
    [CompactSpace Y] [ConnectedSpace Y] (k : ℕ)
    (h_triangulable : Triangulable Y)
    (h_boundary : Cardinal.mk (ConnectedComponents (∂Y)) = k) :
    Surface.IsWithHoles Y (StandardSphere 2) k ∨
      (∃ (n : ℕ) (hn : 0 < n),
        Surface.IsWithHoles Y (OrientableSurfacePresentation.nFoldTorus n hn) k) ∨
      Surface.IsWithHoles Y RealProjectivePlane k ∨
      ∃ (m : ℕ) (hm : 1 < m),
        Surface.IsWithHoles Y
          (NonorientableSurfacePresentation.mFoldProjectivePlane m hm) k := by
  -- Present the capped surface by one paired polygon while retaining its cap complements.
  obtain ⟨n, S, poly, pasting, hpairs, hholes⟩ :=
    existsPairedEdgePastingWithHoles Y k h_triangulable h_boundary
  -- Classify the paired word and transport the retained hole complement in each case.
  rcases pairedEdgePastingClassification poly pasting hpairs with
    hsphere | htorus | hprojective | hhigher
  · obtain ⟨e⟩ := hsphere
    exact Or.inl ((Surface.isWithHoles_congr_right e).mp hholes)
  · obtain ⟨g, hg, ⟨e⟩⟩ := htorus
    have hstandard :
        Surface.IsWithHoles Y (OrientableSurfacePresentation.nFoldTorus g hg) k :=
      (Surface.isWithHoles_congr_right e).mp hholes
    exact Or.inr (Or.inl ⟨g, hg, hstandard⟩)
  · obtain ⟨e⟩ := hprojective
    have hstandard : Surface.IsWithHoles Y RealProjectivePlane k :=
      (Surface.isWithHoles_congr_right e).mp hholes
    exact Or.inr (Or.inr (Or.inl hstandard))
  · obtain ⟨m, hm, ⟨e⟩⟩ := hhigher
    have hstandard : Surface.IsWithHoles Y
        (NonorientableSurfacePresentation.mFoldProjectivePlane m hm) k :=
      (Surface.isWithHoles_congr_right e).mp hholes
    exact Or.inr (Or.inr (Or.inr ⟨m, hm, hstandard⟩))
