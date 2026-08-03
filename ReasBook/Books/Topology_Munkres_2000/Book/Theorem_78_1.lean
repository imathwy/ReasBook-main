module

public import Topology_Munkres_2000.Book.Definition_36_2
public import Topology_Munkres_2000.Book.Definition_78_1.Triangulation
public import Topology_Munkres_2000.Book.Theorem_62_3
public import Topology_Munkres_2000.Book.Theorem_78_1.EdgePairing
public import Topology_Munkres_2000.Book.Theorem_78_1.OpenEdgeCollar
public import Topology_Munkres_2000.Book.Theorem_78_1.TrianglePresentation
public import Topology_Munkres_2000.Book.Theorem_78_1.VertexStar

import all Topology_Munkres_2000.Book.Definition_78_1.Triangulation
import all Topology_Munkres_2000.Book.Theorem_74_1
import all Topology_Munkres_2000.Book.Theorem_78_1.TrianglePresentation

public section

universe u

/-- Helper for Theorem 78.1: the relative interior of a curved edge is the
vertex-free chart image of the interior of its model face. -/
private def CurvedTriangle.openEdge
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) : Set X :=
  ((fun y : triangle.model.closedInterior ↦ (triangle.chart y : X)) ''
      (Subtype.val ⁻¹' (triangle.model.faceOpposite i).interior)) \
    Set.range triangle.vertex

/-- Helper for Theorem 78.1: every relative open edge lies in its corresponding
closed curved edge. -/
private theorem CurvedTriangle.openEdge_subset_edge
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) : triangle.openEdge i ⊆ triangle.edge i := by
  -- Forget the vertex-free condition and enlarge face interior to closed interior.
  rw [CurvedTriangle.openEdge, triangle.edge_eq_chart_image_modelEdge i]
  rintro x ⟨⟨y, hyInterior, rfl⟩, _⟩
  refine ⟨y, ?_, rfl⟩
  rw [triangle.modelEdge_def i]
  exact (triangle.model.faceOpposite i).interior_subset_closedInterior hyInterior

/-- Helper for Theorem 78.1: no vertex of a triangle lies in the relative
interior of one of its opposite faces. -/
private theorem Affine.Simplex.faceOpposite_interior_ne_point
    {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (simplex : Affine.Simplex ℝ P 2) (i : Fin 3) {p : P}
    (hp : p ∈ (simplex.faceOpposite i).interior) (k : Fin 3) :
    p ≠ simplex.points k := by
  -- The opposite vertex misses the face span; the other two are face endpoints.
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

/-- Helper for Theorem 78.1: one half belongs to the unit interval. -/
private theorem half_mem_unitInterval : (1 / 2 : ℝ) ∈ unitInterval := by
  -- Both endpoint inequalities are numerical.
  norm_num

/-- Helper for Theorem 78.1: the fixed affine midpoint parameter used on every
triangulation edge. -/
private noncomputable def edgeMidpointParameter : unitInterval :=
  ⟨1 / 2, half_mem_unitInterval⟩

/-- Helper for Theorem 78.1: the fixed midpoint parameter is strictly between
the two edge endpoints. -/
private theorem edgeMidpointParameter_mem_Ioo :
    (edgeMidpointParameter : ℝ) ∈ Set.Ioo 0 1 := by
  -- The midpoint has real coordinate `1 / 2`.
  norm_num [edgeMidpointParameter]

/-- Helper for Theorem 78.1: the fixed affine midpoint belongs to the relative
open edge of every curved triangle. -/
private theorem CurvedTriangle.edgeMidpoint_mem_openEdge
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) :
    (triangle.chart (triangle.modelEdgePoint i edgeMidpointParameter) : X) ∈
      triangle.openEdge i := by
  have hInterior :
      (triangle.modelEdgePoint i edgeMidpointParameter :
          EuclideanSpace ℝ (Fin 2)) ∈
        (triangle.model.faceOpposite i).interior :=
    (triangle.modelEdgePoint_mem_faceOpposite_interior_iff
      i edgeMidpointParameter).mpr edgeMidpointParameter_mem_Ioo
  refine ⟨⟨triangle.modelEdgePoint i edgeMidpointParameter, hInterior, rfl⟩, ?_⟩
  -- A strictly interior face point cannot be one of the triangle vertices.
  rintro ⟨k, hk⟩
  have hchart :
      triangle.chart (triangle.modelEdgePoint i edgeMidpointParameter) =
        triangle.chart
          ⟨triangle.model.points k, triangle.model.point_mem_closedInterior k⟩ := by
    apply Subtype.ext
    unfold CurvedTriangle.vertex at hk
    exact hk.symm
  have hmodel := congrArg Subtype.val (triangle.chart.injective hchart)
  exact triangle.model.faceOpposite_interior_ne_point i hInterior k hmodel

/-- Helper for Theorem 78.1: compatible edge parametrizations send the fixed
midpoint of the first edge to the relative interior of the second edge. -/
private theorem CurvedTriangle.edgeMidpoint_mem_openEdge_of_edgesCompatible
    {X : Type u} [TopologicalSpace X] (first second : CurvedTriangle X)
    (i j : Fin 3) (hcompatible : first.EdgesCompatible second i j) :
    (first.chart (first.modelEdgePoint i edgeMidpointParameter) : X) ∈
      second.openEdge j := by
  obtain ⟨reverse, hreverse⟩ :=
    (first.edgesCompatible_iff second i j).mp hcompatible
  have hfixed :
      (if reverse then unitInterval.symm edgeMidpointParameter
        else edgeMidpointParameter) = edgeMidpointParameter := by
    -- Both possible orientations fix the affine midpoint.
    cases reverse
    · rfl
    · apply Subtype.ext
      simp only [if_pos rfl, unitInterval.coe_symm_eq]
      norm_num [edgeMidpointParameter]
  have hmidpoint := hreverse edgeMidpointParameter
  rw [hfixed] at hmidpoint
  -- Transport the second triangle's standard midpoint membership across the
  -- compatible parametrization equality.
  rw [hmidpoint]
  exact second.edgeMidpoint_mem_openEdge j

/-- Helper for Theorem 78.1: interiors of distinct opposite faces of a real
triangle are disjoint from the other closed face. -/
private theorem Affine.Simplex.disjoint_interior_faceOpposite_closedInterior_faceOpposite_of_ne
    {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (simplex : Affine.Simplex ℝ P 2) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (simplex.faceOpposite i).interior
      (simplex.faceOpposite j).closedInterior := by
  -- Compare the two faces through barycentric coordinates of the ambient simplex.
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
  unfold Affine.Simplex.faceOpposite at hpInterior
  have hpositive :=
    (simplex.affineCombination_mem_interior_face_iff_pos _ hsum).mp hpInterior
  have hjmem : j ∈ ({i}ᶜ : Finset (Fin 3)) := by
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact hij.symm
  exact (ne_of_gt (hpositive.1 j hjmem)) hjzero

/-- Helper for Theorem 78.1: the relative interior of one curved edge is
disjoint from every distinct closed edge of the same triangle. -/
private theorem CurvedTriangle.disjoint_openEdge_edge_of_ne
    {X : Type u} [TopologicalSpace X] (triangle : CurvedTriangle X)
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (triangle.openEdge i) (triangle.edge j) := by
  -- Pull a common point back through the injective chart to the two model faces.
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

/-- Helper for Theorem 78.1: the image of an injective continuous planar patch
in a topological surface contains an ambient neighborhood of each image point. -/
private theorem Topology.exists_openNeighborhood_subset_range_of_planarEmbedding
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y] [TopologicalManifold 2 Y]
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (f : U → Y) (hfContinuous : Continuous f)
    (hfInjective : Function.Injective f) (p : U) :
    ∃ V : Set Y, IsOpen V ∧ f p ∈ V ∧ V ⊆ Set.range f := by
  let chart : OpenPartialHomeomorph Y (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) (f p)
  have hfpSource : f p ∈ chart.source := by
    exact mem_chart_source (EuclideanSpace ℝ (Fin 2)) (f p)
  let domain : Set U := f ⁻¹' chart.source
  have hdomainOpen : IsOpen domain := by
    exact chart.open_source.preimage hfContinuous
  let inclusion : domain → EuclideanSpace ℝ (Fin 2) :=
    (Subtype.val : U → EuclideanSpace ℝ (Fin 2)) ∘
      (Subtype.val : domain → U)
  have hInclusionOpen : IsOpenEmbedding inclusion := by
    -- Both successive subtype inclusions have open range.
    dsimp only [inclusion]
    exact hU.isOpenEmbedding_subtypeVal.comp
      hdomainOpen.isOpenEmbedding_subtypeVal
  let domainEquiv : domain ≃ₜ Set.range inclusion :=
    hInclusionOpen.isEmbedding.toHomeomorph
  let coordinateMap : domain → EuclideanSpace ℝ (Fin 2) :=
    fun q ↦ chart (f q.1)
  have hCoordinateContinuous : Continuous coordinateMap := by
    -- Restrict the manifold chart to the part of the patch inside its source.
    exact chart.continuousOn.comp_continuous
      (hfContinuous.comp continuous_subtype_val) (fun q ↦ q.2)
  let planarMap : Set.range inclusion → EuclideanSpace ℝ (Fin 2) :=
    fun q ↦ coordinateMap (domainEquiv.symm q)
  have hPlanarContinuous : Continuous planarMap := by
    exact hCoordinateContinuous.comp domainEquiv.symm.continuous
  have hPlanarInjective : Function.Injective planarMap := by
    intro q r hqr
    apply domainEquiv.symm.injective
    apply Subtype.ext
    apply hfInjective
    apply chart.injOn
      (domainEquiv.symm q).2 (domainEquiv.symm r).2
    exact hqr
  have hPlanarRangeOpen : IsOpen (Set.range planarMap) :=
    (invarianceOfDomainPlane hInclusionOpen.isOpen_range planarMap
      hPlanarContinuous hPlanarInjective).isOpen_range
  let chartSubset : Set (EuclideanSpace ℝ (Fin 2)) := Set.range planarMap
  have hChartSubsetOpen : IsOpen chartSubset := hPlanarRangeOpen
  have hChartSubsetTarget : chartSubset ⊆ chart.target := by
    intro a ha
    obtain ⟨q, hq⟩ := ha
    let d : domain := domainEquiv.symm q
    have haCoordinate : a = coordinateMap d := hq.symm
    rw [haCoordinate]
    exact chart.map_source d.2
  have hImageOpen : IsOpen (chart.symm '' chartSubset) :=
    chart.isOpen_image_symm_of_subset_target hChartSubsetOpen hChartSubsetTarget
  refine ⟨chart.symm '' chartSubset, hImageOpen, ?_, ?_⟩
  · let pDomain : domain := ⟨p, hfpSource⟩
    let pRange : Set.range inclusion := domainEquiv pDomain
    have hpChartSubset : chart (f p) ∈ chartSubset := by
      refine ⟨pRange, ?_⟩
      dsimp only [planarMap, pRange, coordinateMap, pDomain]
      rw [domainEquiv.symm_apply_apply]
    exact ⟨chart (f p), hpChartSubset, chart.left_inv hfpSource⟩
  · rintro y ⟨a, ha, rfl⟩
    obtain ⟨q, hq⟩ := ha
    let d : domain := domainEquiv.symm q
    have haCoordinate : a = coordinateMap d := hq.symm
    refine ⟨d.1, ?_⟩
    rw [haCoordinate]
    exact (chart.left_inv d.2).symm

/-- Helper for Theorem 78.1: a relative open-edge point of one curved triangle
cannot have an ambient open neighborhood contained in that triangle. -/
private theorem CurvedTriangle.not_exists_openNeighborhood_subset_carrier_of_mem_openEdge
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangle : CurvedTriangle X) (i : Fin 3) {x : X}
    (hx : x ∈ triangle.openEdge i) :
    ¬ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ triangle.carrier := by
  rintro ⟨U, hUOpen, hxU, hUCarrier⟩
  obtain ⟨y, hyFaceInterior, hyChart⟩ := hx.1
  let surfaceChart : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hxSource : x ∈ surfaceChart.source := by
    exact mem_chart_source (EuclideanSpace ℝ (Fin 2)) x
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
  have hSymmMemCarrier (z : D) : surfaceChart.symm z.1 ∈ triangle.carrier :=
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
  have hToCarrierP : toCarrier p =
      ⟨x, hUCarrier hxU⟩ := by
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
  -- The selected point is simultaneously in the simplex interior and in the
  -- closed opposite face, contradicting their canonical disjointness.
  exact Set.disjoint_left.mp
    (triangle.model.disjoint_interior_closedInterior_faceOpposite i)
      hySimplexInterior
      ((triangle.model.faceOpposite i).interior_subset_closedInterior
        hyFaceInterior)

/-- Helper for Theorem 78.1: the triangle indices whose carriers contain a selected edge. -/
private def Triangulation.edgeIncidentTriangles {X : Type u} [TopologicalSpace X]
    (triangulation : Triangulation X) (edge : Fin triangulation.card × Fin 3) :
    Set (Fin triangulation.card) :=
  {i | (triangulation.triangle edge.1).edge edge.2 ⊆
    (triangulation.triangle i).carrier}

/-- Helper for Theorem 78.1: the set of triangles incident to an edge is finite. -/
private theorem Triangulation.edgeIncidentTriangles_finite
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) :
    (triangulation.edgeIncidentTriangles edge).Finite := by
  -- The incidence set is a subset of the finite triangulation index type.
  exact Set.toFinite _

/-- Helper for Theorem 78.1: an edge's owning triangle is incident to that edge. -/
private theorem Triangulation.edge_owner_mem_incidentTriangles
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) :
    edge.1 ∈ triangulation.edgeIncidentTriangles edge := by
  -- The defining incidence inclusion is the standard edge-to-carrier inclusion.
  exact (triangulation.triangle edge.1).edge_subset edge.2

/-- Helper for Theorem 78.1: every selected edge has positive incident-triangle rank. -/
private theorem Triangulation.edgeIncidentTriangles_ncard_pos
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) :
    0 < (triangulation.edgeIncidentTriangles edge).ncard := by
  -- Finiteness converts the owning triangle witness into positivity of `ncard`.
  rw [Set.ncard_pos (triangulation.edgeIncidentTriangles_finite edge)]
  exact ⟨edge.1, triangulation.edge_owner_mem_incidentTriangles edge⟩

/-- Helper for Theorem 78.1: at a point in the relative interior of a selected
edge, carrier membership is equivalent to membership in the edge-incidence set. -/
private theorem Triangulation.mem_carrier_iff_mem_edgeIncidentTriangles_of_mem_openEdge
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) (x : X)
    (hx : x ∈ (triangulation.triangle edge.1).openEdge edge.2)
    (r : Fin triangulation.card) :
    x ∈ (triangulation.triangle r).carrier ↔
      r ∈ triangulation.edgeIncidentTriangles edge := by
  constructor
  · intro hxr
    change (triangulation.triangle edge.1).edge edge.2 ⊆
      (triangulation.triangle r).carrier
    by_cases hir : edge.1 = r
    · subst r
      exact (triangulation.triangle edge.1).edge_subset edge.2
    have hxEdge : x ∈ (triangulation.triangle edge.1).edge edge.2 :=
      (triangulation.triangle edge.1).openEdge_subset_edge edge.2 hx
    have hxi : x ∈ (triangulation.triangle edge.1).carrier :=
      (triangulation.triangle edge.1).edge_subset edge.2 hxEdge
    have hxIntersection : x ∈
        (triangulation.triangle edge.1).carrier ∩
          (triangulation.triangle r).carrier := ⟨hxi, hxr⟩
    rcases triangulation.intersection_spec edge.1 r hir with
      hdisjoint | hvertex | hsharedEdge
    · exact False.elim (Set.disjoint_left.mp hdisjoint hxi hxr)
    · obtain ⟨vertexI, _, hintersection, _⟩ :=
        (CurvedTriangle.sharesVertex_iff _ _).mp hvertex
      rw [hintersection] at hxIntersection
      have hxvertex : x = (triangulation.triangle edge.1).vertex vertexI :=
        Set.mem_singleton_iff.mp hxIntersection
      exact False.elim (hx.2 ⟨vertexI, hxvertex.symm⟩)
    · obtain ⟨edgeI, _, hintersection, _⟩ :=
        (CurvedTriangle.sharesEdge_iff _ _).mp hsharedEdge
      have hxSharedEdge : x ∈ (triangulation.triangle edge.1).edge edgeI := by
        rw [← hintersection]
        exact hxIntersection
      have hedge : edgeI = edge.2 := by
        by_contra hne
        exact Set.disjoint_left.mp
          ((triangulation.triangle edge.1).disjoint_openEdge_edge_of_ne
            (Ne.symm hne)) hx hxSharedEdge
      subst edgeI
      -- The normalized intersection equation contains the whole selected edge.
      intro y hy
      have hyIntersection : y ∈
          (triangulation.triangle edge.1).carrier ∩
            (triangulation.triangle r).carrier := by
        rw [hintersection]
        exact hy
      exact hyIntersection.2
  · intro hr
    change (triangulation.triangle edge.1).edge edge.2 ⊆
      (triangulation.triangle r).carrier at hr
    -- An open-edge point lies on the corresponding closed edge.
    exact hr ((triangulation.triangle edge.1).openEdge_subset_edge edge.2 hx)

/-- Helper for Theorem 78.1: a distinct incident triangle meets the owner in
the selected edge and carries the compatible affine edge parameterization. -/
private theorem Triangulation.exists_compatibleSharedEdge_of_mem_edgeIncidentTriangles
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) (x : X)
    (hx : x ∈ (triangulation.triangle edge.1).openEdge edge.2)
    (r : Fin triangulation.card) (hir : edge.1 ≠ r)
    (hr : r ∈ triangulation.edgeIncidentTriangles edge) :
    ∃ edgeR : Fin 3,
      (triangulation.triangle edge.1).carrier ∩
          (triangulation.triangle r).carrier =
        (triangulation.triangle edge.1).edge edge.2 ∧
      (triangulation.triangle edge.1).carrier ∩
          (triangulation.triangle r).carrier =
        (triangulation.triangle r).edge edgeR ∧
      (triangulation.triangle edge.1).EdgesCompatible
        (triangulation.triangle r) edge.2 edgeR := by
  have hxEdge : x ∈ (triangulation.triangle edge.1).edge edge.2 :=
    (triangulation.triangle edge.1).openEdge_subset_edge edge.2 hx
  have hxi : x ∈ (triangulation.triangle edge.1).carrier :=
    (triangulation.triangle edge.1).edge_subset edge.2 hxEdge
  have hxr : x ∈ (triangulation.triangle r).carrier :=
    (triangulation.mem_carrier_iff_mem_edgeIncidentTriangles_of_mem_openEdge
      edge x hx r).mpr hr
  have hxIntersection : x ∈
      (triangulation.triangle edge.1).carrier ∩
        (triangulation.triangle r).carrier := ⟨hxi, hxr⟩
  -- The common open-edge point excludes disjoint and vertex-only intersections.
  rcases triangulation.intersection_spec edge.1 r hir with
    hdisjoint | hvertex | hsharedEdge
  · exact False.elim (Set.disjoint_left.mp hdisjoint hxi hxr)
  · obtain ⟨vertexI, _, hintersection, _⟩ :=
      (CurvedTriangle.sharesVertex_iff _ _).mp hvertex
    rw [hintersection] at hxIntersection
    have hxvertex : x = (triangulation.triangle edge.1).vertex vertexI :=
      Set.mem_singleton_iff.mp hxIntersection
    exact False.elim (hx.2 ⟨vertexI, hxvertex.symm⟩)
  · obtain ⟨edgeI, edgeR, hintersectionI, hedgeEq⟩ :=
      (CurvedTriangle.sharesEdge_iff _ _).mp hsharedEdge
    have hxSharedEdge : x ∈ (triangulation.triangle edge.1).edge edgeI := by
      rw [← hintersectionI]
      exact hxIntersection
    have hedgeI : edgeI = edge.2 := by
      by_contra hne
      exact Set.disjoint_left.mp
        ((triangulation.triangle edge.1).disjoint_openEdge_edge_of_ne
          (Ne.symm hne)) hx hxSharedEdge
    subst edgeI
    have hintersectionR :
        (triangulation.triangle edge.1).carrier ∩
            (triangulation.triangle r).carrier =
          (triangulation.triangle r).edge edgeR :=
      hintersectionI.trans hedgeEq
    refine ⟨edgeR, hintersectionI, hintersectionR, ?_⟩
    exact triangulation.sharedEdgeCompatible edge.1 r hir edge.2 edgeR
      hintersectionI hintersectionR

/-- Helper for Theorem 78.1: at most two triangles of a surface triangulation
can contain any selected edge. -/
private theorem Triangulation.edgeIncidentTriangles_ncard_le_two
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) :
    (triangulation.edgeIncidentTriangles edge).ncard ≤ 2 := by
  classical
  let x : X :=
    triangulation.triangle edge.1 |>.chart
      ((triangulation.triangle edge.1).modelEdgePoint edge.2 edgeMidpointParameter)
  have hxOpen : x ∈ (triangulation.triangle edge.1).openEdge edge.2 :=
    (triangulation.triangle edge.1).edgeMidpoint_mem_openEdge edge.2
  by_contra hle
  have hgt : 2 < (triangulation.edgeIncidentTriangles edge).ncard :=
    Nat.lt_of_not_ge hle
  have hmatesCard :
      1 < (triangulation.edgeIncidentTriangles edge \ {edge.1}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem
      (triangulation.edge_owner_mem_incidentTriangles edge)]
    omega
  have hmatesFinite :
      (triangulation.edgeIncidentTriangles edge \ {edge.1}).Finite :=
    (triangulation.edgeIncidentTriangles_finite edge).sdiff
  obtain ⟨second, hsecondMate, third, hthirdMate, hsecondThird⟩ :=
    (Set.one_lt_ncard hmatesFinite).mp hmatesCard
  have hsecondIncident : second ∈ triangulation.edgeIncidentTriangles edge :=
    hsecondMate.1
  have hthirdIncident : third ∈ triangulation.edgeIncidentTriangles edge :=
    hthirdMate.1
  have hsecondOwner : second ≠ edge.1 := by
    simpa only [Set.mem_singleton_iff] using hsecondMate.2
  have hthirdOwner : third ≠ edge.1 := by
    simpa only [Set.mem_singleton_iff] using hthirdMate.2
  obtain ⟨edgeSecond, hOwnerSecondFirst, hOwnerSecondSecond,
      hOwnerSecondCompatible⟩ :=
    triangulation.exists_compatibleSharedEdge_of_mem_edgeIncidentTriangles
      edge x hxOpen second hsecondOwner.symm hsecondIncident
  obtain ⟨edgeThird, hOwnerThirdFirst, hOwnerThirdThird,
      hOwnerThirdCompatible⟩ :=
    triangulation.exists_compatibleSharedEdge_of_mem_edgeIncidentTriangles
      edge x hxOpen third hthirdOwner.symm hthirdIncident
  have hxSecondOpen : x ∈
      (triangulation.triangle second).openEdge edgeSecond :=
    (triangulation.triangle edge.1).edgeMidpoint_mem_openEdge_of_edgesCompatible
      (triangulation.triangle second) edge.2 edgeSecond hOwnerSecondCompatible
  let secondEdge : Fin triangulation.card × Fin 3 := ⟨second, edgeSecond⟩
  have hSecondEdgeEq :
      (triangulation.triangle second).edge edgeSecond =
        (triangulation.triangle edge.1).edge edge.2 :=
    hOwnerSecondSecond.symm.trans hOwnerSecondFirst
  have hthirdIncidentToSecond :
      third ∈ triangulation.edgeIncidentTriangles secondEdge := by
    change (triangulation.triangle second).edge edgeSecond ⊆
      (triangulation.triangle third).carrier
    rw [hSecondEdgeEq]
    exact hthirdIncident
  obtain ⟨_, hSecondThirdFirst, _, _⟩ :=
    triangulation.exists_compatibleSharedEdge_of_mem_edgeIncidentTriangles
      secondEdge x hxSecondOpen third hsecondThird hthirdIncidentToSecond
  obtain ⟨USecond, hUSecondOpen, pSecond, fSecond, hfSecondContinuous,
      hfSecondInjective, hfSecondPoint, hfSecondRange⟩ :=
    (triangulation.triangle edge.1).existsPlanarEmbeddingAtOfCompatibleSharedEdge
      (triangulation.triangle second) edge.2 edgeSecond hOwnerSecondFirst
        hOwnerSecondSecond hOwnerSecondCompatible edgeMidpointParameter
          edgeMidpointParameter_mem_Ioo
  obtain ⟨VSecond, hVSecondOpen, hVSecondPoint, hVSecondRange⟩ :=
    Topology.exists_openNeighborhood_subset_range_of_planarEmbedding
      hUSecondOpen fSecond hfSecondContinuous hfSecondInjective pSecond
  have hxVSecond : x ∈ VSecond := by
    rwa [hfSecondPoint] at hVSecondPoint
  obtain ⟨UThird, hUThirdOpen, pThird, fThird, hfThirdContinuous,
      hfThirdInjective, hfThirdPoint, hfThirdRange⟩ :=
    (triangulation.triangle edge.1).existsPlanarEmbeddingAtOfCompatibleSharedEdge
      (triangulation.triangle third) edge.2 edgeThird hOwnerThirdFirst
        hOwnerThirdThird hOwnerThirdCompatible edgeMidpointParameter
          edgeMidpointParameter_mem_Ioo
  obtain ⟨VThird, hVThirdOpen, hVThirdPoint, hVThirdRange⟩ :=
    Topology.exists_openNeighborhood_subset_range_of_planarEmbedding
      hUThirdOpen fThird hfThirdContinuous hfThirdInjective pThird
  have hxVThird : x ∈ VThird := by
    rwa [hfThirdPoint] at hVThirdPoint
  have hIntersectionSubsetOwner :
      VSecond ∩ VThird ⊆ (triangulation.triangle edge.1).carrier := by
    rintro y ⟨hySecondNeighborhood, hyThirdNeighborhood⟩
    have hyOwnerSecond :=
      hfSecondRange (hVSecondRange hySecondNeighborhood)
    have hyOwnerThird := hfThirdRange (hVThirdRange hyThirdNeighborhood)
    rcases hyOwnerSecond with hyOwner | hySecond
    · exact hyOwner
    rcases hyOwnerThird with hyOwner | hyThird
    · exact hyOwner
    have hySecondThird : y ∈
        (triangulation.triangle second).carrier ∩
          (triangulation.triangle third).carrier := ⟨hySecond, hyThird⟩
    have hySecondEdge :
        y ∈ (triangulation.triangle second).edge edgeSecond := by
      rwa [← hSecondThirdFirst]
    rw [hSecondEdgeEq] at hySecondEdge
    exact (triangulation.triangle edge.1).edge_subset edge.2 hySecondEdge
  -- Two distinct collars would therefore create a forbidden one-page ambient
  -- neighborhood at the selected midpoint.
  exact (triangulation.triangle edge.1
    |>.not_exists_openNeighborhood_subset_carrier_of_mem_openEdge edge.2 hxOpen)
      ⟨VSecond ∩ VThird, hVSecondOpen.inter hVThirdOpen,
        ⟨hxVSecond, hxVThird⟩, hIntersectionSubsetOwner⟩

/-- Helper for Theorem 78.1: every selected edge of a boundaryless surface
triangulation is contained in exactly two triangles. -/
private theorem Triangulation.edgeIncidentTriangles_ncard_eq_two
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) :
    (triangulation.edgeIncidentTriangles edge).ncard = 2 := by
  classical
  have hpositive := triangulation.edgeIncidentTriangles_ncard_pos edge
  have hupper := triangulation.edgeIncidentTriangles_ncard_le_two edge
  have hnotOne : (triangulation.edgeIncidentTriangles edge).ncard ≠ 1 := by
    intro hcard
    have hIncidentEq : triangulation.edgeIncidentTriangles edge = {edge.1} := by
      obtain ⟨only, honly⟩ := Set.ncard_eq_one.mp hcard
      have howner : edge.1 = only := by
        rw [honly] at hpositive
        simpa only [Set.ncard_singleton] using
          Set.mem_singleton_iff.mp
            (honly ▸ triangulation.edge_owner_mem_incidentTriangles edge)
      rwa [howner]
    let x : X :=
      triangulation.triangle edge.1 |>.chart
        ((triangulation.triangle edge.1).modelEdgePoint edge.2 edgeMidpointParameter)
    have hxOpen : x ∈ (triangulation.triangle edge.1).openEdge edge.2 :=
      (triangulation.triangle edge.1).edgeMidpoint_mem_openEdge edge.2
    let excluded : Set X :=
      ⋃ r : {r : Fin triangulation.card //
          r ∉ triangulation.edgeIncidentTriangles edge},
        (triangulation.triangle r.1).carrier
    have hExcludedClosed : IsClosed excluded := by
      dsimp only [excluded]
      exact isClosed_iUnion_of_finite fun r ↦
        (triangulation.triangle r.1).isClosed_carrier
    have hxExcluded : x ∉ excluded := by
      intro hxExcluded
      obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hxExcluded
      have hrIncident : r.1 ∈ triangulation.edgeIncidentTriangles edge :=
        (triangulation.mem_carrier_iff_mem_edgeIncidentTriangles_of_mem_openEdge
          edge x hxOpen r.1).mp hxr
      exact r.2 hrIncident
    have hComplementSubsetOwner :
        excludedᶜ ⊆ (triangulation.triangle edge.1).carrier := by
      intro y hyExcluded
      have hyCover : y ∈ ⋃ r, (triangulation.triangle r).carrier := by
        rw [triangulation.cover]
        exact Set.mem_univ y
      obtain ⟨r, hyr⟩ := Set.mem_iUnion.mp hyCover
      by_cases hr : r ∈ triangulation.edgeIncidentTriangles edge
      · have hre : r = edge.1 := by
          exact Set.mem_singleton_iff.mp (hIncidentEq ▸ hr)
        rwa [hre] at hyr
      · exact False.elim
          (hyExcluded (Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hyr⟩))
    -- If the owner were the sole incident triangle, deleting every competing
    -- carrier would leave a forbidden ambient neighborhood inside that owner.
    exact (triangulation.triangle edge.1
      |>.not_exists_openNeighborhood_subset_carrier_of_mem_openEdge edge.2 hxOpen)
        ⟨excludedᶜ, hExcludedClosed.isOpen_compl, hxExcluded,
          hComplementSubsetOwner⟩
  omega

/-- Helper for Theorem 78.1: every geometric edge occurrence has a unique
distinct occurrence representing the same closed curved edge. -/
private theorem Triangulation.existsUniqueGeometricEdgeMate
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) :
    ∃! mate : Fin triangulation.card × Fin 3,
      mate ≠ edge ∧
        (triangulation.triangle mate.1).edge mate.2 =
          (triangulation.triangle edge.1).edge edge.2 := by
  classical
  let x : X :=
    triangulation.triangle edge.1 |>.chart
      ((triangulation.triangle edge.1).modelEdgePoint edge.2 edgeMidpointParameter)
  have hxOpen : x ∈ (triangulation.triangle edge.1).openEdge edge.2 :=
    (triangulation.triangle edge.1).edgeMidpoint_mem_openEdge edge.2
  have hremainingCard :
      (triangulation.edgeIncidentTriangles edge \ {edge.1}).ncard = 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem
      (triangulation.edge_owner_mem_incidentTriangles edge),
      triangulation.edgeIncidentTriangles_ncard_eq_two edge]
  obtain ⟨mateTriangle, hremaining⟩ := Set.ncard_eq_one.mp hremainingCard
  have hmateIncident : mateTriangle ∈ triangulation.edgeIncidentTriangles edge := by
    have hmember : mateTriangle ∈
        triangulation.edgeIncidentTriangles edge \ {edge.1} := by
      rw [hremaining]
      exact Set.mem_singleton mateTriangle
    exact hmember.1
  have hmateTriangleNe : mateTriangle ≠ edge.1 := by
    have hmember : mateTriangle ∈
        triangulation.edgeIncidentTriangles edge \ {edge.1} := by
      rw [hremaining]
      exact Set.mem_singleton mateTriangle
    simpa only [Set.mem_singleton_iff] using hmember.2
  obtain ⟨mateEdge, hintersectionOwner, hintersectionMate, hcompatible⟩ :=
    triangulation.exists_compatibleSharedEdge_of_mem_edgeIncidentTriangles
      edge x hxOpen mateTriangle hmateTriangleNe.symm hmateIncident
  have hmateEdgeEq :
      (triangulation.triangle mateTriangle).edge mateEdge =
        (triangulation.triangle edge.1).edge edge.2 :=
    hintersectionMate.symm.trans hintersectionOwner
  refine ⟨⟨mateTriangle, mateEdge⟩, ?_, ?_⟩
  · -- The remaining incident triangle is different from the owner, and its
    -- selected edge is precisely the original geometric edge.
    exact ⟨fun heq ↦ hmateTriangleNe (congrArg Prod.fst heq), hmateEdgeEq⟩
  · rintro ⟨otherTriangle, otherEdge⟩ ⟨hotherNe, hotherEdgeEq⟩
    have hotherIncident :
        otherTriangle ∈ triangulation.edgeIncidentTriangles edge := by
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
        triangulation.edgeIncidentTriangles edge \ {edge.1} := by
      exact ⟨hotherIncident, by simpa only [Set.mem_singleton_iff]⟩
    have htriangleEq : otherTriangle = mateTriangle := by
      rw [hremaining] at hotherRemaining
      exact Set.mem_singleton_iff.mp hotherRemaining
    subst otherTriangle
    have hxMateOpen : x ∈
        (triangulation.triangle mateTriangle).openEdge mateEdge :=
      (triangulation.triangle edge.1).edgeMidpoint_mem_openEdge_of_edgesCompatible
        (triangulation.triangle mateTriangle) edge.2 mateEdge hcompatible
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

/-- Helper for Theorem 78.1: two distinct occurrences of the same geometric
edge carry compatible affine parametrizations. -/
private theorem Triangulation.edgesCompatible_of_geometricEdge_eq
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangulation : Triangulation X)
    (first second : Fin triangulation.card × Fin 3)
    (hne : second ≠ first)
    (hedgeEq : (triangulation.triangle second.1).edge second.2 =
      (triangulation.triangle first.1).edge first.2) :
    (triangulation.triangle first.1).EdgesCompatible
      (triangulation.triangle second.1) first.2 second.2 := by
  let x : X :=
    triangulation.triangle first.1 |>.chart
      ((triangulation.triangle first.1).modelEdgePoint first.2 edgeMidpointParameter)
  have hxOpen : x ∈ (triangulation.triangle first.1).openEdge first.2 :=
    (triangulation.triangle first.1).edgeMidpoint_mem_openEdge first.2
  have htriangleNe : first.1 ≠ second.1 := by
    intro htriangle
    have hedgeIndex : first.2 = second.2 := by
      by_contra hedgeNe
      have hxSecond : x ∈
          (triangulation.triangle first.1).edge second.2 := by
        rw [htriangle, hedgeEq]
        exact (triangulation.triangle first.1).openEdge_subset_edge first.2 hxOpen
      exact Set.disjoint_left.mp
        ((triangulation.triangle first.1).disjoint_openEdge_edge_of_ne hedgeNe)
          hxOpen hxSecond
    apply hne
    exact Prod.ext htriangle.symm hedgeIndex.symm
  have hsecondIncident :
      second.1 ∈ triangulation.edgeIncidentTriangles first := by
    change (triangulation.triangle first.1).edge first.2 ⊆
      (triangulation.triangle second.1).carrier
    rw [← hedgeEq]
    exact (triangulation.triangle second.1).edge_subset second.2
  obtain ⟨edgeSecond, _, _, hcompatible⟩ :=
    triangulation.exists_compatibleSharedEdge_of_mem_edgeIncidentTriangles
      first x hxOpen second.1 htriangleNe hsecondIncident
  have hxSecondOpen : x ∈
      (triangulation.triangle second.1).openEdge edgeSecond :=
    (triangulation.triangle first.1).edgeMidpoint_mem_openEdge_of_edgesCompatible
      (triangulation.triangle second.1) first.2 edgeSecond hcompatible
  have hedgeSecond : edgeSecond = second.2 := by
    by_contra hedgeNe
    have hxSecond : x ∈
        (triangulation.triangle second.1).edge second.2 := by
      rw [hedgeEq]
      exact (triangulation.triangle first.1).openEdge_subset_edge first.2 hxOpen
    exact Set.disjoint_left.mp
      ((triangulation.triangle second.1).disjoint_openEdge_edge_of_ne hedgeNe)
        hxSecondOpen hxSecond
  -- Uniqueness of the edge index in the second triangle puts the compatibility
  -- statement into the requested occurrence-level form.
  subst edgeSecond
  exact hcompatible

/-- Helper for Theorem 78.1: the ambient point at parameter `t` on a selected
triangulation edge occurrence. -/
private noncomputable def Triangulation.edgePoint
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) (t : unitInterval) : X :=
  triangulation.triangle edge.1 |>.chart
    ((triangulation.triangle edge.1).modelEdgePoint edge.2 t)

/-- Helper for Theorem 78.1: the canonical occurrence-level data used to
pair every triangulation edge with its unique affine-compatible mate. -/
private structure Triangulation.EdgePairing
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X) where
  /-- The other occurrence of a geometric triangulation edge. -/
  mate : (Fin triangulation.card × Fin 3) →
    Fin triangulation.card × Fin 3
  /-- No edge occurrence is paired with itself. -/
  mate_ne (edge) : mate edge ≠ edge
  /-- Paired occurrences represent the same closed curved edge. -/
  edge_eq (edge) :
    (triangulation.triangle (mate edge).1).edge (mate edge).2 =
      (triangulation.triangle edge.1).edge edge.2
  /-- Taking the mate twice returns the original occurrence. -/
  mate_involutive : Function.Involutive mate
  /-- Whether the mate parametrization reverses the unit interval. -/
  reverse : (Fin triangulation.card × Fin 3) → Bool
  /-- Paired edge parametrizations agree after the selected reversal. -/
  parameter_eq (edge) (t : unitInterval) :
    triangulation.edgePoint edge t =
      triangulation.edgePoint (mate edge)
        (if reverse edge then unitInterval.symm t else t)
  /-- Equality of geometric edges is exactly equality or mating. -/
  edge_eq_iff (first second) :
    (triangulation.triangle second.1).edge second.2 =
        (triangulation.triangle first.1).edge first.2 ↔
      second = first ∨ second = mate first

/-- Helper for Theorem 78.1: exact two-triangle incidence canonically supplies
a fixed-point-free involutive edge pairing with compatible orientations. -/
private theorem Triangulation.existsEdgePairing
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    (triangulation : Triangulation X) : Nonempty triangulation.EdgePairing := by
  classical
  let mate : (Fin triangulation.card × Fin 3) →
      Fin triangulation.card × Fin 3 :=
    fun edge ↦ Classical.choose (triangulation.existsUniqueGeometricEdgeMate edge)
  have hmateProperty (edge : Fin triangulation.card × Fin 3) :
      mate edge ≠ edge ∧
        (triangulation.triangle (mate edge).1).edge (mate edge).2 =
          (triangulation.triangle edge.1).edge edge.2 :=
    (Classical.choose_spec (triangulation.existsUniqueGeometricEdgeMate edge)).1
  have hmateUnique (edge other : Fin triangulation.card × Fin 3)
      (hother : other ≠ edge ∧
        (triangulation.triangle other.1).edge other.2 =
          (triangulation.triangle edge.1).edge edge.2) :
      other = mate edge :=
    (Classical.choose_spec
      (triangulation.existsUniqueGeometricEdgeMate edge)).2 other hother
  have hcompatible (edge : Fin triangulation.card × Fin 3) :
      (triangulation.triangle edge.1).EdgesCompatible
        (triangulation.triangle (mate edge).1) edge.2 (mate edge).2 :=
    triangulation.edgesCompatible_of_geometricEdge_eq edge (mate edge)
      (hmateProperty edge).1 (hmateProperty edge).2
  let reverse : (Fin triangulation.card × Fin 3) → Bool :=
    fun edge ↦ Classical.choose
      ((triangulation.triangle edge.1).edgesCompatible_iff
        (triangulation.triangle (mate edge).1) edge.2 (mate edge).2 |>.mp
          (hcompatible edge))
  have hparameter (edge : Fin triangulation.card × Fin 3) (t : unitInterval) :
      triangulation.edgePoint edge t =
        triangulation.edgePoint (mate edge)
          (if reverse edge then unitInterval.symm t else t) := by
    -- Unfold the stable occurrence-level spelling once to consume compatibility.
    unfold Triangulation.edgePoint
    exact
    Classical.choose_spec
      ((triangulation.triangle edge.1).edgesCompatible_iff
        (triangulation.triangle (mate edge).1) edge.2 (mate edge).2 |>.mp
          (hcompatible edge)) t
  refine ⟨{
    mate := mate
    mate_ne := fun edge ↦ (hmateProperty edge).1
    edge_eq := fun edge ↦ (hmateProperty edge).2
    mate_involutive := ?_
    reverse := reverse
    parameter_eq := hparameter
    edge_eq_iff := ?_ }⟩
  · intro edge
    -- The original occurrence is the unique distinct representative of the
    -- mate's geometric edge.
    exact (hmateUnique (mate edge) edge
      ⟨(hmateProperty edge).1.symm, (hmateProperty edge).2.symm⟩).symm
  · intro first second
    constructor
    · intro hedge
      by_cases heq : second = first
      · exact Or.inl heq
      · exact Or.inr (hmateUnique first second ⟨heq, hedge⟩)
    · rintro (rfl | rfl)
      · rfl
      · exact (hmateProperty first).2

/-- Helper for Theorem 78.1: the finite rank of a triangulation edge
occurrence orders triangle indices first and edge indices second. -/
private def Triangulation.edgeOccurrenceRank
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X)
    (edge : Fin triangulation.card × Fin 3) : ℕ :=
  edge.1.1 * 3 + edge.2.1

/-- Helper for Theorem 78.1: the finite occurrence rank distinguishes all
triangle-edge pairs. -/
private theorem Triangulation.edgeOccurrenceRank_injective
    {X : Type u} [TopologicalSpace X] (triangulation : Triangulation X) :
    Function.Injective triangulation.edgeOccurrenceRank := by
  intro first second hrank
  apply Prod.ext
  · apply Fin.ext
    dsimp only [edgeOccurrenceRank] at hrank
    omega
  · apply Fin.ext
    dsimp only [edgeOccurrenceRank] at hrank
    omega

/-- Helper for Theorem 78.1: orient an edge occurrence by choosing the
lower-ranked member of its two-element orbit as the positive representative. -/
private def Triangulation.EdgePairing.direction
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (edge : Fin triangulation.card × Fin 3) : Bool :=
  if triangulation.edgeOccurrenceRank edge <
      triangulation.edgeOccurrenceRank (pairing.mate edge) then true
  else !(pairing.reverse (pairing.mate edge))

/-- Helper for Theorem 78.1: the orbit label of an edge occurrence consists
exactly of it and its mate. -/
private def Triangulation.EdgePairing.orbitLabel
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (edge : Fin triangulation.card × Fin 3) :
    Finset (Fin triangulation.card × Fin 3) :=
  {edge, pairing.mate edge}

/-- Helper for Theorem 78.1: equality of two edge-orbit labels means equality
of the occurrences or passage to the unique mate. -/
private theorem Triangulation.EdgePairing.orbitLabel_eq_iff
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (first second : Fin triangulation.card × Fin 3) :
    pairing.orbitLabel second = pairing.orbitLabel first ↔
      second = first ∨ second = pairing.mate first := by
  constructor
  · intro hlabel
    -- Membership of `second` in its own orbit transfers across label equality.
    have hmem : second ∈ pairing.orbitLabel first := by
      rw [← hlabel]
      simp only [orbitLabel, Finset.mem_insert, Finset.mem_singleton, true_or]
    simpa only [orbitLabel, Finset.mem_insert, Finset.mem_singleton] using hmem
  · rintro (rfl | rfl)
    · rfl
    · -- Involutivity makes the mate's two-element orbit the same unordered pair.
      apply Finset.ext
      intro edge
      simp only [orbitLabel, Finset.mem_insert, Finset.mem_singleton]
      rw [pairing.mate_involutive first]
      tauto

/-- Helper for Theorem 78.1: the orbit directions make the two mate
parameterizations agree at a common presentation parameter. -/
private theorem Triangulation.EdgePairing.edgePoint_direction_eq
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (edge : Fin triangulation.card × Fin 3) (t : unitInterval) :
    triangulation.edgePoint edge
        (if pairing.direction edge then t else unitInterval.symm t) =
      triangulation.edgePoint (pairing.mate edge)
        (if pairing.direction (pairing.mate edge) then t
          else unitInterval.symm t) := by
  by_cases hsmall : triangulation.edgeOccurrenceRank edge <
      triangulation.edgeOccurrenceRank (pairing.mate edge)
  · have hnotBack : ¬triangulation.edgeOccurrenceRank (pairing.mate edge) <
        triangulation.edgeOccurrenceRank edge :=
      (not_lt_of_ge (le_of_lt hsmall))
    rw [direction, if_pos hsmall, direction,
      pairing.mate_involutive, if_neg hnotBack]
    cases hreverse : pairing.reverse edge
    · simpa only [Bool.true_eq, hreverse, Bool.false_eq_true, if_false,
        Bool.not_false, if_true] using pairing.parameter_eq edge t
    · simpa only [Bool.true_eq, hreverse, if_true, Bool.not_true,
        Bool.false_eq_true, if_false] using pairing.parameter_eq edge t
  · have hmateSmall : triangulation.edgeOccurrenceRank (pairing.mate edge) <
        triangulation.edgeOccurrenceRank edge := by
      have hne : triangulation.edgeOccurrenceRank (pairing.mate edge) ≠
          triangulation.edgeOccurrenceRank edge := by
        intro heq
        exact pairing.mate_ne edge
          (triangulation.edgeOccurrenceRank_injective heq)
      omega
    rw [direction, if_neg hsmall, direction, pairing.mate_involutive,
      if_pos hmateSmall]
    have hparameter :=
      (pairing.parameter_eq (pairing.mate edge) t).symm
    rw [pairing.mate_involutive edge] at hparameter
    cases hreverse : pairing.reverse (pairing.mate edge)
    · simpa only [Bool.true_eq, hreverse, Bool.not_false, if_true,
        Bool.false_eq_true, if_false] using hparameter
    · simpa only [Bool.true_eq, hreverse, Bool.not_true, Bool.false_eq_true,
        if_false, if_true] using hparameter

/-- Helper for Theorem 78.1: presentation edge occurrences are canonically
equivalent to geometric triangulation edge occurrences. -/
private noncomputable def Triangulation.EdgePairing.presentationEdgeEquiv
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (_pairing : triangulation.EdgePairing) :
    (Σ _ : Fin triangulation.card, Fin 3) ≃
      (Fin triangulation.card × Fin 3) :=
  (Equiv.sigmaEquivProd _ _).trans
    (Equiv.prodCongr (Equiv.refl _) Theorem78_1.presentationEdgeEquiv)

/-- Helper for Theorem 78.1: the occurrence equivalence preserves the triangle
index and applies the fixed cyclic-to-model edge equivalence. -/
private theorem Triangulation.EdgePairing.presentationEdgeEquiv_apply
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (i : Fin triangulation.card) (edge : Fin 3) :
    pairing.presentationEdgeEquiv ⟨i, edge⟩ =
      (i, Theorem78_1.presentationEdgeToModelEdge edge) := by
  -- Both equivalences act componentwise and leave the triangle index fixed.
  unfold Triangulation.EdgePairing.presentationEdgeEquiv
  rfl

/-- Helper for Theorem 78.1: the fixed cyclic triangles, orbit labels, and
coherent directions form the polygonal presentation attached to a pairing. -/
private noncomputable abbrev Triangulation.EdgePairing.presentation
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) :
    PolygonalPasting (Fin triangulation.card)
      (Finset (Fin triangulation.card × Fin 3)) where
  sides _ := 3
  polygon _ := Theorem78_1.presentationTriangle
  pasting i := Theorem78_1.presentationDirectedEdgePasting
    (fun edge ↦ pairing.orbitLabel
      (pairing.presentationEdgeEquiv ⟨i, edge⟩))
    (fun edge ↦ pairing.direction
      (pairing.presentationEdgeEquiv ⟨i, edge⟩))

/-- Helper for Theorem 78.1: the canonical presentation's edge label is the
mate orbit of the corresponding geometric edge occurrence. -/
private theorem Triangulation.EdgePairing.presentation_label
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (i : Fin triangulation.card) (edge : Fin 3) :
    (pairing.presentation.pasting i).label edge =
      pairing.orbitLabel (pairing.presentationEdgeEquiv ⟨i, edge⟩) := by
  -- Project the label field through the direction-aware edge-pasting API.
  exact Theorem78_1.presentationDirectedEdgePasting_label _ _ edge

/-- Helper for Theorem 78.1: every orbit label in the canonical presentation
has exactly the unique other edge occurrence supplied by the pairing. -/
private theorem Triangulation.EdgePairing.presentation_pairsEdges
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) :
    pairing.presentation.PairsEdges := by
  rw [PolygonalPasting.pairsEdges_iff]
  intro i edge
  let current := pairing.presentationEdgeEquiv ⟨i, edge⟩
  let mateSource := pairing.presentationEdgeEquiv.symm (pairing.mate current)
  refine ⟨mateSource, ?_, ?_⟩
  · constructor
    · -- Injectivity of the edge equivalence reduces distinctness to `mate_ne`.
      intro hmate
      apply pairing.mate_ne current
      have hmapped : pairing.presentationEdgeEquiv mateSource =
          pairing.presentationEdgeEquiv ⟨i, edge⟩ :=
        congrArg pairing.presentationEdgeEquiv hmate
      calc
        pairing.mate current = pairing.presentationEdgeEquiv mateSource := by
          dsimp only [mateSource]
          rw [Equiv.apply_symm_apply]
        _ = pairing.presentationEdgeEquiv ⟨i, edge⟩ := hmapped
        _ = current := rfl
    · -- The mate orbit has the same unordered two-element label.
      rw [pairing.presentation_label, pairing.presentation_label]
      change pairing.orbitLabel (pairing.presentationEdgeEquiv mateSource) =
        pairing.orbitLabel current
      dsimp only [mateSource]
      rw [Equiv.apply_symm_apply]
      exact (pairing.orbitLabel_eq_iff current (pairing.mate current)).mpr
        (Or.inr rfl)
  · intro other hother
    rw [pairing.presentation_label, pairing.presentation_label] at hother
    have hlabel :
        pairing.orbitLabel (pairing.presentationEdgeEquiv other) =
          pairing.orbitLabel current := hother.2
    rcases (pairing.orbitLabel_eq_iff current
      (pairing.presentationEdgeEquiv other)).mp hlabel with heq | hmate
    · exfalso
      apply hother.1
      exact pairing.presentationEdgeEquiv.injective heq
    · apply pairing.presentationEdgeEquiv.injective
      dsimp only [mateSource]
      rw [Equiv.apply_symm_apply]
      exact hmate

/-- Helper for Theorem 78.1: compare the canonical polygonal source with the
surface by applying the cellwise region homeomorphisms. -/
private noncomputable def Triangulation.EdgePairing.comparison
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) : pairing.presentation.Source → X :=
  fun point ↦
    ((triangulation.triangle point.1).presentationRegionHomeomorph point.2 :
      (triangulation.triangle point.1).carrier)

/-- Helper for Theorem 78.1: on an oriented presentation edge, the comparison
map is the corresponding coherently directed curved-edge parameterization. -/
private theorem Triangulation.EdgePairing.comparison_orientedPoint
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (i : Fin triangulation.card) (edge : Fin 3) (t : unitInterval) :
    pairing.comparison
        ⟨i, (pairing.presentation.pasting i).orientedPoint edge t⟩ =
      triangulation.edgePoint (pairing.presentationEdgeEquiv ⟨i, edge⟩)
        (if pairing.direction (pairing.presentationEdgeEquiv ⟨i, edge⟩)
          then t else unitInterval.symm t) := by
  -- The presentation API performs the affine edge conversion before the
  -- curved chart, exactly matching the occurrence-level `edgePoint` spelling.
  unfold comparison Triangulation.edgePoint
  rw [pairing.presentationEdgeEquiv_apply]
  have hedge :=
    (triangulation.triangle i).presentationRegionHomeomorph_directedOrientedPoint
      (fun edge ↦ pairing.orbitLabel
        (pairing.presentationEdgeEquiv ⟨i, edge⟩))
      (fun edge ↦ pairing.direction
        (pairing.presentationEdgeEquiv ⟨i, edge⟩)) edge t
  rw [pairing.presentationEdgeEquiv_apply] at hedge
  simpa only [Sigma.fst, Sigma.snd, Prod.fst, Prod.snd] using hedge

/-- Helper for Theorem 78.1: the cellwise comparison map is continuous on the
finite sigma source. -/
private theorem Triangulation.EdgePairing.continuous_comparison
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) : Continuous pairing.comparison := by
  -- Continuity on a sigma type is checked independently on every triangle.
  apply continuous_sigma
  intro i
  exact continuous_subtype_val.comp
    (triangulation.triangle i).presentationRegionHomeomorph.continuous

/-- Helper for Theorem 78.1: the triangulation cover makes the cellwise
comparison map surjective. -/
private theorem Triangulation.EdgePairing.comparison_surjective
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) :
    Function.Surjective pairing.comparison := by
  intro x
  have hxCover : x ∈ ⋃ i, (triangulation.triangle i).carrier := by
    rw [triangulation.cover]
    exact Set.mem_univ x
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxCover
  let target : (triangulation.triangle i).carrier := ⟨x, hxi⟩
  let preimage :=
    (triangulation.triangle i).presentationRegionHomeomorph.symm target
  refine ⟨⟨i, preimage⟩, ?_⟩
  -- Surjectivity is the inverse computation in the chosen cell, followed by
  -- coercion from its carrier subtype.
  unfold comparison
  exact congrArg Subtype.val
    ((triangulation.triangle i).presentationRegionHomeomorph.apply_symm_apply
      target)

/-- Helper for Theorem 78.1: generated edge identifications lie in fibers of
the cellwise comparison map. -/
private theorem Triangulation.EdgePairing.comparison_eq_of_identified
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (x y : pairing.presentation.Source)
    (hidentified : pairing.presentation.Identified x y) :
    pairing.comparison x = pairing.comparison y := by
  -- Induct over the generated equivalence relation; only a direct edge step
  -- needs the orbit-label and coherent-direction computations.
  induction hidentified with
  | rel x y hrelated =>
      unfold PolygonalPasting.Related at hrelated
      obtain ⟨i, j, edgeI, edgeJ, t, hlabel, rfl, rfl⟩ := hrelated
      rw [pairing.comparison_orientedPoint,
        pairing.comparison_orientedPoint]
      rw [pairing.presentation_label, pairing.presentation_label] at hlabel
      rcases (pairing.orbitLabel_eq_iff
          (pairing.presentationEdgeEquiv ⟨i, edgeI⟩)
          (pairing.presentationEdgeEquiv ⟨j, edgeJ⟩)).mp hlabel.symm with
        heq | hmate
      · rw [heq]
      · rw [hmate]
        exact pairing.edgePoint_direction_eq _ t
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- Helper for Theorem 78.1: convert a geometric edge parameter into the
common presentation parameter for a selected Boolean direction. -/
private def presentationParameter (direction : Bool) (t : unitInterval) :
    unitInterval :=
  if direction then t else unitInterval.symm t

/-- Helper for Theorem 78.1: converting a geometric parameter to a
presentation parameter and then applying the direction recovers the original. -/
private theorem presentationParameter_normalizes
    (direction : Bool) (t : unitInterval) :
    (if direction then presentationParameter direction t
      else unitInterval.symm (presentationParameter direction t)) = t := by
  -- Positive direction is immediate; negative direction uses involutivity of
  -- unit-interval reversal.
  cases direction
  · simp only [Bool.false_eq_true, if_false, presentationParameter,
      unitInterval.symm_symm]
  · simp only [if_true, presentationParameter]

/-- Helper for Theorem 78.1: the canonical source representative of a point
inside a selected triangle is its inverse under the cellwise homeomorphism. -/
private noncomputable def Triangulation.EdgePairing.sourcePoint
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) (v : X)
    (i : Fin triangulation.card)
    (hv : v ∈ (triangulation.triangle i).carrier) :
    pairing.presentation.Source :=
  ⟨i, (triangulation.triangle i).presentationRegionHomeomorph.symm ⟨v, hv⟩⟩

/-- Helper for Theorem 78.1: comparison sends the canonical source
representative back to its defining surface point. -/
private theorem Triangulation.EdgePairing.comparison_sourcePoint
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) (v : X)
    (i : Fin triangulation.card)
    (hv : v ∈ (triangulation.triangle i).carrier) :
    pairing.comparison (pairing.sourcePoint v i hv) = v := by
  -- Apply the cellwise homeomorphism to its inverse and forget the carrier
  -- membership certificate.
  unfold sourcePoint comparison
  exact congrArg Subtype.val
    ((triangulation.triangle i).presentationRegionHomeomorph.apply_symm_apply
      ⟨v, hv⟩)

/-- Helper for Theorem 78.1: within one triangle, any source point comparing
to `v` is the canonical inverse-image representative of `v`. -/
private theorem Triangulation.EdgePairing.sourcePoint_eq_of_comparison_eq
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) (v : X)
    (i : Fin triangulation.card)
    (hv : v ∈ (triangulation.triangle i).carrier)
    (point : Theorem78_1.presentationTriangle.region)
    (hpoint : pairing.comparison ⟨i, point⟩ = v) :
    pairing.sourcePoint v i hv = ⟨i, point⟩ := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    -- Injectivity of the region homeomorphism reduces the claim to the two
    -- ambient comparison values, both of which are `v`.
    apply (triangulation.triangle i).presentationRegionHomeomorph.injective
    apply Subtype.ext
    exact (pairing.comparison_sourcePoint v i hv).trans hpoint.symm

/-- Helper for Theorem 78.1: if two distinct incident triangles share an
edge, their canonical representatives of a point on that edge are directly
identified by the presentation. -/
private theorem Triangulation.EdgePairing.sourcePoint_identified_of_sharedEdge
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) (v : X)
    (i j : Fin triangulation.card) (hij : i ≠ j)
    (hvI : v ∈ (triangulation.triangle i).carrier)
    (hvJ : v ∈ (triangulation.triangle j).carrier)
    (edgeI edgeJ : Fin 3)
    (hintersectionI :
      (triangulation.triangle i).carrier ∩
          (triangulation.triangle j).carrier =
        (triangulation.triangle i).edge edgeI)
    (hintersectionJ :
      (triangulation.triangle i).carrier ∩
          (triangulation.triangle j).carrier =
        (triangulation.triangle j).edge edgeJ) :
    pairing.presentation.Identified
      (pairing.sourcePoint v i hvI) (pairing.sourcePoint v j hvJ) := by
  let occurrenceI : Fin triangulation.card × Fin 3 := (i, edgeI)
  let occurrenceJ : Fin triangulation.card × Fin 3 := (j, edgeJ)
  have hedgeEq : (triangulation.triangle j).edge edgeJ =
      (triangulation.triangle i).edge edgeI :=
    hintersectionJ.symm.trans hintersectionI
  have hmate : occurrenceJ = pairing.mate occurrenceI := by
    -- The equality-or-mate characterization excludes equality because the
    -- two triangle indices are distinct.
    rcases (pairing.edge_eq_iff occurrenceI occurrenceJ).mp hedgeEq with
      heq | hmate
    · apply False.elim
      apply hij
      simpa only [occurrenceI, occurrenceJ, Prod.fst] using
        (congrArg Prod.fst heq).symm
    · exact hmate
  let polygonEdgeI : Fin 3 := Theorem78_1.presentationEdgeEquiv.symm edgeI
  let polygonEdgeJ : Fin 3 := Theorem78_1.presentationEdgeEquiv.symm edgeJ
  have hoccurrenceI : pairing.presentationEdgeEquiv ⟨i, polygonEdgeI⟩ =
      occurrenceI := by
    rw [pairing.presentationEdgeEquiv_apply]
    exact Prod.ext rfl (Theorem78_1.presentationEdgeEquiv.apply_symm_apply edgeI)
  have hoccurrenceJ : pairing.presentationEdgeEquiv ⟨j, polygonEdgeJ⟩ =
      occurrenceJ := by
    rw [pairing.presentationEdgeEquiv_apply]
    exact Prod.ext rfl (Theorem78_1.presentationEdgeEquiv.apply_symm_apply edgeJ)
  have hvIntersection : v ∈ (triangulation.triangle i).carrier ∩
      (triangulation.triangle j).carrier := ⟨hvI, hvJ⟩
  have hvEdgeI : v ∈ (triangulation.triangle i).edge edgeI := by
    rwa [← hintersectionI]
  obtain ⟨s, hvs⟩ :=
    ((triangulation.triangle i).mem_edge_iff edgeI v).mp hvEdgeI
  let t := presentationParameter (pairing.direction occurrenceI) s
  have hnormalize :
      (if pairing.direction occurrenceI then t else unitInterval.symm t) = s := by
    exact presentationParameter_normalizes (pairing.direction occurrenceI) s
  have hcomparisonI : pairing.comparison
      ⟨i, (pairing.presentation.pasting i).orientedPoint polygonEdgeI t⟩ = v := by
    rw [pairing.comparison_orientedPoint, hoccurrenceI, hnormalize]
    exact hvs.symm
  have hcomparisonJ : pairing.comparison
      ⟨j, (pairing.presentation.pasting j).orientedPoint polygonEdgeJ t⟩ = v := by
    rw [pairing.comparison_orientedPoint, hoccurrenceJ, hmate]
    calc
      triangulation.edgePoint (pairing.mate occurrenceI)
          (if pairing.direction (pairing.mate occurrenceI)
            then t else unitInterval.symm t) =
          triangulation.edgePoint occurrenceI
            (if pairing.direction occurrenceI then t
              else unitInterval.symm t) :=
        (pairing.edgePoint_direction_eq occurrenceI t).symm
      _ = triangulation.edgePoint occurrenceI s := congrArg _ hnormalize
      _ = v := hvs.symm
  have hsourceI : pairing.sourcePoint v i hvI =
      ⟨i, (pairing.presentation.pasting i).orientedPoint polygonEdgeI t⟩ :=
    pairing.sourcePoint_eq_of_comparison_eq v i hvI _ hcomparisonI
  have hsourceJ : pairing.sourcePoint v j hvJ =
      ⟨j, (pairing.presentation.pasting j).orientedPoint polygonEdgeJ t⟩ :=
    pairing.sourcePoint_eq_of_comparison_eq v j hvJ _ hcomparisonJ
  rw [hsourceI, hsourceJ]
  apply Relation.EqvGen.rel
  -- The direct relation uses the common parameter `t`; orbit labels agree
  -- because the second geometric occurrence is the mate of the first.
  refine ⟨i, j, polygonEdgeI, polygonEdgeJ, t, ?_, rfl, rfl⟩
  rw [pairing.presentation_label, pairing.presentation_label,
    hoccurrenceI, hoccurrenceJ, hmate]
  exact (pairing.orbitLabel_eq_iff occurrenceI
    (pairing.mate occurrenceI)).mpr (Or.inr rfl) |>.symm

/-- Helper for Theorem 78.1: an off-vertex overlap of two incident triangles
induces an identification of their canonical representatives of the vertex. -/
private theorem Triangulation.EdgePairing.sourcePoint_identified_of_overlap
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) (v : X)
    (i j : Fin triangulation.card)
    (hvI : v ∈ (triangulation.triangle i).carrier)
    (hvJ : v ∈ (triangulation.triangle j).carrier)
    (hoverlap : (((triangulation.triangle i).carrier ∩
      (triangulation.triangle j).carrier) \ {v}).Nonempty) :
    pairing.presentation.Identified
      (pairing.sourcePoint v i hvI) (pairing.sourcePoint v j hvJ) := by
  by_cases hij : i = j
  · subst j
    exact Relation.EqvGen.refl _
  obtain ⟨z, hzIntersection, hzv⟩ := hoverlap
  rcases triangulation.intersection_spec i j hij with
    hdisjoint | hvertex | hsharedEdge
  · -- A witnessed overlap contradicts disjointness.
    exact False.elim
      (Set.disjoint_left.mp hdisjoint hzIntersection.1 hzIntersection.2)
  · obtain ⟨vertexI, _, hintersection, _⟩ :=
      (CurvedTriangle.sharesVertex_iff _ _).mp hvertex
    have hzVertex : z = (triangulation.triangle i).vertex vertexI := by
      have hz := hzIntersection
      rw [hintersection, Set.mem_singleton_iff] at hz
      exact hz
    have hvVertex : v = (triangulation.triangle i).vertex vertexI := by
      have hv : v ∈ (triangulation.triangle i).carrier ∩
          (triangulation.triangle j).carrier := ⟨hvI, hvJ⟩
      rw [hintersection, Set.mem_singleton_iff] at hv
      exact hv
    exact False.elim (hzv (hzVertex.trans hvVertex.symm))
  · obtain ⟨edgeI, edgeJ, hintersectionI, hedgeEq⟩ :=
      (CurvedTriangle.sharesEdge_iff _ _).mp hsharedEdge
    have hintersectionJ :
        (triangulation.triangle i).carrier ∩
            (triangulation.triangle j).carrier =
          (triangulation.triangle j).edge edgeJ :=
      hintersectionI.trans hedgeEq
    exact pairing.sourcePoint_identified_of_sharedEdge v i j hij hvI hvJ
      edgeI edgeJ hintersectionI hintersectionJ

/-- Helper for Theorem 78.1: vertex-star connectivity composes the local
shared-edge identifications between any two triangles incident to a point. -/
private theorem Triangulation.EdgePairing.sourcePoint_identified
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) (v : X)
    (i j : Fin triangulation.card)
    (hvI : v ∈ (triangulation.triangle i).carrier)
    (hvJ : v ∈ (triangulation.triangle j).carrier) :
    pairing.presentation.Identified
      (pairing.sourcePoint v i hvI) (pairing.sourcePoint v j hvJ) := by
  let adjacent : Fin triangulation.card → Fin triangulation.card → Prop :=
    fun a b ↦ v ∈ (triangulation.triangle a).carrier ∧
      v ∈ (triangulation.triangle b).carrier ∧
        (((triangulation.triangle a).carrier ∩
          (triangulation.triangle b).carrier) \ {v}).Nonempty
  have hchain : Relation.ReflTransGen adjacent i j :=
    triangulation.vertexStarConnectedWithin v i j hvI hvJ
  have hresult : ∃ hv : v ∈ (triangulation.triangle j).carrier,
      pairing.presentation.Identified
        (pairing.sourcePoint v i hvI) (pairing.sourcePoint v j hv) := by
    induction hchain with
    | refl =>
        exact ⟨hvI, Relation.EqvGen.refl _⟩
    | tail hab hbc ih =>
        obtain ⟨hvB, hidentified⟩ := ih hbc.1
        refine ⟨hbc.2.1, Relation.EqvGen.trans _ _ _ hidentified ?_⟩
        exact pairing.sourcePoint_identified_of_overlap v _ _ hbc.1 hbc.2.1
          hbc.2.2
  obtain ⟨hvJ', hidentified⟩ := hresult
  -- Proof irrelevance identifies the two carrier-membership certificates.
  simpa only using hidentified

/-- Helper for Theorem 78.1: equal comparison values are joined by the
generated edge relation, using vertex-star connectivity for different cells. -/
private theorem Triangulation.EdgePairing.identified_of_comparison_eq
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (x y : pairing.presentation.Source)
    (hcomparison : pairing.comparison x = pairing.comparison y) :
    pairing.presentation.Identified x y := by
  obtain ⟨i, pointI⟩ := x
  obtain ⟨j, pointJ⟩ := y
  let v : X := pairing.comparison ⟨i, pointI⟩
  have hvI : v ∈ (triangulation.triangle i).carrier := by
    -- The comparison value of a source point lies in its cell carrier.
    unfold v comparison
    exact ((triangulation.triangle i).presentationRegionHomeomorph pointI).property
  have hvJRaw : pairing.comparison ⟨j, pointJ⟩ ∈
      (triangulation.triangle j).carrier := by
    unfold comparison
    exact ((triangulation.triangle j).presentationRegionHomeomorph pointJ).property
  have hcomparisonJ : pairing.comparison ⟨j, pointJ⟩ = v := by
    exact hcomparison.symm
  have hvJ : v ∈ (triangulation.triangle j).carrier := by
    rw [← hcomparisonJ]
    exact hvJRaw
  have hsourceI : pairing.sourcePoint v i hvI = ⟨i, pointI⟩ :=
    pairing.sourcePoint_eq_of_comparison_eq v i hvI pointI rfl
  have hsourceJ : pairing.sourcePoint v j hvJ = ⟨j, pointJ⟩ :=
    pairing.sourcePoint_eq_of_comparison_eq v j hvJ pointJ hcomparisonJ
  rw [← hsourceI, ← hsourceJ]
  exact pairing.sourcePoint_identified v i j hvI hvJ

/-- Helper for Theorem 78.1: the generated presentation relation is exactly
the kernel of the cellwise comparison map. -/
private theorem Triangulation.EdgePairing.identified_iff_comparison_eq
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing)
    (x y : pairing.presentation.Source) :
    pairing.presentation.Identified x y ↔
      pairing.comparison x = pairing.comparison y := by
  constructor
  · exact pairing.comparison_eq_of_identified x y
  · exact pairing.identified_of_comparison_eq x y

/-- Helper for Theorem 78.1: bundle the continuous cellwise comparison as a
continuous map. -/
private noncomputable def Triangulation.EdgePairing.comparisonMap
    {X : Type u} [TopologicalSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) :
    C(pairing.presentation.Source, X) :=
  ⟨pairing.comparison, pairing.continuous_comparison⟩

/-- Helper for Theorem 78.1: compactness of the finite polygonal source and
Hausdorffness of the surface make the surjective comparison a quotient map. -/
private theorem Triangulation.EdgePairing.isQuotientMap_comparisonMap
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    [CompactSpace X] {triangulation : Triangulation X}
    (pairing : triangulation.EdgePairing) :
    Topology.IsQuotientMap pairing.comparisonMap := by
  -- The standard compact-to-Hausdorff criterion consumes continuity and
  -- surjectivity already established cellwise.
  exact Topology.IsQuotientMap.of_surjective_continuous
    pairing.comparison_surjective pairing.continuous_comparison

/-- Helper for Theorem 78.1: a quotient map whose kernel is the edge-identification
relation induces a homeomorphism from the polygonal realization. -/
private theorem PolygonalPasting.realizationHomeomorphicOfQuotientMap
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι] {S : Type*}
    (presentation : PolygonalPasting ι S)
    (comparison : C(presentation.Source, X))
    (hquotient : Topology.IsQuotientMap comparison)
    (hkernel : ∀ x y, presentation.Identified x y ↔ comparison x = comparison y) :
    Nonempty (presentation.Realization ≃ₜ X) := by
  -- First replace the generated edge setoid by the comparison map's kernel.
  let relationEquiv : presentation.Realization ≃ₜ Quotient (Setoid.ker comparison) :=
    Homeomorph.Quotient.congrRight (r := presentation.Identified)
      (r' := Setoid.ker comparison) hkernel
  -- The quotient-map universal property identifies its kernel quotient with `X`.
  exact ⟨relationEquiv.trans hquotient.homeomorph⟩

/-- Helper for Theorem 78.1: a surface triangulation admits a paired triangular
polygonal presentation whose comparison map has exactly the generated edge fibers. -/
private theorem Triangulation.existsPolygonalPastingComparison
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    [CompactSpace X] (triangulation : Triangulation X) :
    ∃ (S : Type) (presentation : PolygonalPasting (Fin triangulation.card) S)
      (comparison : C(presentation.Source, X)),
      (∀ i, presentation.sides i = 3) ∧ presentation.PairsEdges ∧
        Topology.IsQuotientMap comparison ∧
          ∀ x y, presentation.Identified x y ↔ comparison x = comparison y := by
  -- Route correction: the former monolithic construction had no executable
  -- open-edge interface.  The lemmas above now normalize incidence at a fixed
  -- midpoint and expose compatible shared-edge data before the global assembly.
  classical
  obtain ⟨pairing⟩ := triangulation.existsEdgePairing
  refine ⟨Finset (Fin triangulation.card × Fin 3), pairing.presentation,
    pairing.comparisonMap, ?_, pairing.presentation_pairsEdges,
    pairing.isQuotientMap_comparisonMap, ?_⟩
  · -- Every cell uses the fixed three-sided cyclic presentation triangle.
    intro i
    rfl
  · -- The two kernel directions are the edge-relation induction and the
    -- vertex-star lifting proved above.
    intro x y
    exact pairing.identified_iff_comparison_eq x y

/-- Theorem 78.1. A compact triangulable surface is homeomorphic to a quotient of
finitely many disjoint planar closed triangles obtained by pairing all their edges. -/
theorem compactTriangulableSurface_homeomorphicRealization
    (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    [CompactSpace X] (h_triangulable : Triangulable X) :
    ∃ (m : ℕ) (S : Type) (presentation : PolygonalPasting (Fin m) S),
      (∀ i, presentation.sides i = 3) ∧ presentation.PairsEdges ∧
        Nonempty (presentation.Realization ≃ₜ X) := by
  -- Choose the finite triangulation supplied by triangulability.
  obtain ⟨triangulation⟩ := (triangulable_iff X).mp h_triangulable
  -- Use its comparison package, whose kernel records precisely the edge pasting.
  obtain ⟨S, presentation, comparison, hsides, hpairs, hquotient, hkernel⟩ :=
    triangulation.existsPolygonalPastingComparison
  refine ⟨triangulation.card, S, presentation, hsides, hpairs, ?_⟩
  -- The generic quotient-kernel adapter supplies the required homeomorphism.
  exact presentation.realizationHomeomorphicOfQuotientMap comparison hquotient hkernel
