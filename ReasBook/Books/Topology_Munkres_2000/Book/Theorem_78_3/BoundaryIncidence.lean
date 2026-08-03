module

public import Topology_Munkres_2000.Book.Theorem_78_1.TriangleEdgeTopology
public import Topology_Munkres_2000.Book.Definition_78_3
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

import all Topology_Munkres_2000.Book.Definition_78_1.Triangulation

open scoped Manifold SurfaceBoundary

public section

universe u

namespace CurvedTriangle

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 78.3: a curved-triangle vertex does not belong to its
open cell. -/
theorem vertex_not_mem_openCell (triangle : CurvedTriangle X) (i : Fin 3) :
    triangle.vertex i ∉ triangle.openCell := by
  -- Pull an alleged open-cell witness back to the model vertex and use strictness.
  intro hi
  obtain ⟨y, hyInterior, hyvertex⟩ :=
    (triangle.mem_openCell_iff (triangle.vertex i)).mp hi
  have hy : y =
      ⟨triangle.model.points i, triangle.model.point_mem_closedInterior i⟩ := by
    apply triangle.chart.injective
    apply Subtype.ext
    unfold vertex at hyvertex
    exact hyvertex
  rw [hy] at hyInterior
  exact triangle.model.point_notMem_interior i hyInterior

/-- Helper for Theorem 78.3: the open cell is disjoint from every closed edge
of the same curved triangle. -/
theorem disjoint_openCell_edge (triangle : CurvedTriangle X) (i : Fin 3) :
    Disjoint triangle.openCell (triangle.edge i) := by
  -- Pull a hypothetical common point back through the injective triangle chart.
  rw [Set.disjoint_left]
  intro x hxopen hxedge
  obtain ⟨y, hyInterior, hyx⟩ :=
    (triangle.mem_openCell_iff x).mp hxopen
  rw [triangle.edge_eq_chart_image_modelEdge i] at hxedge
  obtain ⟨z, hzEdge, hzx⟩ := hxedge
  have hyz : y = z := by
    apply triangle.chart.injective
    exact Subtype.ext (hyx.trans hzx.symm)
  rw [hyz] at hyInterior
  exact Set.disjoint_left.mp
    (triangle.model.disjoint_interior_closedInterior_faceOpposite i)
      hyInterior hzEdge

/-- Helper for Theorem 78.3: the carrier of a curved triangle decomposes into
its open cell and its three closed edges. -/
theorem carrier_eq_openCell_union_edges (triangle : CurvedTriangle X) :
    triangle.carrier = triangle.openCell ∪ ⋃ i : Fin 3, triangle.edge i := by
  -- Pull a carrier point back through the chart and apply the simplex decomposition.
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := triangle.chart.surjective ⟨x, hx⟩
    have hyval : (y : EuclideanSpace ℝ (Fin 2)) ∈ triangle.model.closedInterior := y.property
    have hydecomp :=
      (Set.ext_iff.mp (Affine.Simplex.closedInterior_eq_interior_union triangle.model)
        (y : EuclideanSpace ℝ (Fin 2))).mp hyval
    rcases hydecomp with hinterior | hedge
    · exact Or.inl ((triangle.mem_openCell_iff x).mpr
        ⟨y, hinterior, congrArg Subtype.val hy⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hedge
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
      rw [triangle.edge_eq_chart_image_modelEdge i]
      exact ⟨y, hi, congrArg Subtype.val hy⟩
  · rintro (hopen | hedges)
    · exact triangle.openCell_subset_carrier hopen
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hedges
      exact triangle.edge_subset i hi

end

end CurvedTriangle

namespace Triangulation

noncomputable section

variable {X : Type u} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
/-- Helper for Theorem 78.3: the open cell of one triangle misses the carrier
of every distinct triangle in the triangulation. -/
theorem disjoint_openCell_carrier_of_ne (triangulation : Triangulation X)
    (i j : Fin triangulation.card) (hij : i ≠ j) :
    Disjoint (triangulation.triangle i).openCell
      (triangulation.triangle j).carrier := by
  -- Reduce each permitted intersection to a vertex or an edge, both outside the open cell.
  rw [Set.disjoint_left]
  intro x hxopen hxj
  have hxi : x ∈ (triangulation.triangle i).carrier :=
    (triangulation.triangle i).openCell_subset_carrier hxopen
  have hxinter : x ∈ (triangulation.triangle i).carrier ∩
      (triangulation.triangle j).carrier := ⟨hxi, hxj⟩
  rcases triangulation.intersection_spec i j hij with
    hdisjoint | hvertex | hedge
  · exact Set.disjoint_left.mp hdisjoint hxi hxj
  · obtain ⟨vertexI, _, hintersection, _⟩ :=
      (CurvedTriangle.sharesVertex_iff _ _).mp hvertex
    rw [hintersection] at hxinter
    have hxvertex : x = (triangulation.triangle i).vertex vertexI :=
      Set.mem_singleton_iff.mp hxinter
    exact (triangulation.triangle i).vertex_not_mem_openCell vertexI
      (hxvertex ▸ hxopen)
  · obtain ⟨edgeI, _, hintersection, _⟩ :=
      (CurvedTriangle.sharesEdge_iff _ _).mp hedge
    rw [hintersection] at hxinter
    exact Set.disjoint_left.mp
      ((triangulation.triangle i).disjoint_openCell_edge edgeI) hxopen hxinter

/-- Helper for Theorem 78.3: a triangulation open cell is open in the ambient
Hausdorff space. -/
theorem isOpen_openCell (triangulation : Triangulation X)
    (i : Fin triangulation.card) :
    IsOpen (triangulation.triangle i).openCell := by
  let competingCarriers : Set X :=
    ⋃ j : {j : Fin triangulation.card // j ≠ i},
      (triangulation.triangle j.1).carrier
  have hcompetingClosed : IsClosed competingCarriers := by
    dsimp only [competingCarriers]
    exact isClosed_iUnion_of_finite fun j ↦
      (triangulation.triangle j.1).isClosed_carrier
  obtain ⟨ambientOpen, hAmbientOpen, hopenPreimage⟩ :=
    isOpen_induced_iff.mp
      (triangulation.triangle i).isOpen_openCell_preimage_carrier
  have hopenCell :
      (triangulation.triangle i).openCell = ambientOpen \ competingCarriers := by
    ext x
    constructor
    · intro hx
      have hxcarrier :=
        (triangulation.triangle i).openCell_subset_carrier hx
      have hxAmbient : x ∈ ambientOpen := by
        have hxpreimage :
            (⟨x, hxcarrier⟩ : (triangulation.triangle i).carrier) ∈
              Subtype.val ⁻¹' ambientOpen := by
          exact (Set.ext_iff.mp hopenPreimage ⟨x, hxcarrier⟩).mpr hx
        exact hxpreimage
      refine ⟨hxAmbient, ?_⟩
      intro hxcompeting
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxcompeting
      exact Set.disjoint_left.mp
        (triangulation.disjoint_openCell_carrier_of_ne i j.1 j.2.symm) hx hxj
    · rintro ⟨hxAmbient, hxcompeting⟩
      have hxcover : x ∈ ⋃ j, (triangulation.triangle j).carrier := by
        rw [triangulation.cover]
        exact Set.mem_univ x
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxcover
      by_cases hji : j = i
      · subst j
        have hxpreimage :
            (⟨x, hxj⟩ : (triangulation.triangle i).carrier) ∈
              Subtype.val ⁻¹' ambientOpen := hxAmbient
        exact (Set.ext_iff.mp hopenPreimage ⟨x, hxj⟩).mp hxpreimage
      · exact False.elim (hxcompeting (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩))
  -- Remove the finite closed union of all competing carriers from the relative witness.
  rw [hopenCell]
  exact hAmbientOpen.sdiff hcompetingClosed

/-- Helper for Theorem 78.3: membership in a triangulation open cell supplies
an ambient Euclidean chart around the point. -/
theorem exists_euclideanChart_of_mem_openCell
    (triangulation : Triangulation X) (i : Fin triangulation.card) (x : X)
    (hx : x ∈ (triangulation.triangle i).openCell) :
    ∃ e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 2)), x ∈ e.source := by
  let source : TopologicalSpace.Opens X :=
    ⟨(triangulation.triangle i).openCell, triangulation.isOpen_openCell i⟩
  have hspan : affineSpan ℝ
      (Set.range (triangulation.triangle i).model.points) = ⊤ :=
    (triangulation.triangle i).model.span_eq_top (by simp)
  have hinterior :
      (triangulation.triangle i).model.interior =
        interior (triangulation.triangle i).model.closedInterior :=
    Affine.Simplex.interior_eq_topologicalInterior_closedInterior
      (triangulation.triangle i).model hspan
  have htargetOpen : IsOpen (triangulation.triangle i).model.interior := by
    rw [hinterior]
    exact isOpen_interior
  let target : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) :=
    ⟨(triangulation.triangle i).model.interior, htargetOpen⟩
  have hsourceNonempty : Nonempty source := ⟨⟨x, hx⟩⟩
  have htargetNonempty : Nonempty target :=
    Nonempty.map (triangulation.triangle i).openCellHomeomorph hsourceNonempty
  let chart : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 2)) :=
    ((source.openPartialHomeomorphSubtypeCoe hsourceNonempty).symm.trans
      (triangulation.triangle i).openCellHomeomorph.toOpenPartialHomeomorph).trans
        (target.openPartialHomeomorphSubtypeCoe htargetNonempty)
  refine ⟨chart, ?_⟩
  -- Both subtype-level homeomorphisms have full source, leaving exactly the open cell.
  have hxsource : x ∈ (source : Set X) := hx
  simpa only [chart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
    OpenPartialHomeomorph.symm_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_preimage,
    Set.mem_univ, and_true] using hxsource

/-- Helper for Theorem 78.3: every surface-boundary point lies on an edge of
some triangle in a fixed triangulation. -/
theorem exists_edge_of_mem_surfaceBoundary
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
    [IsManifold (𝓡∂ 2) 0 Y] [T2Space Y]
    (triangulation : Triangulation Y) (x : ∂Y) :
    ∃ (i : Fin triangulation.card) (j : Fin 3),
      x.1 ∈ (triangulation.triangle i).edge j := by
  have hxcover : x.1 ∈ ⋃ i, (triangulation.triangle i).carrier := by
    rw [triangulation.cover]
    exact Set.mem_univ x.1
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcover
  have hxdecomp :=
    (Set.ext_iff.mp (triangulation.triangle i).carrier_eq_openCell_union_edges x.1).mp hxi
  rcases hxdecomp with hxopen | hxedges
  · obtain ⟨chart, hxsource⟩ :=
      triangulation.exists_euclideanChart_of_mem_openCell i x.1 hxopen
    -- A Euclidean chart through `x` contradicts the defining boundary characterization.
    exact False.elim
      (((mem_surfaceBoundary_iff_noEuclideanChart x.1).mp x.2) ⟨chart, hxsource⟩)
  · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxedges
    exact ⟨i, j, hxj⟩

end

end Triangulation
