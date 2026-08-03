module

public import Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
public import Topology_Munkres_2000.Book.Definition_74_2.OrientedSegment

public section

namespace CyclicPolygon

noncomputable section

variable {n : ℕ}

/-- Helper for Proposition 74.1: consecutive cyclic vertices are distinct. -/
lemma cyclicVertices_ne (P : CyclicPolygon n) (i : Fin n) :
    P.toPolygon.vertices i ≠ P.toPolygon.vertices (finRotate n i) := by
  -- A repeated endpoint would make the directed edge vector zero.
  exact (sub_ne_zero.mp (P.cyclicEdgeVector_ne_zero i)).symm

/-- The oriented edge from the `i`th cyclic vertex to the next vertex. -/
def orientedEdge (P : CyclicPolygon n) (i : Fin n) :
    OrientedSegment (EuclideanSpace ℝ (Fin 2)) where
  initial := P.toPolygon.vertices i
  final := P.toPolygon.vertices (finRotate n i)
  ne := P.cyclicVertices_ne i

/-- Helper for Proposition 74.1: the canonical parameterized point of a cyclic edge lies
on the polygon boundary. -/
lemma paramHomeomorph_mem_boundary (P : CyclicPolygon n) (i : Fin n) (s : unitInterval) :
    ((P.orientedEdge i).paramHomeomorph s : EuclideanSpace ℝ (Fin 2)) ∈ P.boundary := by
  -- The parameterized carrier is the corresponding member of the boundary edge union.
  rw [P.boundary_def]
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [P.edgeSet_def]
  unfold Polygon.edgeSet OrientedSegment.carrier
  rw [affineSegment_eq_segment]
  exact ((P.orientedEdge i).paramHomeomorph s).property

/-- The point with affine parameter `s` on the `i`th cyclic edge. -/
def edgePoint (P : CyclicPolygon n) (i : Fin n) (s : unitInterval) : P.boundary :=
  ⟨(P.orientedEdge i).paramHomeomorph s, P.paramHomeomorph_mem_boundary i s⟩

/-- The underlying point of `P.edgePoint i s` is the canonical parameterized point of the
oriented edge. -/
theorem edgePoint_coe (P : CyclicPolygon n) (i : Fin n) (s : unitInterval) :
    (P.edgePoint i s : EuclideanSpace ℝ (Fin 2)) =
      ((P.orientedEdge i).paramHomeomorph s : EuclideanSpace ℝ (Fin 2)) := by
  rfl

/-- Helper for Proposition 74.1: the underlying edge parameterization is the usual affine
line map between consecutive vertices. -/
theorem edgePoint_coe_eq_lineMap (P : CyclicPolygon n) (i : Fin n) (s : unitInterval) :
    (P.edgePoint i s : EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap (P.toPolygon.vertices i)
        (P.toPolygon.vertices (finRotate n i)) (s : ℝ) := by
  -- Pass through the oriented-segment parameterization, then reduce its endpoint projections.
  rw [P.edgePoint_coe, OrientedSegment.paramHomeomorph_apply]
  rfl

/-- Helper for Proposition 76.2: a boundary point has its canonical inclusion into
the filled cyclic polygonal region. -/
def boundaryToRegion (P : CyclicPolygon n) : P.boundary → P.region :=
  fun point ↦ ⟨point, P.boundary_subset_region point.property⟩

/-- Helper for Proposition 76.2: the boundary-to-region inclusion preserves the
ambient Euclidean point. -/
theorem boundaryToRegion_coe (P : CyclicPolygon n) (point : P.boundary) :
    (P.boundaryToRegion point : EuclideanSpace ℝ (Fin 2)) = point := by
  -- The inclusion changes only the proof of region membership.
  rfl

/-- Helper for Proposition 76.2: a canonical cyclic edge point lies on its indexed
polygon edge, not merely on the union forming the whole boundary. -/
theorem edgePoint_mem_edgeSet (P : CyclicPolygon n) (i : Fin n) (s : unitInterval) :
    (P.edgePoint i s : EuclideanSpace ℝ (Fin 2)) ∈ P.edgeSet i := by
  -- Expose the indexed segment and use the parameterized point's carrier proof.
  rw [P.edgeSet_def, P.edgePoint_coe]
  unfold Polygon.edgeSet OrientedSegment.carrier orientedEdge
  rw [affineSegment_eq_segment]
  exact ((P.orientedEdge i).paramHomeomorph s).property

/-- Helper for Proposition 76.2: parameter zero on a cyclic edge is its indexed
initial vertex, viewed in the filled polygon. -/
theorem boundaryToRegion_edgePoint_zero (P : CyclicPolygon n) (i : Fin n) :
    P.boundaryToRegion (P.edgePoint i 0) = P.vertexPoint i := by
  -- Evaluate the affine edge parameterization at its initial endpoint.
  apply Subtype.ext
  rw [P.boundaryToRegion_coe, P.edgePoint_coe_eq_lineMap, P.vertexPoint_coe]
  exact AffineMap.lineMap_apply_zero _ _

/-- Helper for Proposition 76.2: parameter one on a cyclic edge is its next cyclic
vertex, viewed in the filled polygon. -/
theorem boundaryToRegion_edgePoint_one (P : CyclicPolygon n) (i : Fin n) :
    P.boundaryToRegion (P.edgePoint i 1) = P.vertexPoint (finRotate n i) := by
  -- Evaluate the affine edge parameterization at its terminal endpoint.
  apply Subtype.ext
  rw [P.boundaryToRegion_coe, P.edgePoint_coe_eq_lineMap, P.vertexPoint_coe]
  exact AffineMap.lineMap_apply_one _ _

/-- The positive homeomorphism from the `i`th edge of `P` to the corresponding edge of `Q`. -/
def positiveEdgeHomeomorph (P Q : CyclicPolygon n) (i : Fin n) :
    (P.orientedEdge i).carrier ≃ₜ (Q.orientedEdge i).carrier :=
  (P.orientedEdge i).positiveHomeomorph (Q.orientedEdge i)

/-- The positive edge homeomorphism preserves the common affine parameter. -/
theorem positiveEdgeHomeomorph_apply (P Q : CyclicPolygon n) (i : Fin n)
    (s : unitInterval) :
    P.positiveEdgeHomeomorph Q i ((P.orientedEdge i).paramHomeomorph s) =
      (Q.orientedEdge i).paramHomeomorph s :=
  OrientedSegment.positiveHomeomorph_apply (P.orientedEdge i) (Q.orientedEdge i) s

/-- Helper for Proposition 74.1: an interior point differs from every boundary point. -/
lemma interiorPoint_ne_boundaryPoint (P : CyclicPolygon n) (p : P.interior)
    (x : P.boundary) :
    (p : EuclideanSpace ℝ (Fin 2)) ≠ (x : EuclideanSpace ℝ (Fin 2)) := by
  -- The source interior is the region with its boundary removed.
  have hp : (p : EuclideanSpace ℝ (Fin 2)) ∈ P.region \ P.boundary := by
    rw [← P.interior_def]
    exact p.property
  intro hpx
  exact hp.2 (hpx ▸ x.property)

/-- The oriented radial segment from an interior point to a boundary point. -/
def radialSegment (P : CyclicPolygon n) (p : P.interior) (x : P.boundary) :
    OrientedSegment (EuclideanSpace ℝ (Fin 2)) where
  initial := p
  final := x
  ne := P.interiorPoint_ne_boundaryPoint p x

/-- Helper for Proposition 74.1: the canonical parameterized point of a radial segment
lies in the filled polygonal region. -/
lemma radialSegment_point_mem_region (P : CyclicPolygon n) (p : P.interior)
    (x : P.boundary) (s : unitInterval) :
    ((P.radialSegment p x).point s : EuclideanSpace ℝ (Fin 2)) ∈ P.region := by
  -- Convexity contains the whole segment between the interior and boundary endpoints.
  have hp : (p : EuclideanSpace ℝ (Fin 2)) ∈ P.region \ P.boundary := by
    rw [← P.interior_def]
    exact p.property
  exact P.convex_region.segment_subset hp.1 (P.boundary_subset_region x.property)
    ((P.radialSegment p x).point s).property

/-- The point with affine parameter `s` on the radial segment from `p` to `x`. -/
def radialPoint (P : CyclicPolygon n) (p : P.interior) (x : P.boundary)
    (s : unitInterval) : P.region :=
  ⟨(P.radialSegment p x).point s, P.radialSegment_point_mem_region p x s⟩

/-- The underlying point of `P.radialPoint p x s` is the canonical parameterized point of the
oriented radial segment. -/
theorem radialPoint_coe (P : CyclicPolygon n) (p : P.interior) (x : P.boundary)
    (s : unitInterval) :
    (P.radialPoint p x s : EuclideanSpace ℝ (Fin 2)) = (P.radialSegment p x).point s := by
  rfl

/-- Helper for Proposition 74.1: the underlying radial parameterization is the affine line
map from the chosen interior point to the chosen boundary point. -/
theorem radialPoint_coe_eq_lineMap (P : CyclicPolygon n) (p : P.interior)
    (x : P.boundary) (s : unitInterval) :
    (P.radialPoint p x s : EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap (p : EuclideanSpace ℝ (Fin 2))
        (x : EuclideanSpace ℝ (Fin 2)) (s : ℝ) := by
  -- Pass through the oriented radial segment, then reduce its endpoint projections.
  rw [P.radialPoint_coe, OrientedSegment.point_coe]
  rfl


end

end CyclicPolygon
