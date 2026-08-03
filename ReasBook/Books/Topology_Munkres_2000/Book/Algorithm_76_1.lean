module

public import Topology_Munkres_2000.Book.Definition_35_4.AdjunctionSpace
public import Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
public import Topology_Munkres_2000.Book.Definition_74_2.OrientedSegment

public section

open Set

namespace CyclicPolygon

noncomputable section

variable {m n : ℕ}

/-- A directed edge of a cyclic polygon, specified by its edge index and orientation. -/
structure DirectedEdge (poly : CyclicPolygon n) where
  /-- The cyclic index of the underlying polygon edge. -/
  index : Fin n
  /-- Whether the orientation follows the cyclic direction of the polygon. -/
  forward : Bool

namespace DirectedEdge

variable {poly : CyclicPolygon n}

/-- The initial endpoint selected by the directed edge orientation. -/
def initial (edge : poly.DirectedEdge) : EuclideanSpace ℝ (Fin 2) :=
  if edge.forward then poly.toPolygon.vertices edge.index
  else poly.toPolygon.vertices (finRotate n edge.index)

/-- The final endpoint selected by the directed edge orientation. -/
def final (edge : poly.DirectedEdge) : EuclideanSpace ℝ (Fin 2) :=
  if edge.forward then poly.toPolygon.vertices (finRotate n edge.index)
  else poly.toPolygon.vertices edge.index

/-- Helper for Proposition 76.2: the initial endpoint of a directed edge is selected
by its orientation flag. -/
theorem initial_eq (edge : poly.DirectedEdge) :
    edge.initial = if edge.forward then poly.toPolygon.vertices edge.index
      else poly.toPolygon.vertices (finRotate n edge.index) := by
  -- Record the defining endpoint formula as public rewrite API.
  rfl

/-- Helper for Proposition 76.2: the final endpoint of a directed edge is selected
by its orientation flag. -/
theorem final_eq (edge : poly.DirectedEdge) :
    edge.final = if edge.forward then poly.toPolygon.vertices (finRotate n edge.index)
      else poly.toPolygon.vertices edge.index := by
  -- Record the defining endpoint formula as public rewrite API.
  rfl

/-- Helper for Algorithm 76.1: the endpoints selected by a directed polygon edge are distinct. -/
theorem initial_ne_final (edge : poly.DirectedEdge) : edge.initial ≠ edge.final := by
  -- The nonzero cyclic edge vector gives the endpoint inequality in either orientation.
  have hnext_ne_current :
      poly.toPolygon.vertices (finRotate n edge.index) ≠
        poly.toPolygon.vertices edge.index :=
    sub_ne_zero.mp (poly.cyclicEdgeVector_ne_zero edge.index)
  cases hforward : edge.forward
  · simpa [initial, final, hforward] using hnext_ne_current
  · simpa [initial, final, hforward] using hnext_ne_current.symm

/-- The canonically oriented nondegenerate segment underlying a directed polygon edge. -/
def segment (edge : poly.DirectedEdge) : OrientedSegment (EuclideanSpace ℝ (Fin 2)) where
  initial := edge.initial
  final := edge.final
  -- Endpoint nondegeneracy is supplied by the directed-edge interface.
  ne := edge.initial_ne_final

/-- Helper for Proposition 76.2: the canonical segment starts at the directed
edge's selected initial endpoint. -/
theorem segment_initial (edge : poly.DirectedEdge) :
    edge.segment.initial = edge.initial := by
  -- Project the initial field of the canonical segment constructor.
  rfl

/-- Helper for Proposition 76.2: the canonical segment ends at the directed edge's
selected final endpoint. -/
theorem segment_final (edge : poly.DirectedEdge) :
    edge.segment.final = edge.final := by
  -- Project the final field of the canonical segment constructor.
  rfl

/-- The canonical oriented segment has the indexed polygon edge as carrier. -/
theorem segment_carrier (edge : poly.DirectedEdge) :
    edge.segment.carrier = poly.edgeSet edge.index := by
  -- Both directed orientations normalize to the same unoriented polygon segment.
  cases hforward : edge.forward
  · simp [segment, OrientedSegment.carrier, initial, final, hforward,
      edgeSet_def, Polygon.edgeSet, affineSegment_eq_segment, segment_symm]
  · simp [segment, OrientedSegment.carrier, initial, final, hforward,
      edgeSet_def, Polygon.edgeSet, affineSegment_eq_segment]

/-- The selected edge as a subset of the filled polygonal region. -/
abbrev regionEdge (edge : poly.DirectedEdge) : Set poly.region :=
  {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ poly.edgeSet edge.index}

/-- Membership in the selected region edge is membership in the indexed polygon edge. -/
theorem mem_regionEdge_iff (edge : poly.DirectedEdge) (x : poly.region) :
    x ∈ edge.regionEdge ↔ (x : EuclideanSpace ℝ (Fin 2)) ∈ poly.edgeSet edge.index :=
  Iff.rfl

/-- A point of the selected region edge, viewed in its canonical oriented segment. -/
def segmentPoint (edge : poly.DirectedEdge) (x : edge.regionEdge) : edge.segment.carrier :=
  ⟨x.1.1, edge.segment_carrier.symm ▸ x.2⟩

/-- Helper for Proposition 76.2: passing a selected region-edge point to the
oriented segment preserves its ambient point. -/
theorem segmentPoint_coe (edge : poly.DirectedEdge) (x : edge.regionEdge) :
    (edge.segmentPoint x : EuclideanSpace ℝ (Fin 2)) = x := by
  -- The conversion changes only the nested membership proofs.
  rfl

/-- Helper for Algorithm 76.1: viewing a selected region-edge point in its oriented segment
is continuous. -/
theorem continuous_segmentPoint (edge : poly.DirectedEdge) : Continuous edge.segmentPoint := by
  -- Forget the two ambient subtypes, then rebuild the segment-carrier subtype.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The positive affine map from one directed polygon edge into the region containing another. -/
def positiveMapFunction {left : CyclicPolygon m} {right : CyclicPolygon n}
    (source : left.DirectedEdge) (target : right.DirectedEdge) :
    source.regionEdge → right.region :=
  fun x ↦
    ⟨source.segment.positiveHomeomorph target.segment (source.segmentPoint x),
      right.edgeSet_subset_region target.index
        (target.segment_carrier ▸
          (source.segment.positiveHomeomorph target.segment (source.segmentPoint x)).2)⟩

/-- The positive affine map between directed polygon edges is continuous. -/
theorem continuous_positiveMapFunction {left : CyclicPolygon m} {right : CyclicPolygon n}
    (source : left.DirectedEdge) (target : right.DirectedEdge) :
    Continuous (positiveMapFunction source target) := by
  -- Compose the segment inclusion with the positive homeomorphism and forget its carrier.
  exact (continuous_subtype_val.comp
    ((source.segment.positiveHomeomorph target.segment).continuous_toFun.comp
      source.continuous_segmentPoint)).subtype_mk _

/-- The canonical continuous positive affine map from one directed polygon edge to another. -/
def positiveMap {left : CyclicPolygon m} {right : CyclicPolygon n}
    (source : left.DirectedEdge) (target : right.DirectedEdge) :
    C(source.regionEdge, right.region) :=
  ⟨positiveMapFunction source target, continuous_positiveMapFunction source target⟩

/-- The canonical positive edge map is the positive homeomorphism on underlying points. -/
theorem positiveMap_apply {left : CyclicPolygon m} {right : CyclicPolygon n}
    (source : left.DirectedEdge) (target : right.DirectedEdge) (x : source.regionEdge) :
    (positiveMap source target x : EuclideanSpace ℝ (Fin 2)) =
      source.segment.positiveHomeomorph target.segment (source.segmentPoint x) := by
  -- The bundled continuous map has `positiveMapFunction` as its underlying function.
  rfl

end DirectedEdge

/-- Algorithm 76.1: Two disjoint cyclic polygonal regions with distinguished directed edges
are glued by their canonical positive affine map. -/
structure EdgeGluing (left : CyclicPolygon m) (right : CyclicPolygon n) where
  /-- The distinguished directed edge of the left polygonal region. -/
  leftEdge : left.DirectedEdge
  /-- The distinguished directed edge of the right polygonal region. -/
  rightEdge : right.DirectedEdge
  /-- The two filled polygonal regions are disjoint in the plane. -/
  regions_disjoint : Disjoint left.region right.region

namespace EdgeGluing

variable {left : CyclicPolygon m} {right : CyclicPolygon n}

/-- The selected left edge as a subset of the left polygonal region. -/
abbrev attachingSubset (gluing : EdgeGluing left right) : Set left.region :=
  gluing.leftEdge.regionEdge

/-- The canonical positive affine attaching map between the distinguished edges. -/
def attachingMap (gluing : EdgeGluing left right) :
    C(gluing.attachingSubset, right.region) :=
  gluing.leftEdge.positiveMap gluing.rightEdge

/-- The quotient obtained by attaching the left polygonal region to the right one along
the distinguished directed edges. -/
abbrev Realization (gluing : EdgeGluing left right) : Type :=
  AdjunctionSpace gluing.attachingSubset gluing.attachingMap

/-- The attaching map is induced by the positive affine homeomorphism of the selected
oriented segments. -/
theorem attachingMap_apply (gluing : EdgeGluing left right)
    (x : gluing.attachingSubset) :
    (gluing.attachingMap x : EuclideanSpace ℝ (Fin 2)) =
      gluing.leftEdge.segment.positiveHomeomorph gluing.rightEdge.segment
        (gluing.leftEdge.segmentPoint x) := by
  -- Unfolding the canonical attaching map reduces to the directed-edge computation rule.
  exact gluing.leftEdge.positiveMap_apply gluing.rightEdge x

/-- The realization is the canonical adjunction space for the positive affine attaching map. -/
theorem realization_def (gluing : EdgeGluing left right) :
    gluing.Realization = AdjunctionSpace gluing.attachingSubset gluing.attachingMap := by
  -- `Realization` is the canonical adjunction-space abbreviation.
  rfl

/-- The canonical inclusion of the left polygonal region into the realization. -/
def includeLeft (gluing : EdgeGluing left right) : left.region → gluing.Realization :=
  AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap

/-- The canonical inclusion of the right polygonal region into the realization. -/
def includeRight (gluing : EdgeGluing left right) : right.region → gluing.Realization :=
  AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap

/-- The left realization inclusion is the canonical first-summand inclusion of the
underlying adjunction space. -/
theorem includeLeft_eq_includeX (gluing : EdgeGluing left right) (x : left.region) :
    gluing.includeLeft x =
      AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap x := by
  -- Unwrap the named inclusion at its construction owner.
  rfl

/-- The right realization inclusion is the canonical second-summand inclusion of the
underlying adjunction space. -/
theorem includeRight_eq_includeY (gluing : EdgeGluing left right) (y : right.region) :
    gluing.includeRight y =
      AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap y := by
  -- Unwrap the named inclusion at its construction owner.
  rfl


end EdgeGluing

end

end CyclicPolygon
