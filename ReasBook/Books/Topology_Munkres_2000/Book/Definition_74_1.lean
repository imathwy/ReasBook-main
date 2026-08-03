module

public import Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon

public section

/- Definition 74.1: A polygonal region in the plane is determined by at least three
counterclockwise cyclic vertices on a circle. Its filled region is the intersection
of the inward closed half-planes, its boundary is the union of its cyclic edges, and
its source-defined interior is the region minus that boundary. From any interior
point, radial segments to the boundary cover the region and distinct such segments
intersect only at the chosen interior point. The source half-plane `Hᵢ`, supported by
the edge from `pᵢ₋₁` to `pᵢ`, corresponds to the preceding zero-based cyclic edge. -/
#check CyclicPolygon
#check CyclicPolygon.vertex
#check CyclicPolygon.vertexLast
#check CyclicPolygon.toPolygon
#check CyclicPolygon.region
#check CyclicPolygon.supportingHalfspace
#check CyclicPolygon.edgeSet
#check CyclicPolygon.boundary
#check CyclicPolygon.interior
#check CyclicPolygon.region_eq_iInter_supportingHalfspace
#check CyclicPolygon.region_eq_convexHull
#check CyclicPolygon.region_eq_iUnion_segments
#check CyclicPolygon.segment_inter_segment
