module

public import Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
public import Mathlib.Topology.Algebra.Group.Basic

public section

open Set
open scoped Pointwise

namespace CyclicPolygon

noncomputable section

variable {n : ℕ}

/-- The cyclic polygon obtained by translating every vertex by `v`. -/
def translate (poly : CyclicPolygon n) (v : EuclideanSpace ℝ (Fin 2)) :
    CyclicPolygon n where
  three_le := poly.three_le
  center := Homeomorph.addRight v poly.center
  radius := poly.radius
  radius_pos := poly.radius_pos
  angles := poly.angles
  angles_strictMono := poly.angles_strictMono
  angles_last := poly.angles_last

/-- Translation acts on each cyclic vertex by `Homeomorph.addRight`. -/
theorem translate_apply (poly : CyclicPolygon n) (v : EuclideanSpace ℝ (Fin 2))
    (i : Fin n) :
    (poly.translate v).toPolygon.vertices i =
      Homeomorph.addRight v (poly.toPolygon.vertices i) := by
  -- Translation changes only the center, so the same offset is added to each vertex.
  simp only [toPolygon_vertices, vertex, translate, Homeomorph.coe_addRight]
  abel

/-- The region of a translated cyclic polygon is the translated original region. -/
theorem translate_region (poly : CyclicPolygon n) (v : EuclideanSpace ℝ (Fin 2)) :
    (poly.translate v).region = Homeomorph.addRight v '' poly.region := by
  -- Convex hull commutes with translating its finite set of generating vertices.
  rw [(poly.translate v).region_eq_convexHull, poly.region_eq_convexHull]
  have htranslatedRange :
      Set.range (poly.translate v).toPolygon.vertices =
        v +ᵥ Set.range poly.toPolygon.vertices := by
    ext x
    simp only [Set.mem_range, Set.mem_vadd_set]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨poly.toPolygon.vertices i, ⟨i, rfl⟩, ?_⟩
      rw [translate_apply, Homeomorph.coe_addRight]
      simp only [vadd_eq_add, add_comm]
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      rw [translate_apply, Homeomorph.coe_addRight]
      simp only [vadd_eq_add, add_comm]
  rw [htranslatedRange, convexHull_vadd]
  ext x
  simp only [Set.mem_vadd_set, Set.mem_image, Homeomorph.coe_addRight]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hsum : y + v = v +ᵥ y := by
      simpa only [vadd_eq_add] using add_comm y v
    exact ⟨y, hy, hsum⟩
  · rintro ⟨y, hy, rfl⟩
    have hsum : v +ᵥ y = y + v := by
      simpa only [vadd_eq_add] using add_comm v y
    exact ⟨y, hy, hsum⟩

/-- Each edge set of a translated cyclic polygon is the translated original edge set. -/
theorem translate_edgeSet (poly : CyclicPolygon n) (v : EuclideanSpace ℝ (Fin 2))
    (i : Fin n) :
    (poly.translate v).edgeSet i = Homeomorph.addRight v '' poly.edgeSet i := by
  -- An affine segment is carried to the segment between the translated endpoints.
  rw [edgeSet_def, edgeSet_def]
  unfold Polygon.edgeSet
  rw [translate_apply, translate_apply]
  simpa only [Homeomorph.coe_addRight, vadd_eq_add, add_comm] using
    (affineSegment_const_vadd_image (R := ℝ)
      (poly.toPolygon.vertices i)
      (poly.toPolygon.vertices (finRotate n i)) v).symm


end

end CyclicPolygon
