module

public import Topology_Munkres_2000.Book.Example_74_1.Presentation

public section

namespace LabellingScheme

/-- A labelling scheme is triangular when every polygon word has three edges. -/
def IsTriangular {α : Type u} (scheme : LabellingScheme α) : Prop :=
  ∀ region : Occurrence scheme, region.1.1.length = 3

/-- A region in a triangular labelling scheme has exactly three boundary edges. -/
theorem IsTriangular.region_length {α : Type u} {scheme : LabellingScheme α}
    (h : scheme.IsTriangular) (region : Occurrence scheme) : region.1.1.length = 3 := by
  change ∀ region : Occurrence scheme, region.1.1.length = 3 at h
  exact h region

/-- A scheme is triangular when every polygon word occurring in it has length three. -/
theorem isTriangular_of_forall_mem {α : Type u} {scheme : LabellingScheme α}
    (h : ∀ word ∈ scheme, word.1.length = 3) : scheme.IsTriangular := by
  classical
  intro region
  -- Every occurrence projects to a polygon word belonging to the original multiset.
  exact h region.1 <| (@Multiset.count_pos _ (Classical.decEq _) region.1 scheme).mp <|
    Nat.zero_lt_of_lt region.2.2

/-- Standard triangular regions carrying a triangular labelling scheme. -/
@[expose]
def triangularRegions {α : Type u} (scheme : LabellingScheme α)
    (h : scheme.IsTriangular) : PolygonalRegions scheme where
  Point _ := standardTriangle
  topology _ := inferInstance
  edge region edge t :=
    TriangleDisk.edgePoint (Fin.cast (IsTriangular.region_length h region) edge) t

/-- The edge map of `triangularRegions` is the standard cyclic triangle parametrization. -/
@[simp] theorem triangularRegions_edge {α : Type u} (scheme : LabellingScheme α)
    (h : scheme.IsTriangular) (region : Occurrence scheme)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    (triangularRegions scheme h).edge region edge t =
      TriangleDisk.edgePoint (Fin.cast (IsTriangular.region_length h region) edge) t := rfl


end LabellingScheme
