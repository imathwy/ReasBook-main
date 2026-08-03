module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere

public section

universe u

namespace ClosedUnitDisk

/-- The open unit disk, regarded as a subset of the closed unit disk. -/
def interior : Set B² :=
  (Subtype.val : B² → EuclideanSpace ℝ (Fin 2)) ⁻¹' Metric.ball 0 1

/-- Membership in the open disk is the strict unit-norm inequality. -/
theorem mem_interior_iff_norm_lt (x : B²) :
    x ∈ interior ↔ ‖(x : EuclideanSpace ℝ (Fin 2))‖ < 1 := by
  -- Unfold the preimage and express distance from the origin as the norm.
  simp only [interior, Set.mem_preimage, Metric.mem_ball, dist_zero_right]

/-- The restriction of a disk map to its boundary, with codomain restricted to
the subspace containing the boundary image. -/
@[expose]
def boundaryMap {X : Type u} [TopologicalSpace X] (A : Set X) (h : C(B², X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary 1) A) :
    C(StandardSphere.boundary 1, A) :=
  ⟨fun q ↦ ⟨h q, h_boundary q.property⟩,
    ((map_continuous h).comp continuous_subtype_val).subtype_mk _⟩

@[simp]
theorem boundaryMap_coe {X : Type u} [TopologicalSpace X] (A : Set X) (h : C(B², X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary 1) A)
    (q : StandardSphere.boundary 1) :
    (boundaryMap A h h_boundary q : X) = h q := by
  change h q = h q
  rfl

end ClosedUnitDisk

end
