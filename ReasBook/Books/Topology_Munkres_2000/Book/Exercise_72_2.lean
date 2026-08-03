module

public import Topology_Munkres_2000.Book.Definition_35_4.AdjunctionSpace
public import Topology_Munkres_2000.Book.Theorem_72_1.Attachment

public section

universe u

/-- Exercise 72.2 (1): Attaching the closed unit two-ball to a normal space along
its boundary produces a normal adjunction space. This supplies the Hausdorff
hypothesis of Theorem 72.1. Through Exercise 35.8, normality of `A` is used both
here and to prove that the canonical copy of `A` is closedly embedded. -/
instance twoCellAdjunctionSpaceT4Space {A : Type u} [TopologicalSpace A] [T4Space A]
    (f : C(StandardSphere.boundary 1, A)) :
    T4Space (AdjunctionSpace (StandardSphere.boundary 1) f) := sorry

/-- The canonical copy of the attached space is closedly embedded in the
two-cell adjunction space. -/
theorem twoCellIncludeA_isClosedEmbedding {A : Type u} [TopologicalSpace A]
    [T4Space A] (f : C(StandardSphere.boundary 1, A)) :
    Topology.IsClosedEmbedding
      (AdjunctionSpace.includeY (StandardSphere.boundary 1) f) := sorry

/-- Exercise 72.2 (2): The canonical copy of `A` is closed in the two-cell
adjunction space. -/
theorem twoCellIncludeA_range_isClosed {A : Type u} [TopologicalSpace A]
    [T4Space A] (f : C(StandardSphere.boundary 1, A)) :
    IsClosed (Set.range (AdjunctionSpace.includeY
      (StandardSphere.boundary 1) f)) :=
  (twoCellIncludeA_isClosedEmbedding f).isClosed_range

/-- Exercise 72.2 (3): The canonical copy of `A` is path-connected in the
two-cell adjunction space. -/
theorem twoCellIncludeA_range_isPathConnected {A : Type u} [TopologicalSpace A]
    [PathConnectedSpace A] (f : C(StandardSphere.boundary 1, A)) :
    IsPathConnected (Set.range (AdjunctionSpace.includeY
      (StandardSphere.boundary 1) f)) :=
  isPathConnected_range (AdjunctionSpace.continuous_includeY
    (StandardSphere.boundary 1) f)

/-- The canonical continuous map from the closed unit disk to the two-cell
adjunction space. -/
@[expose]
def twoCellMap {A : Type u} [TopologicalSpace A]
    (f : C(StandardSphere.boundary 1, A)) :
    C(B², AdjunctionSpace (StandardSphere.boundary 1) f) :=
  ⟨AdjunctionSpace.includeX (StandardSphere.boundary 1) f,
    AdjunctionSpace.continuous_includeX (StandardSphere.boundary 1) f⟩

@[simp]
theorem twoCellMap_apply {A : Type u} [TopologicalSpace A]
    (f : C(StandardSphere.boundary 1, A)) (x : B²) :
    twoCellMap f x = AdjunctionSpace.includeX (StandardSphere.boundary 1) f x := rfl

/- Exercise 72.2 (4): The canonical map from the closed unit two-ball to the
adjunction space is continuous. -/
#check AdjunctionSpace.continuous_includeX

/-- Exercise 72.2 (5): The canonical disk map sends the boundary circle into
the canonical copy of `A`. -/
theorem twoCellMap_boundary {A : Type u} [TopologicalSpace A]
    (f : C(StandardSphere.boundary 1, A)) :
    Set.MapsTo (twoCellMap f) (StandardSphere.boundary 1)
      (Set.range (AdjunctionSpace.includeY
        (StandardSphere.boundary 1) f)) := by
  intro q hq
  refine ⟨f ⟨q, hq⟩, ?_⟩
  exact (AdjunctionSpace.glue (StandardSphere.boundary 1) f ⟨q, hq⟩).symm

/-- Exercise 72.2 (6): The canonical disk map restricts to a bijection from the
open unit two-ball onto the complement of the canonical copy of `A`. -/
theorem twoCellMap_interior_bijOn {A : Type u} [TopologicalSpace A]
    (f : C(StandardSphere.boundary 1, A)) :
    Set.BijOn (twoCellMap f) ClosedUnitDisk.interior
      (Set.range (AdjunctionSpace.includeY
        (StandardSphere.boundary 1) f))ᶜ := sorry

/-- Exercise 72.2: The canonical disk map and canonical copy of `A` satisfy the
closedness, path-connectedness, boundary, and interior-bijection hypotheses of
Theorem 72.1. -/
theorem twoCellAdjunctionSpace_attachmentSpec {A : Type u} [TopologicalSpace A]
    [T4Space A] [PathConnectedSpace A]
    (f : C(StandardSphere.boundary 1, A)) :
    IsClosed (Set.range (AdjunctionSpace.includeY
      (StandardSphere.boundary 1) f)) ∧
    IsPathConnected (Set.range (AdjunctionSpace.includeY
      (StandardSphere.boundary 1) f)) ∧
    Set.MapsTo (twoCellMap f) (StandardSphere.boundary 1)
      (Set.range (AdjunctionSpace.includeY
        (StandardSphere.boundary 1) f)) ∧
    Set.BijOn (twoCellMap f) ClosedUnitDisk.interior
      (Set.range (AdjunctionSpace.includeY
        (StandardSphere.boundary 1) f))ᶜ :=
  ⟨twoCellIncludeA_range_isClosed f,
    twoCellIncludeA_range_isPathConnected f, twoCellMap_boundary f,
    twoCellMap_interior_bijOn f⟩


end
