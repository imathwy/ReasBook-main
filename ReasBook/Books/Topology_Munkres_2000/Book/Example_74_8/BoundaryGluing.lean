module

public import Topology_Munkres_2000.Book.Definition_35_4.AdjunctionSpace
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Real

public section

universe u v

/-- Explicit choices of disc charts in two spaces and an identification of their boundary
circles. -/
structure DiscBoundaryGluing (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] where
  leftChart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) X
  rightChart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) Y
  leftSource : leftChart.source = Metric.ball 0 1
  rightSource : rightChart.source = Metric.ball 0 1
  leftBoundary : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ) →
    {x : X // x ∉ leftChart '' Metric.ball 0 (1 / 2 : ℝ)}
  rightBoundary : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ) →
    {y : Y // y ∉ rightChart '' Metric.ball 0 (1 / 2 : ℝ)}
  leftBoundary_coe (point) : (leftBoundary point : X) = leftChart point
  rightBoundary_coe (point) : (rightBoundary point : Y) = rightChart point
  leftBoundary_embedding : Topology.IsEmbedding leftBoundary
  rightBoundary_embedding : Topology.IsEmbedding rightBoundary
  boundaryIdentification :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ)

namespace DiscBoundaryGluing

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The same boundary gluing with the two spaces interchanged. -/
def symm (gluing : DiscBoundaryGluing X Y) : DiscBoundaryGluing Y X where
  leftChart := gluing.rightChart
  rightChart := gluing.leftChart
  leftSource := gluing.rightSource
  rightSource := gluing.leftSource
  leftBoundary := gluing.rightBoundary
  rightBoundary := gluing.leftBoundary
  leftBoundary_coe := gluing.rightBoundary_coe
  rightBoundary_coe := gluing.leftBoundary_coe
  leftBoundary_embedding := gluing.rightBoundary_embedding
  rightBoundary_embedding := gluing.leftBoundary_embedding
  boundaryIdentification := gluing.boundaryIdentification.symm

/-- Reversing a boundary gluing twice recovers its original data. -/
theorem symm_symm (gluing : DiscBoundaryGluing X Y) : gluing.symm.symm = gluing := by
  -- All data fields return to their original values; proof fields are irrelevant.
  cases gluing
  rfl

/-- The Euclidean plane used for the chosen disc charts. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The boundary circle of the radius-`1 / 2` disc in `Plane`. -/
abbrev BoundaryCircle := Metric.sphere (0 : Plane) (1 / 2 : ℝ)

/-- The open disc deleted from the left-hand space. -/
@[expose]
def leftDeletedDisc (gluing : DiscBoundaryGluing X Y) : Set X :=
  gluing.leftChart '' Metric.ball 0 (1 / 2 : ℝ)

/-- The open disc deleted from the right-hand space. -/
@[expose]
def rightDeletedDisc (gluing : DiscBoundaryGluing X Y) : Set Y :=
  gluing.rightChart '' Metric.ball 0 (1 / 2 : ℝ)

/-- The left-hand space after deleting the chosen open disc. -/
abbrev LeftComplement (gluing : DiscBoundaryGluing X Y) :=
  {x : X // x ∉ gluing.leftDeletedDisc}

/-- The right-hand space after deleting the chosen open disc. -/
abbrev RightComplement (gluing : DiscBoundaryGluing X Y) :=
  {y : Y // y ∉ gluing.rightDeletedDisc}

/-- The embedded boundary circle in the left disc complement. -/
abbrev attachingSubset (gluing : DiscBoundaryGluing X Y) : Set gluing.LeftComplement :=
  Set.range gluing.leftBoundary

/-- The chosen parametrization of the left boundary as the attaching subset. -/
noncomputable def leftBoundaryHomeomorph (gluing : DiscBoundaryGluing X Y) :
    BoundaryCircle ≃ₜ gluing.attachingSubset :=
  gluing.leftBoundary_embedding.toHomeomorph

/-- The attaching map from the left boundary to the right disc complement. -/
noncomputable def attachingMap (gluing : DiscBoundaryGluing X Y) :
    C(gluing.attachingSubset, gluing.RightComplement) where
  toFun point := gluing.rightBoundary
    (gluing.boundaryIdentification (gluing.leftBoundaryHomeomorph.symm point))
  continuous_toFun := gluing.rightBoundary_embedding.continuous.comp
    (gluing.boundaryIdentification.continuous.comp gluing.leftBoundaryHomeomorph.symm.continuous)

/-- The attaching map is injective because both boundary parameterizations and their
identification are injective. -/
theorem attachingMap_injective (gluing : DiscBoundaryGluing X Y) :
    Function.Injective gluing.attachingMap := by
  intro a b hab
  -- Cancel the right boundary embedding, the boundary homeomorphism, and the inverse left
  -- parameterization in succession.
  apply gluing.leftBoundaryHomeomorph.symm.injective
  apply gluing.boundaryIdentification.injective
  exact gluing.rightBoundary_embedding.injective hab

/-- The surface obtained by deleting the chosen discs and gluing their boundary circles. -/
noncomputable abbrev GluedSurface (gluing : DiscBoundaryGluing X Y) :=
  AdjunctionSpace gluing.attachingSubset gluing.attachingMap

/-- The canonical map from the left disc complement into the glued surface. -/
noncomputable def leftInclusion (gluing : DiscBoundaryGluing X Y) :
    gluing.LeftComplement → gluing.GluedSurface :=
  AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap

/-- The canonical map from the right disc complement into the glued surface. -/
noncomputable def rightInclusion (gluing : DiscBoundaryGluing X Y) :
    gluing.RightComplement → gluing.GluedSurface :=
  AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap

/-- The point of the attaching subset determined by a boundary parameter. -/
def leftBoundaryPoint (gluing : DiscBoundaryGluing X Y) (point : BoundaryCircle) :
    gluing.attachingSubset :=
  ⟨gluing.leftBoundary point, point, rfl⟩

/-- The attaching-subset point retains its underlying left-boundary value. -/
theorem leftBoundaryPoint_coe (gluing : DiscBoundaryGluing X Y)
    (point : BoundaryCircle) :
    (gluing.leftBoundaryPoint point : gluing.LeftComplement) =
      gluing.leftBoundary point := by
  -- The subtype package stores this boundary point as its value.
  rfl

/-- The attaching map sends each left boundary point to its identified right boundary point. -/
theorem attachingMap_leftBoundaryPoint (gluing : DiscBoundaryGluing X Y)
    (point : BoundaryCircle) :
    gluing.attachingMap (gluing.leftBoundaryPoint point) =
      gluing.rightBoundary (gluing.boundaryIdentification point) := by
  -- The inverse of the embedding homeomorphism recovers the boundary parameter.
  have hpoint : gluing.leftBoundaryHomeomorph.symm
      (gluing.leftBoundaryPoint point) = point := by
    apply gluing.leftBoundaryHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    rfl
  exact congrArg
    (fun parameter ↦ gluing.rightBoundary (gluing.boundaryIdentification parameter)) hpoint

/-- The glued surface identifies the paired points of the two boundary circles. -/
theorem glue (gluing : DiscBoundaryGluing X Y) (point : BoundaryCircle) :
    gluing.leftInclusion (gluing.leftBoundary point) =
      gluing.rightInclusion (gluing.rightBoundary (gluing.boundaryIdentification point)) := by
  -- Apply the adjunction relation and compute the attaching map on this boundary point.
  calc
    gluing.leftInclusion (gluing.leftBoundary point) =
        gluing.leftInclusion (gluing.leftBoundaryPoint point) := rfl
    _ = gluing.rightInclusion (gluing.attachingMap (gluing.leftBoundaryPoint point)) :=
      AdjunctionSpace.glue gluing.attachingSubset gluing.attachingMap
        (gluing.leftBoundaryPoint point)
    _ = gluing.rightInclusion
        (gluing.rightBoundary (gluing.boundaryIdentification point)) :=
      congrArg gluing.rightInclusion (gluing.attachingMap_leftBoundaryPoint point)


end DiscBoundaryGluing
