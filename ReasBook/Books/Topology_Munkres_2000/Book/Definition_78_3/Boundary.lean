module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.Instances.Real

open scoped Manifold

public section

universe u

namespace Surface

/-- The surface-with-boundary condition for a specified half-space charted-space structure. -/
def IsManifoldWithBoundary {X : Type u} [TopologicalSpace X]
    (charts : ChartedSpace (EuclideanHalfSpace 2) X) : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 2)) _ _ (EuclideanHalfSpace 2) _
      (modelWithCornersEuclideanHalfSpace 2) 0 X _ charts

/-- The three defining conditions for a specified half-space atlas to make a space a
surface with boundary. -/
theorem isManifoldWithBoundary_iff {X : Type u} [TopologicalSpace X]
    (charts : ChartedSpace (EuclideanHalfSpace 2) X) :
    IsManifoldWithBoundary charts ↔
      T2Space X ∧ SecondCountableTopology X ∧
        @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 2)) _ _ (EuclideanHalfSpace 2) _
          (modelWithCornersEuclideanHalfSpace 2) 0 X _ charts :=
  Iff.rfl

/-- The boundary of a surface modeled on `EuclideanHalfSpace 2`. -/
abbrev boundary (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X] :=
  (𝓡∂ 2).boundary X

/-- The boundary determined by a specified half-space charted-space structure. -/
abbrev boundaryWith {X : Type u} [TopologicalSpace X]
    (charts : ChartedSpace (EuclideanHalfSpace 2) X) :=
  @boundary X _ charts

end Surface

/- The boundary `∂X` of a surface with boundary, realized by the canonical
model-with-corners boundary for `EuclideanHalfSpace 2`. -/
scoped[SurfaceBoundary] notation "∂" X:arg => Surface.boundary X
