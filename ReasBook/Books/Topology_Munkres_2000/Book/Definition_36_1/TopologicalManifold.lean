module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace

public section

universe u

/-- A topological `m`-manifold is a Hausdorff second-countable space equipped with
charts in `EuclideanSpace ℝ (Fin m)`. -/
class TopologicalManifold (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] : Prop extends T2Space X,
      SecondCountableTopology X

namespace TopologicalManifold

/-- The topological `m`-manifold property for a specified charted-space structure. -/
def With (m : ℕ) {X : Type u} [TopologicalSpace X]
    (charts : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) : Prop :=
  -- Local instance justification (explicit choice): this view evaluates the canonical class
  -- using the charted-space structure supplied as its explicit mathematical input.
  letI : ChartedSpace (EuclideanSpace ℝ (Fin m)) X := charts
  TopologicalManifold m X

/-- A specified charted-space structure makes `X` a topological `m`-manifold exactly when
`X` is Hausdorff and second countable. -/
theorem with_iff (m : ℕ) {X : Type u} [TopologicalSpace X]
    (charts : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) :
    With m charts ↔ T2Space X ∧ SecondCountableTopology X := by
  constructor
  · intro h
    exact ⟨h.toT2Space, h.toSecondCountableTopology⟩
  · rintro ⟨hT2, hSecondCountable⟩
    exact { toT2Space := hT2, toSecondCountableTopology := hSecondCountable }

/-- Bundle Hausdorffness and second countability into the topological manifold property. -/
theorem of (m : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] (hT2 : T2Space X)
    (hSecondCountable : SecondCountableTopology X) : TopologicalManifold m X :=
  { toT2Space := hT2, toSecondCountableTopology := hSecondCountable }

end TopologicalManifold
