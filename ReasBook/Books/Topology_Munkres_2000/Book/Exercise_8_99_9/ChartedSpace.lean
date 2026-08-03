module

public import Mathlib.Geometry.Manifold.HasGroupoid
public import Mathlib.Topology.Connected.LocallyConnected

public section

universe u v

namespace ConnectedComponent

variable {H : Type u} {X : Type v} [TopologicalSpace H] [TopologicalSpace X]

/-- Connected components are open when the ambient chart model is locally connected. -/
theorem isOpen_of_chartedSpace (H : Type u) [TopologicalSpace H] [LocallyConnectedSpace H]
    [ChartedSpace H X] (x : X) : IsOpen (connectedComponent x) := by
  exact @isOpen_connectedComponent X _ (ChartedSpace.locallyConnectedSpace H X) x

/-- A connected component inherits the charted-space structure of a locally connected model. -/
noncomputable instance instChartedSpace [LocallyConnectedSpace H] [ChartedSpace H X] (x : X) :
    ChartedSpace H (connectedComponent x) :=
  (⟨connectedComponent x, isOpen_of_chartedSpace H x⟩ :
    TopologicalSpace.Opens X).instChartedSpace

end ConnectedComponent
