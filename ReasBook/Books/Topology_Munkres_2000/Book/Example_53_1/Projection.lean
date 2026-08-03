module

public import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.FiberBundle.Constructions

public section

universe u v

/-- Projection from a product with a discrete second factor is a covering map. -/
theorem isCoveringMap_fst (X : Type u) (Y : Type v) [TopologicalSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] :
    IsCoveringMap (Prod.fst : X × Y → X) := by
  -- Transport the covering projection of the trivial bundle to the product model.
  convert
    (FiberBundle.isCoveringMap (F := Y) (E := Bundle.Trivial X Y)).comp_homeomorph
      (Bundle.Trivial.homeomorphProd X Y).symm using 1
  funext point
  rfl
