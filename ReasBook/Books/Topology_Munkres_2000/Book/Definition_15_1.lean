module

public import Mathlib.Topology.Bases

public section

universe u v

/- Definition 15.1: The product topology on `X × Y` is the canonical topology
whose basis consists of the open rectangles `U ×ˢ V`. -/
#check fun (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] ↦
  (inferInstance : TopologicalSpace (X × Y))
