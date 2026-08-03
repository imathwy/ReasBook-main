module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Mathlib.Topology.Separation.Regular

public section

universe u v

/-- A normal space is an absolute retract when the range of every closed embedding into a
normal space is a retract of the ambient space. -/
class AbsoluteRetract (Y : Type v) [TopologicalSpace Y] [T4Space Y] : Prop where
  /-- An absolute retract is a retract of every normal space in which it is closedly embedded. -/
  isRetract_range {Z : Type u} [TopologicalSpace Z] [T4Space Z] (e : Y → Z)
    (he : Topology.IsClosedEmbedding e) : Set.IsRetract (Set.range e)
