module

import Mathlib.Topology.Connected.LocallyPathConnected
import Topology_Munkres_2000.Book.Definition_53_2.Covering

public section

universe u v

/- Assumption 13.0.1: Throughout this chapter, saying that `p : E → B` is a
covering map includes the assumptions that `E` and `B` are locally path connected
and path connected, unless specifically stated otherwise. -/
#check fun {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B] (p : E → B) ↦
  IsSurjectiveCoveringMap p
