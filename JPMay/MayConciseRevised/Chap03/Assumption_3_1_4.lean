import Mathlib.Tactic.Recall
import Mathlib.Topology.Connected.LocPathConnected

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Assumption 3.1.4: the ambient spaces in Chapter 3 are assumed connected and locally path
connected unless explicitly stated otherwise, so the canonical ambient hypotheses are
`ConnectedSpace X` and `LocPathConnectedSpace X`. -/
recall ConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

/- Assumption 3.1.4 also uses the standard local path-connectedness hypothesis. -/
recall LocPathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop
