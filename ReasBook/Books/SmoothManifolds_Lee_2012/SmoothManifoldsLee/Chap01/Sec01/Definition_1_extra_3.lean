import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Tactic.Recall

universe u

/- Definition 1-extra-3: the canonical mathlib notions for the recalled properties of a
topological space are `ConnectedSpace X`, `PathConnectedSpace X`, and
`LocPathConnectedSpace X`. -/
recall ConnectedSpace (X : Type u) [TopologicalSpace X] : Prop
recall PathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop
recall LocPathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop
