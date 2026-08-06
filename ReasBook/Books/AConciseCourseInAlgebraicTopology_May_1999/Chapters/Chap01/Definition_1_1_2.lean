import Mathlib.Topology.Defs.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.1.2: a map `p : X → Y` is continuous when the inverse image of every open set in
`Y` is open in `X`; for metric spaces this agrees with the usual epsilon-delta formulation. -/
recall Continuous {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) : Prop
