module

import Mathlib.Topology.Order.Basic

universe u v

/- Exercise 18.8 (1): For continuous maps into a simply ordered set with the order
topology, the pointwise comparison set is closed. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [LinearOrder Y]
    [TopologicalSpace Y] [OrderTopology Y] {f g : X → Y}
    (hf : Continuous f) (hg : Continuous g) ↦
  (isClosed_le hf hg : IsClosed {x | f x ≤ g x})

/- Exercise 18.8 (2): The pointwise minimum of continuous maps into a simply ordered
set with the order topology is continuous. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [LinearOrder Y]
    [TopologicalSpace Y] [OrderTopology Y] {f g : X → Y}
    (hf : Continuous f) (hg : Continuous g) ↦
  (hf.min hg : Continuous (fun x ↦ min (f x) (g x)))
