module

import Mathlib.Topology.Defs.Induced

universe u

/- Remark 16.1: For a topological space `X` and a subspace `Y`, the phrase
"open set" is ambiguous: it can mean `IsOpen U` for `U : Set X`, or `IsOpen U`
for `U : Set Y`, where `Y` carries its canonical subtype topology. -/
#check fun {X : Type u} [TopologicalSpace X] (U : Set X) ↦ IsOpen U
#check fun {X : Type u} [TopologicalSpace X] (Y : Set X) (U : Set Y) ↦ IsOpen U
