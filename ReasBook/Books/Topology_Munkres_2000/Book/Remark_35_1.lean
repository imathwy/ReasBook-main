module

import Mathlib.Topology.TietzeExtension

universe u

/-
Remark 35.1. The Tietze extension theorem extends a continuous real-valued map
from a closed subspace of a normal space to the whole ambient space.
-/
#check Real.instTietzeExtension
#check fun {X : Type u} [TopologicalSpace X] [NormalSpace X] {A : Set X}
    (hA : IsClosed A) (f : C(A, ℝ)) ↦ f.exists_restrict_eq hA
