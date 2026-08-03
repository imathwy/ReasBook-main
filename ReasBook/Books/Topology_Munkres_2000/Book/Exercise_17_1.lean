module

import Mathlib.Topology.Basic

/- Exercise 17.1: If `𝒞` contains `∅` and `Set.univ` and is closed under finite
unions and arbitrary intersections, then the complements of members of `𝒞`
form a topology. This is exactly `TopologicalSpace.ofClosed`; its arbitrary
intersection hypothesis already implies `Set.univ ∈ 𝒞`. -/
#check TopologicalSpace.ofClosed
