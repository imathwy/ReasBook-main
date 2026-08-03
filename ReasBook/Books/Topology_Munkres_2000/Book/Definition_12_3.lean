module

import Mathlib.Topology.Basic

open scoped Topology

universe u

/- Definition 12.3: A subset `U` of a type `X` is open with respect to a
topology `𝒯` when `IsOpen[𝒯] U` holds. The empty set and the whole space are
open, and open sets are closed under arbitrary unions and finite intersections. -/
#check fun {X : Type u} (𝒯 : TopologicalSpace X) (U : Set X) ↦ IsOpen[𝒯] U
#check isOpen_empty
#check isOpen_univ
#check isOpen_sUnion
#check Set.Finite.isOpen_sInter
