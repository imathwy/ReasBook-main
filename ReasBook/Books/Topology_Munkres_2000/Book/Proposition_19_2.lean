module

import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct

universe u v

open scoped CartesianProduct

/- Proposition 19.2: Passing from finite or positive-integer indexing to an
arbitrary index type `J`, the Cartesian product of a type family `X` is its
dependent function type. For a family of subsets of one ambient type, the
existing notation `∏ j, A j` gives the corresponding set of choice functions. -/
#check fun {J : Type u} (X : J → Type v) ↦ ((j : J) → X j)
#check fun {J : Type u} {X : Type v} (A : J → Set X) ↦ ∏ j, A j
