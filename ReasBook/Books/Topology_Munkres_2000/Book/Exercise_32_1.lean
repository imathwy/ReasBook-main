module

import Mathlib.Topology.Separation.Regular

universe u

public section

variable {X : Type u} [TopologicalSpace X] [T4Space X]
variable {A : Set X} (hA : IsClosed A)

/- Exercise 32.1: A closed subspace of a normal space is normal.
Here `T4Space` expresses the book's convention that a normal space is also `T₁`. -/
#check hA.isClosedEmbedding_subtypeVal.t4Space

end
