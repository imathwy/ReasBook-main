module

import Mathlib.Topology.Bases

universe u v

/- Remark 19.5: In the product topology on `(i : ι) → X i`, the finite
intersections of coordinate-projection preimages of open sets form a basis.
Equivalently, these are the open boxes restricted on a finite set of coordinates. -/
#check fun {ι : Type u} {X : ι → Type v} [(i : ι) → TopologicalSpace (X i)] ↦
  isTopologicalBasis_pi (fun _ ↦ TopologicalSpace.isTopologicalBasis_opens)

/- Intersecting two restrictions at the same coordinate produces one restriction
to the intersection of the two open sets. -/
#check Set.preimage_inter
