module

import Mathlib.Topology.Separation.Regular

/- Definition 2.99.6: The regularity axiom states that, given a closed set `A`
and a point `x ∉ A`, there exist disjoint open sets containing `A` and `x`,
respectively. This is exactly mathlib's `RegularSpace`; no `T₁` assumption is
part of the axiom itself. -/
#check RegularSpace
#check regularSpace_iff
