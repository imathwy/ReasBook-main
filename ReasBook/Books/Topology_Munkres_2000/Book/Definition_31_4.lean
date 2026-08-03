module

import Mathlib.Topology.Algebra.MulAction

/- Definition 31.4: Given a continuous action of a topological group `G` on a
topological space `X`, the relation identifying points in the same `G`-orbit is
`MulAction.orbitRel G X`. The orbit space denoted `X/G` is
`MulAction.orbitRel.Quotient G X`, and its inherited `TopologicalSpace` instance
is the quotient topology for the canonical projection `Quotient.mk''`. -/
#check MulAction.orbitRel
#check MulAction.orbitRel.Quotient

-- The relation and the canonical projection have the expected orbit-space descriptions.
#check MulAction.orbitRel_apply
#check Quotient.mk''
#check Quotient.eq''
#check continuous_quotient_mk'
#check isQuotientMap_quotient_mk'
