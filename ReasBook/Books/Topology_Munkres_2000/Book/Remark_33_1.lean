module

import Mathlib.Topology.Separation.Regular

/- Remark 33.1: In a regular space, `exists_mem_nhds_isClosed_subset` shrinks the neighborhood
`U₁` of `a` to a closed neighborhood; its interior is an open neighborhood `U₀`
whose closure is contained in `U₁`. The next step asks for an open `Uₚ` with
`closure U₀ ⊆ Uₚ` and `closure Uₚ ⊆ U₁`. Taking `s = closure U₀`, `t = U₁`,
and `u = Uₚ`, this is exactly the normal-space interpolation supplied by
`normal_exists_closure_subset`; regularity alone does not supply this step. -/
#check exists_mem_nhds_isClosed_subset
#check normal_exists_closure_subset
