module

import Mathlib.Topology.UniformSpace.CompactConvergence

/- Remark 46.2: The compact-open topology exists on the space `C(X, Y)` of
continuous maps for arbitrary topological spaces `X` and `Y`. When `Y` is a
uniform space, convergence in this topology is exactly uniform convergence on
every compact subset of `X`; in particular this applies to metric codomains. -/
#check ContinuousMap.compactOpen
#check ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn
