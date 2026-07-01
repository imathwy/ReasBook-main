import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file is in the compact-open / locally uniform convergence domain.
-- The relevant owner declarations inspected before refinement were
-- `ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn`,
-- `ContinuousMap.tendsto_iff_tendstoLocallyUniformly`, and
-- `tendstoLocallyUniformly_iff_forall_isCompact`.
-- Layer triage: the textbook phrase "uniform convergence on compact subsets" is source-facing,
-- `Tendsto f p (𝓝 g)` in `C(D, E)` is the core/canonical owner for continuous maps, and the
-- locally compact bridge to `TendstoLocallyUniformly` is derived API.

variable {D E : Type*} [TopologicalSpace D] [UniformSpace E]

/- Definition V.1-extra-1. For continuous maps, "uniform convergence on compact subsets" is the
canonical compact-open convergence criterion. On a weakly locally compact domain, the same owner is
equivalent to locally uniform convergence. -/
#check ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn

#check ContinuousMap.tendsto_iff_tendstoLocallyUniformly
