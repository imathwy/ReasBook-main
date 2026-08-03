module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence

/- Remark 21.2: Uniform convergence depends on the metric of the codomain through
its induced `UniformSpace`, not merely through the resulting topology. -/
#check TendstoUniformly
#check PseudoMetricSpace.toUniformSpace
#check UniformSpace.toTopologicalSpace
