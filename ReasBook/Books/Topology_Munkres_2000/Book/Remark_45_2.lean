module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Equicontinuity

/- Remark 45.2: `Equicontinuous` uses the `UniformSpace` structure on the
codomain. Thus for a pseudometric space it depends on
`PseudoMetricSpace.toUniformSpace`, not merely on the induced
`TopologicalSpace`. -/
#check Equicontinuous
#check PseudoMetricSpace.toUniformSpace
#check UniformSpace.toTopologicalSpace
