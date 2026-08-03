module

import Mathlib.Topology.MetricSpace.Cauchy

/- Remark 43.1: For a sequence `u : ℕ → X` in a metric space, convergence implies
`CauchySeq u`; if `X` is complete, every Cauchy sequence converges. -/
#check Filter.Tendsto.cauchySeq
#check cauchySeq_tendsto_of_complete
#check Metric.complete_of_cauchySeq_tendsto
