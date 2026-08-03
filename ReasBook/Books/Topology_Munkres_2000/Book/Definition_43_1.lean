module

import Mathlib.Topology.MetricSpace.Cauchy

/- Definition 43.1 (1): A sequence `x : ℕ → X` is Cauchy exactly when, for every
`ε > 0`, its terms are pairwise within `ε` beyond some index. -/
#check Metric.cauchySeq_iff

/- Definition 43.1 (2): A metric space is complete when every Cauchy sequence
in the space converges. -/
#check CompleteSpace
#check cauchySeq_tendsto_of_complete
#check Metric.complete_of_cauchySeq_tendsto
