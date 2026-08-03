module

import Mathlib.Data.PNat.Interval
import Mathlib.Topology.Instances.PNat
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

public section

/- Remark 21.1: Some order topologies are metrizable, including those on the
positive integers and on `ℝ`, while other order topologies are not metrizable. -/
#check (inferInstance : OrderTopology ℕ+)
#check (inferInstance : TopologicalSpace.MetrizableSpace ℕ+)
#check (inferInstance : OrderTopology ℝ)
#check (inferInstance : TopologicalSpace.MetrizableSpace ℝ)
