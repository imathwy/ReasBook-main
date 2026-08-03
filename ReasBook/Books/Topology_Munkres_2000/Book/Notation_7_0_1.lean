module

import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.MetricSpace.Defs

public section

universe u v

/- Notation 7.0.1: For a topological space `X` and a metric space `Y`, `C(X, Y)`
is the bundled type of continuous maps from `X` to `Y`. The uniform metric and
its completeness properties are developed later. -/
#check fun (X : Type u) (Y : Type v) [TopologicalSpace X] [MetricSpace Y] ↦ C(X, Y)
