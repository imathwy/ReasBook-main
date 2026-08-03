module

import Mathlib.Topology.MetricSpace.Defs

/- Definition 20.2: In a metric space, `dist x y` is the distance from `x` to `y`.
For `ε > 0`, `Metric.ball x ε` is the `ε`-ball centered at `x`, and its points
are exactly the `y` satisfying `dist x y < ε`. -/
#check dist
#check Metric.ball
#check Metric.mem_ball'
