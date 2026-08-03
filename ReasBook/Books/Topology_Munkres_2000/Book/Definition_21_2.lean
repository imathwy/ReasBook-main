module

import Mathlib.Topology.MetricSpace.Basic

public section

universe u v

variable {X : Type u} {Y : Type v} [MetricSpace Y]
variable (f : ℕ → X → Y) (g : X → Y)

/- Definition 21.2. A sequence `f : ℕ → X → Y` converges uniformly to
`g : X → Y` when one index bound works for every `x : X` at each positive
metric tolerance. -/
#check TendstoUniformly f g Filter.atTop

/- In a metric space, this is exactly the ε–`Filter.atTop` formulation from the
definition. -/
#check (Metric.tendstoUniformly_iff :
  TendstoUniformly f g Filter.atTop ↔
    ∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ x, dist (g x) (f n x) < ε)
