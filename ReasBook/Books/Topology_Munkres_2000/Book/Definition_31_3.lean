module

import Mathlib.Topology.Algebra.MulAction

/- Definition 31.3: An action of a topological group `G` on a topological space
`X` is represented by the canonical combination of `MulAction G X`, which gives
the laws `1 • x = x` and `(g₁ * g₂) • x = g₁ • g₂ • x`, and
`ContinuousSMul G X`, which says that `(g, x) ↦ g • x` is continuous. The
standing assumption that `G` is a topological group is `IsTopologicalGroup G`. -/
#check MulAction
#check ContinuousSMul
#check IsTopologicalGroup

-- The canonical action laws and joint-continuity projection.
#check one_smul
#check mul_smul
#check continuous_smul
