import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe uG uK

variable {G : Type uG} [Monoid G] [TopologicalSpace G] [PreconnectedSpace G]
variable {K : Type uK} [TopologicalSpace K] [DiscreteTopology K] [MulAction G K]
variable [ContinuousSMul G K]

-- The source-facing statement is proved directly from the canonical owners
-- `IsLocallyConstant.iff_continuous`, `IsLocallyConstant.apply_eq_of_preconnectedSpace`, and
-- `Continuous.smul`; no chapter-local orbit-map wrapper is needed here.

/-- Problem 7-8: a continuous action of a preconnected topological monoid on a discrete space `K`
is trivial. In particular, this applies to connected topological groups. -/
theorem continuous_action_on_discrete_is_trivial (g : G) (x : K) : g • x = x := by
  simpa using
    ((IsLocallyConstant.iff_continuous (fun h : G ↦ h • x)).2
      (continuous_id.smul continuous_const)).apply_eq_of_preconnectedSpace g (1 : G)
