import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

variable (u : ℕ → ℝ)

/- Theorem 1.2.8: every `ℝ`-Cauchy sequence converges to a real number. This is the
specialization to `ℝ` of the general theorem that Cauchy sequences converge in complete spaces. -/
#check (cauchySeq_tendsto_of_complete : CauchySeq u → ∃ x : ℝ, Tendsto u atTop (𝓝 x))
