import Mathlib
import cartan.I.section02.«0002_Definition_I_2_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Topology

variable {α : Type u} {F : Type v} [TopologicalSpace α] [NormedAddCommGroup F] [CompleteSpace F]

-- Proof sketch: apply `tendsto_tsum_of_dominated_convergence` to the filter `𝓝 x₀`, using the
-- summable majorant supplied by `NormallyConvergentOn u Set.univ` and the termwise limits `ha`.
/-- Proposition 1.2: if `u n x` tends to `a n` as `x` tends to `x₀`, then a normally convergent
series `∑ n, u n x` on the whole space may be summed termwise through the limit. This is the
`NormallyConvergentOn` reformulation of mathlib's canonical Tannery theorem
`tendsto_tsum_of_dominated_convergence`. -/
theorem NormallyConvergentOn.tendsto_tsum
    {u : ℕ → α → F} {x₀ : α} {a : ℕ → F}
    (h : NormallyConvergentOn u Set.univ)
    (ha : ∀ n, Tendsto (u n) (𝓝 x₀) (𝓝 (a n))) :
    Tendsto (fun x ↦ ∑' n, u n x) (𝓝 x₀) (𝓝 (∑' n, a n)) := by
  rcases h with ⟨C, hC, hC_bound⟩
  simpa using
    tendsto_tsum_of_dominated_convergence (NNReal.summable_coe.2 hC) ha <|
      Eventually.of_forall fun x n ↦ hC_bound n x (by simp)
