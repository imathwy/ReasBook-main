import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped NNReal Topology

variable {α : Type u} {F : Type v} [NormedAddCommGroup F]

/-- Definition I.2-extra-2: a series of functions is normally convergent on `s` if it admits a
summable `ℝ≥0`-valued majorant that bounds the norm of each term uniformly on `s`. -/
def NormallyConvergentOn (f : ℕ → α → F) (s : Set α) : Prop :=
  ∃ C : ℕ → ℝ≥0, Summable C ∧ ∀ n, ∀ x ∈ s, ‖f n x‖ ≤ C n

-- Proof sketch: choose the summable majorant from `NormallyConvergentOn` and apply
-- `Summable.of_nonneg_of_le` pointwise at `x`.
/-- Pointwise absolute convergence follows from normal convergence on `s`. -/
theorem NormallyConvergentOn.summable_norm_apply {f : ℕ → α → F} {s : Set α}
    (h : NormallyConvergentOn f s) {x : α} (hx : x ∈ s) :
    Summable (fun n ↦ ‖f n x‖) := by
  rcases h with ⟨C, hC, hC_bound⟩
  exact Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ hC_bound n x hx)
    (NNReal.summable_coe.2 hC)

-- Proof sketch: unpack the summable majorant from `NormallyConvergentOn` and invoke
-- `HasSumUniformlyOn.of_norm_le_summable`.
/-- Normal convergence on `s` gives uniform convergence of the partial sums on `s`
to the pointwise infinite sum. -/
theorem NormallyConvergentOn.hasSumUniformlyOn {f : ℕ → α → F} {s : Set α} [CompleteSpace F]
    (h : NormallyConvergentOn f s) :
    HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  rcases h with ⟨C, hC, hC_bound⟩
  simpa using HasSumUniformlyOn.of_norm_le_summable (NNReal.summable_coe.2 hC)
    (fun n x hx ↦ hC_bound n x hx)

-- Proof sketch: combine the uniform convergence obtained from `NormallyConvergentOn` with the
-- continuity of each term through `continuousOn_tsum`.
/-- A normally convergent series of continuous functions is continuous on the set of normal
convergence. -/
theorem NormallyConvergentOn.continuousOn_tsum {f : ℕ → α → F} {s : Set α}
    [TopologicalSpace α] [CompleteSpace F] (h : NormallyConvergentOn f s)
    (hf : ∀ n, ContinuousOn (f n) s) :
    ContinuousOn (fun x ↦ ∑' n, f n x) s := by
  rcases h with ⟨C, hC, hC_bound⟩
  exact _root_.continuousOn_tsum hf (NNReal.summable_coe.2 hC) fun n x hx ↦ hC_bound n x hx
