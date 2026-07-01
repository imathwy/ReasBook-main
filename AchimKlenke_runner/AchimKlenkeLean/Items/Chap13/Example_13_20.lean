import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

-- Proof sketch: the convergence in distribution is immediate from
-- `tendstoInDistribution_of_identDistrib`; the primitive input is equality in distribution of the
-- tail variables with `X 0`, and the i.i.d. version is just its source-facing specialization.
private theorem tail_tendstoInDistribution_of_identDistrib
    {X : ℕ → Ω → E}
    (hX_ident : ∀ n : ℕ, IdentDistrib (X (n + 1)) (X 0) μ μ) :
    TendstoInDistribution (fun n ↦ X (n + 1)) atTop (X 0) (fun _ ↦ μ) μ := by
  refine tendstoInDistribution_of_identDistrib 0 (fun n ↦ ?_) (hX_ident 0)
  exact (hX_ident 0).trans (hX_ident n).symm

/-- If `X 0, X 1, X 2, ...` are i.i.d., then the tail sequence `X (n + 1)` converges in
distribution to `X 0`. -/
theorem iid_tail_tendstoInDistribution
    {X : ℕ → Ω → E}
    (hX_iid : IsIID X μ) :
    TendstoInDistribution (fun n ↦ X (n + 1)) atTop (X 0) (fun _ ↦ μ) μ := by
  exact tail_tendstoInDistribution_of_identDistrib (fun n ↦ hX_iid.identDistrib (n + 1) 0)

end

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type v} [MetricSpace E] [MeasurableSpace E]
variable [BorelSpace E]

/-- If `X 0, X 1, X 2, ...` are independent, identically distributed, and the common law is
nontrivial, then the tail sequence `X (n + 1)` does not converge in probability to `X 0`. The
metric assumption rules out the pseudometric pathology where distinct points can still have
distance `0`. -/
theorem iid_tail_not_tendstoInMeasure
    {X : ℕ → Ω → E}
    (hX_iid : IsIID X μ)
    (h_nontrivial : ¬ ∃ c : E, X 0 =ᵐ[μ] fun _ ↦ c) :
    ¬ TendstoInMeasure μ (fun n ↦ X (n + 1)) atTop (X 0) := sorry

/-- Example 13.20: if `X 0, X 1, X 2, ...` are i.i.d. and the common distribution is nontrivial,
then the tail sequence `X (n + 1)` converges in distribution to `X 0`, but it does not converge
in probability to `X 0`. -/
theorem iid_tail_tendstoInDistribution_not_tendstoInMeasure
    {X : ℕ → Ω → E}
    (hX_iid : IsIID X μ)
    (h_nontrivial : ¬ ∃ c : E, X 0 =ᵐ[μ] fun _ ↦ c) :
    TendstoInDistribution (fun n ↦ X (n + 1)) atTop (X 0) (fun _ ↦ μ) μ ∧
      ¬ TendstoInMeasure μ (fun n ↦ X (n + 1)) atTop (X 0) := by
  exact ⟨iid_tail_tendstoInDistribution hX_iid, iid_tail_not_tendstoInMeasure hX_iid h_nontrivial⟩

end
