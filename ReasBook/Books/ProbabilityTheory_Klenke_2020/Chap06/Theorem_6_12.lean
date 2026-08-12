import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

section RealValued

-- Proof sketch: apply Markov's inequality to the deviation events
-- `{ω | ε < |fSeq n ω - f ω|}` to reduce to the summable real series of `L^p`-distances, then
-- invoke Borel-Cantelli and pass from `|fSeq n - f| → 0` to pointwise convergence.
/-- Theorem 6.12 (1): If the real-valued measurable maps `fₙ` all belong to `L^p(μ)` for some
`1 ≤ p < ∞`, the limit map `f` also belongs to `L^p(μ)`, and `∑ ‖fₙ - f‖ₚ < ∞`, then `fₙ`
converges to `f` almost everywhere. -/
theorem tendsto_ae_of_summable_lpNorm_sub
    (μ : Measure Ω) (fSeq : ℕ → Ω → ℝ) (f : Ω → ℝ) (p : ℝ≥0∞)
    (h_meas : ∀ n, Measurable (fSeq n))
    (hf_meas : Measurable f)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hfSeq_mem : ∀ n, MemLp (fSeq n) p μ)
    (hf_mem : MemLp f p μ)
    (h_sum : Summable fun n ↦ lpNorm (fSeq n - f) p μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := sorry

end RealValued

section MetricValued

variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

-- Proof sketch: for each `ε > 0`, apply Borel-Cantelli to the deviation sets
-- `A ∩ {ω | ε < dist (f ω) (fSeq n ω)}` on every finite-measure measurable set `A`; then take the
-- union over `ε = 1 / m` to obtain pointwise convergence outside a null set.
/-- Theorem 6.12 (2): If the deviation measures
`μ (A ∩ {ω | ε < dist (f ω) (fₙ ω)})` form a summable series for every `ε > 0` and every
measurable finite-measure set `A`, then `fₙ` converges to `f` almost everywhere. -/
theorem tendsto_ae_of_summable_deviation_measures_on_finite_sets
    (μ : Measure Ω) (fSeq : ℕ → Ω → E) (f : Ω → E)
    (h_meas : ∀ n, Measurable (fSeq n))
    (hf_meas : Measurable f)
    (h_sum : ∀ A, MeasurableSet A → μ A < ∞ →
      ∀ ε : ℝ, 0 < ε →
        Summable (fun n ↦ μ (A ∩ {ω | ε < dist (f ω) (fSeq n ω)}))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := sorry

-- Proof sketch: Borel-Cantelli shows that, outside a null set, only finitely many increments
-- violate the bounds `dist (fₙ, fₙ₊₁) ≤ εₙ`. Since `∑ εₙ` converges, the pointwise sequence is
-- Cauchy there; completeness gives a limit, and separability/measurability yield a measurable
-- version of that limit.
/-- Theorem 6.12 (3): In a complete separable metric space, if the successive deviation sets
`A ∩ {ω | εₙ < dist (fₙ ω) (fₙ₊₁ ω)}` have summable measures on every measurable finite-measure
set `A` for some summable nonnegative sequence `εₙ`, then the measurable maps `fₙ` converge almost
everywhere to a measurable limit. -/
theorem exists_measurable_tendsto_ae_of_summable_successive_deviation_measures
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    (μ : Measure Ω) (fSeq : ℕ → Ω → E) (εSeq : ℕ → ℝ)
    (h_meas : ∀ n, Measurable (fSeq n))
    (hε_nonneg : ∀ n, 0 ≤ εSeq n)
    (hε_summable : Summable εSeq)
    (h_sum : ∀ A, MeasurableSet A → μ A < ∞ →
      Summable (fun n ↦ μ (A ∩ {ω | εSeq n < dist (fSeq n ω) (fSeq (n + 1) ω)}))) :
    ∃ f : Ω → E, Measurable f ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := sorry

end MetricValued
