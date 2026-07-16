import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap10.Corollary_10_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal MeasureTheory

open MeasureTheory

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ] {τ : ℕ → Ω → ℕ}

/- Corollary 10.22 is `source-facing`: it keeps the sampled martingale and supermartingale
processes indexed by the original finite stopping-time sequence. The owner filtration abstraction is
the chapter-level `stoppingTimeSequenceFiltration` from Corollary 10.12, while the finite optional
sampling input comes from Theorem 10.21. The primitive ambient hypothesis for that owner API is
`[SigmaFiniteFiltration μ ℱ]`, so this file exposes exactly that canonical assumption instead of
the stronger derived instance `[IsFiniteMeasure μ]`. -/

local notation "τ∞" => fun n ω ↦ (τ n ω : ℕ∞)

section

variable {X : ℕ → Ω → ℝ}
variable (hτ : ∀ n, IsStoppingTime ℱ (τ∞ n)) (hmono : Monotone τ)

private theorem monotone_tauInf (hmono : Monotone τ) : Monotone τ∞ := by
  intro i j hij ω
  exact WithTop.coe_le_coe.2 (hmono hij ω)

local notation "ℱτ" =>
  stoppingTimeSequenceFiltration ℱ τ∞ hτ (monotone_tauInf hmono)

/-- Corollary 10.22 (1): sampling a uniformly integrable martingale along an increasing sequence of
finite stopping times yields a martingale with respect to the filtration formed by the
corresponding stopping-time `σ`-algebras. -/
-- Proof sketch: apply the uniformly integrable optional sampling identity from Theorem 10.21 to
-- each pair `τ m ≤ τ n` with `m ≤ n`; the monotonicity of the stopping times makes the
-- corresponding stopping-time `σ`-algebras into an increasing filtration.
theorem stoppedValue_martingale_of_uniformIntegrable_of_monotone_finite_stopping_times
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Martingale (fun n ↦ stoppedValue X (τ∞ n)) ℱτ μ := sorry

/-- Corollary 10.22 (2): sampling a uniformly integrable supermartingale along an increasing
sequence of finite stopping times yields a supermartingale with respect to the filtration formed by
the corresponding stopping-time `σ`-algebras. -/
-- Proof sketch: apply the supermartingale form of Theorem 10.21 to each pair `τ m ≤ τ n`, and use
-- the monotonicity of the stopping times to view the stopping-time `σ`-algebras as an increasing
-- filtration.
theorem stoppedValue_supermartingale_of_uniformIntegrable_of_monotone_finite_stopping_times
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Supermartingale (fun n ↦ stoppedValue X (τ∞ n)) ℱτ μ := sorry

end

end
