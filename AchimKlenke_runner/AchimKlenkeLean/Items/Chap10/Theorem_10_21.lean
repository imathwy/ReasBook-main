import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

/- Theorem 10.21 is `source-facing`: its public content is the finite-stopping-time extension of
optional sampling for uniformly integrable martingales and supermartingales. Its
`core/canonical` owner remains the mathlib theorem
`Martingale.stoppedValue_ae_eq_condExp_of_le` on `ℕ∞`-valued stopping times. The only
`bridge/view` layer used here is the finite-time coercion `Ω → ℕ` to `Ω → ℕ∞`, so the public API
keeps the source-facing finite stopping times while reusing the owner-shaped stopped-value
expressions directly. -/
variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {σ τ : Ω → ℕ}

local notation "σ∞" => fun ω ↦ (σ ω : ℕ∞)
local notation "τ∞" => fun ω ↦ (τ ω : ℕ∞)

-- Proof sketch: apply the bounded optional sampling identity to the truncations `σ ∧ n` and
-- `τ ∧ n`, use uniform integrability to upgrade convergence in measure of the stopped values to
-- convergence in `L¹`, and then pass the conditional expectations to the limit.
/-- Theorem 10.21 (1): if `X` is a uniformly integrable martingale and `σ ≤ τ` are finite
stopping times, then `stoppedValue X τ` is integrable and its conditional expectation with respect
to `𝓕_σ` agrees almost surely with `stoppedValue X σ`. -/
theorem martingale_condExp_stoppedValue_ae_eq_of_uniformIntegrable_of_le_of_finite
    (hX : Martingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ)
    (hσ : IsStoppingTime ℱ σ∞) (hτ : IsStoppingTime ℱ τ∞) (hστ : σ ≤ τ) :
    Integrable (stoppedValue X τ∞) μ ∧
      μ[stoppedValue X τ∞ | hσ.measurableSpace] =ᵐ[μ] stoppedValue X σ∞ := sorry

-- Proof sketch: write the uniformly integrable supermartingale as the sum of its martingale part
-- and its decreasing predictable part, apply the martingale optional sampling identity to the
-- martingale part, and use monotonicity of the predictable part and of conditional expectation to
-- obtain the inequality.
/-- Theorem 10.21 (2): if `X` is a uniformly integrable supermartingale and `σ ≤ τ` are finite
stopping times, then `stoppedValue X τ` is integrable and its conditional expectation with respect
to `𝓕_σ` is almost surely bounded above by `stoppedValue X σ`. -/
theorem supermartingale_condExp_stoppedValue_ae_le_of_uniformIntegrable_of_le_of_finite
    (hX : Supermartingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ)
    (hσ : IsStoppingTime ℱ σ∞) (hτ : IsStoppingTime ℱ τ∞) (hστ : σ ≤ τ) :
    Integrable (stoppedValue X τ∞) μ ∧
      μ[stoppedValue X τ∞ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X σ∞ := sorry
