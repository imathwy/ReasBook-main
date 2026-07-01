import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u}
variable {E : Type v} [TopologicalSpace E]

-- Proof sketch: fix a sample point `ω`. Along that path, the map `t ↦ min t (τ ω).untopA` is
-- right continuous, so composing the right-continuous path `t ↦ X t ω` with this time change
-- preserves right continuity.
/-- Exercise 21.1.3 (7): the stopped process of a right-continuous process is still right
continuous. -/
theorem stoppedProcess_hasRightContinuousPaths
    {X : NNReal → Ω → E} (hX_rc : HasRightContinuousPaths X) {τ : Ω → ENNReal} :
    HasRightContinuousPaths (stoppedProcess X τ) := sorry

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration NNReal mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X Y : NNReal → Ω → ℝ}

/-- The dyadic ceiling approximation `t ↦ 2^{-n} ⌈2^n t⌉` applied pointwise to a nonnegative random
time. -/
def dyadicCeilApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

-- Proof sketch: for each deterministic time `t`, the event
-- `{dyadicCeilApprox n τ ≤ t}` can be rewritten as `{τ ≤ k / 2^n}` for the appropriate dyadic
-- predecessor of `t`; this is measurable because `τ` is a stopping time.
/-- The dyadic ceiling approximation of a finite nonnegative stopping time is again a stopping
time. -/
theorem dyadicCeilApprox_isStoppingTime {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal) := sorry

-- Proof sketch: the dyadic ceilings `σⁿ` decrease to `σ`, so the stopping-time σ-algebras
-- `𝓕_{σⁿ}` decrease to `𝓕_σ`; backward martingale convergence then gives both almost-sure and
-- `L¹` convergence of the conditional expectations of the fixed integrable random variable
-- `X_{τ^m}`.
/-- Exercise 21.1.3 (1): for fixed `m`, the conditional expectations of `X_{τ^m}` with respect to
the dyadic stopping-time σ-algebras `𝓕_{σ^n}` converge almost surely and in `L¹` to the
conditional expectation with respect to `𝓕_σ`. -/
theorem dyadic_condExp_stoppedValue_tendsto_of_bounded_stopping_times
    (hX : Supermartingale X ℱ μ)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
    (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) (m : ℕ) :
    (∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦
          μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
            (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
        atTop
        (𝓝
          (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
            hσ.measurableSpace] ω))) ∧
      Tendsto
        (fun n ↦
          eLpNorm
            (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] -
              μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                hσ.measurableSpace])
            1 μ)
        atTop (𝓝 0) := sorry

-- Proof sketch: right continuity of the sample paths gives pointwise convergence
-- `X_{σ^n} → X_σ`, and boundedness of the stopping times upgrades the sampled family to a
-- uniformly integrable one, yielding convergence in `L¹`.
/-- Exercise 21.1.3 (2): the dyadic ceiling samples `X_{σ^n}` converge almost surely and in `L¹`
to `X_σ`. -/
theorem dyadic_stoppedValue_tendsto_of_bounded_stopping_times
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T) :
    (∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ X (dyadicCeilApprox n σ ω) ω) atTop (𝓝 (X (σ ω) ω))) ∧
      Tendsto
        (fun n ↦ eLpNorm (fun ω ↦ X (dyadicCeilApprox n σ ω) ω - X (σ ω) ω) 1 μ)
        atTop (𝓝 0) := sorry

-- Proof sketch: approximate `σ` and `τ` from above by their dyadic ceilings, apply the
-- discrete-time optional sampling theorem to the dyadic skeleton, and then pass to the limit using
-- the convergence statements from the preceding two parts.
/-- Exercise 21.1.3 (3): a right-continuous supermartingale satisfies the optional sampling
inequality for bounded stopping times `σ ≤ τ`. -/
theorem supermartingale_condExp_stoppedValue_ae_le_of_le_of_bounded_rightContinuous
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hστ : σ ≤ τ) (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) :
    μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
      stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := sorry

-- Proof sketch: the forward implication is the martingale case of optional sampling. For the
-- converse, test the expectation identity on bounded stopping times obtained from deterministic
-- times and events in `𝓕_s`, and recover the martingale conditional-expectation identity at
-- deterministic times.
/-- Exercise 21.1.3 (4): an adapted integrable process is a martingale if and only if every
bounded stopping time preserves its initial expectation. -/
theorem martingale_iff_expected_stoppedValue_eq_initial_of_bounded_stopping_times
    (hY_adapted : Adapted ℱ Y) (hY_int : ∀ t : NNReal, Integrable (Y t) μ) :
    Martingale Y ℱ μ ↔
      ∀ τ : Ω → NNReal, IsStoppingTime ℱ (fun ω ↦ (τ ω : ENNReal)) →
        (∃ T : NNReal, ∀ ω, τ ω ≤ T) →
          μ[stoppedValue Y (fun ω ↦ (τ ω : ENNReal))] = μ[Y 0] := sorry

-- Proof sketch: truncate the finite stopping times by deterministic bounds, apply the bounded
-- optional sampling inequality to the truncations, use uniform integrability and right continuity
-- to pass the stopped values to the limit in `L¹`, and retain both the integrability of
-- `X_τ` and the limiting conditional-expectation inequality.
/-- Exercise 21.1.3 (5): if `X` is uniformly integrable and `σ ≤ τ` are finite stopping times,
then `X_τ` is integrable and the optional sampling inequality still holds without boundedness. -/
theorem supermartingale_condExp_stoppedValue_ae_le_of_uniformIntegrable_of_le
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    (hX_UI : UniformIntegrable X 1 μ)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hστ : σ ≤ τ) :
    Integrable (stoppedValue X (fun ω ↦ (τ ω : ENNReal))) μ ∧
      μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := sorry

-- Proof sketch: for deterministic times `s ≤ t`, identify
-- `stoppedProcess X τ t = X_{τ ∧ t}` and apply the bounded optional sampling inequality from part
-- (3) to the stopping times `τ ∧ s` and `τ ∧ t`.
/-- Exercise 21.1.3 (6): for an arbitrary stopping time `τ`, the stopped process
`(X_{τ ∧ t})_{t ≥ 0}` is again a supermartingale. -/
theorem stoppedProcess_supermartingale_of_optional_stopping
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ) :
    Supermartingale (stoppedProcess X τ) ℱ μ := sorry
end ProbabilityTheory
