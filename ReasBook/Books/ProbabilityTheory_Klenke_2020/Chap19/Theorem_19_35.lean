import ProbabilityTheory_Klenke_2020.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Chap19.Theorem_19_33
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Layering for Theorem 19.35:
- `source-facing`: a sampled one-dimensional environment `W : Ω → RandomEnvironment`, the site
  law of the logarithmic Solomon ratios `log ρ_x`, and the quenched almost-sure drift/oscillation
  conclusions for the walk in the realized environment `W ω`.
- `core/canonical`: for each fixed environment sample `ω`, the Chapter 19 owner
  `W ω .IsElliptic` together with `IsMarkovProcessRealization
    (fun n ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)`.
- `bridge/view`: the almost-sure Solomon series regimes `R⁻[W ω]`, `R⁺[W ω]` from
  `Theorem_19_33`, obtained from the sign of `∫ log ρ₀`. -/

/-- The logarithmic local Solomon ratio `log ρ_x` of the sampled environment `W ω`. This is the
real-valued source quantity that appears in Solomon's criterion. -/
def randomEnvironmentLogRatio (W : Ω → RandomEnvironment) (x : ℤ) : Ω → ℝ :=
  fun ω ↦
    Real.log
      (((((1 : ℝ≥0) - ((W ω).rightJumpProb x)) / ((W ω).rightJumpProb x) : ℝ≥0) : ℝ))

scoped[ProbabilityTheory] notation "logρ[" W "](" x ")" => randomEnvironmentLogRatio W x

/-- A Solomon environment law is a random nearest-neighbor environment on `ℤ` whose log-ratio
field is i.i.d. and whose sampled environments are almost surely elliptic. This is the
source-facing environment-law owner for Theorem 19.35; the walk itself remains organized by the
canonical fixed-environment owner from Definition 19.34. -/
class IsSolomonEnvironmentLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → RandomEnvironment) : Prop where
  ae_elliptic : ∀ᵐ ω ∂μ, (W ω).IsElliptic
  logRatio_iid : IsIID (fun x ↦ logρ[W](x)) μ

namespace IsSolomonEnvironmentLaw

variable {W : Ω → RandomEnvironment}

/-- In a Solomon environment law, the sampled environment is elliptic almost surely. -/
theorem ae_elliptic_at (hW : IsSolomonEnvironmentLaw μ W) (x : ℤ) :
    ∀ᵐ ω ∂μ, 0 < (W ω).rightJumpProb x ∧ (W ω).rightJumpProb x < 1 :=
  hW.ae_elliptic.mono fun _ hω ↦ hω.pos_lt_one x

/-- In a Solomon environment law, all sitewise log-ratios have the same distribution. -/
theorem identDistrib_logRatio (hW : IsSolomonEnvironmentLaw μ W) (x y : ℤ) :
    IdentDistrib (logρ[W](x)) (logρ[W](y)) μ μ :=
  hW.logRatio_iid.identDistrib x y

end IsSolomonEnvironmentLaw

section SeriesBridge

variable {W : Ω → RandomEnvironment}

-- Proof sketch: apply the strong law of large numbers to the i.i.d. field `x ↦ logρ[W](x)` from
-- `IsSolomonEnvironmentLaw`; negative mean implies exponentially decaying rightward products and
-- divergent reciprocal leftward products, so Solomon's series satisfy `R_w^- = ∞` and
-- `R_w^+ < ∞` almost surely.
/-- If the common law of `log ρ₀` has negative mean, then almost every sampled environment lies in
the Solomon regime `R_w^- = ∞`, `R_w^+ < ∞` used in Theorem 19.33. -/
theorem ae_leftSeries_eq_top_and_rightSeries_lt_top_of_integral_logRatio_lt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ < 0) :
    ∀ᵐ ω ∂μ,
      R⁻[W ω] = ∞ ∧ R⁺[W ω] < ∞ := sorry

-- Proof sketch: the same strong-law argument, now with positive mean, makes the rightward
-- products grow and the leftward reciprocal products decay, yielding `R_w^- < ∞` and
-- `R_w^+ = ∞` almost surely.
/-- If the common law of `log ρ₀` has positive mean, then almost every sampled environment lies in
the Solomon regime `R_w^- < ∞`, `R_w^+ = ∞` used in Theorem 19.33. -/
theorem ae_leftSeries_lt_top_and_rightSeries_eq_top_of_integral_logRatio_gt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : 0 < ∫ ω, logρ[W](0) ω ∂μ) :
    ∀ᵐ ω ∂μ,
      R⁻[W ω] < ∞ ∧ R⁺[W ω] = ∞ := sorry

-- Proof sketch: zero mean forces the partial sums of `log ρ_x` to oscillate on both sides
-- infinitely often, so neither Solomon series converges.
/-- If the common law of `log ρ₀` has mean `0`, then almost every sampled environment lies in the
recurrent Solomon regime `R_w^- = ∞`, `R_w^+ = ∞` used in Theorem 19.33. -/
theorem ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ,
      R⁻[W ω] = ∞ ∧ R⁺[W ω] = ∞ := sorry

end SeriesBridge

section Quenched

variable {Ξ : Type v} [MeasurableSpace Ξ]
variable {W : Ω → RandomEnvironment}
variable {P : Ω → ℤ → ProbabilityMeasure Ξ} {X : Ω → ℕ → Ξ → ℤ}

-- Proof sketch: combine the almost-sure series regime from
-- `ae_leftSeries_eq_top_and_rightSeries_lt_top_of_integral_logRatio_lt_zero` with Theorem 19.33
-- for each fixed environment sample `ω`; since `R_w^- = ∞`, the positive-direction Solomon ratio
-- is `1`, so the quenched probability of `X_n → +∞` equals `1`.
/-- Theorem 19.35 (1): if `E[log ρ₀] < 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
tends to `+∞` with quenched probability `1`. -/
theorem ae_quenched_prob_tendsToPosInfinity_of_integral_logRatio_lt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ < 0)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atTop} = 1 := sorry

-- Proof sketch: use the almost-sure series regime from
-- `ae_leftSeries_lt_top_and_rightSeries_eq_top_of_integral_logRatio_gt_zero` and apply Theorem
-- 19.33 pointwise in the sampled environment `W ω`; the negative-direction ratio is then `1`.
/-- Theorem 19.35 (2): if `E[log ρ₀] > 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
tends to `-∞` with quenched probability `1`. -/
theorem ae_quenched_prob_tendsToNegInfinity_of_integral_logRatio_gt_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : 0 < ∫ ω, logρ[W](0) ω ∂μ)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      (P ω 0 : Measure Ξ) {ξ | Tendsto (fun n ↦ X ω n ξ) atTop atBot} = 1 := sorry

-- Proof sketch: combine the recurrent series regime from
-- `ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero` with Theorem 19.33
-- pointwise in `W ω`.
/-- Theorem 19.35 (3): if `E[log ρ₀] = 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
satisfies `liminf Xₙ = -∞` almost surely under the quenched law. -/
theorem ae_quenched_liminf_eq_bot_of_integral_logRatio_eq_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ = 0)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      ∀ᵐ ξ ∂(P ω 0 : Measure Ξ),
        liminf (fun n ↦ (((X ω n ξ : ℤ) : ℝ) : EReal)) atTop = ⊥ := sorry

-- Proof sketch: the same recurrent regime from
-- `ae_leftSeries_eq_top_and_rightSeries_eq_top_of_integral_logRatio_eq_zero`, together with the
-- second oscillation conclusion in Theorem 19.33, gives `limsup Xₙ = +∞` quenched almost surely.
/-- Theorem 19.35 (4): if `E[log ρ₀] = 0` and `E[|log ρ₀|] < ∞`, then for almost every
environment sample `ω`, every realization of the random walk in the fixed environment `W ω`
satisfies `limsup Xₙ = +∞` almost surely under the quenched law. -/
theorem ae_quenched_limsup_eq_top_of_integral_logRatio_eq_zero
    (hW : IsSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ[W](0)) μ)
    (hmean : ∫ ω, logρ[W](0) ω ∂μ = 0)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω)) :
    ∀ᵐ ω ∂μ,
      ∀ᵐ ξ ∂(P ω 0 : Measure Ξ),
        limsup (fun n ↦ (((X ω n ξ : ℤ) : ℝ) : EReal)) atTop = ⊤ := sorry

end Quenched

end ProbabilityTheory
