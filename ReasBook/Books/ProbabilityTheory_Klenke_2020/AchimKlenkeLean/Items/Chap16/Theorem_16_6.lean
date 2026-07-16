import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Definition_15_27
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_1

open Filter MeasureTheory
open scoped Topology

-- Proof sketch: apply the continuity of characteristic functions to the witnessing probability
-- measure and specialize the resulting continuity at the origin.
/-- A characteristic function on `ℝ` is continuous at the origin. -/
theorem continuousAt_zero_of_exists_probabilityMeasure_charFun_eq {φ : ℝ → ℂ}
    (hφ : IsCFP φ) :
    ContinuousAt φ 0 := sorry

-- Proof sketch: specialize the one-dimensional Bochner characterization from Theorem 15.29 to
-- `ℝ`.
/-- Bochner's criterion on `ℝ`: a complex-valued function is a characteristic function exactly when
it is continuous, positive semidefinite, and normalized by `φ 0 = 1`. -/
theorem exists_probabilityMeasure_charFun_eq_iff_continuous_posSemidefiniteFunction_eq_one
    {φ : ℝ → ℂ} :
    IsCFP φ ↔
      Continuous φ ∧ IsPositiveSemidefiniteFunction φ ∧ φ 0 = 1 := sorry

section

variable {φs : ℕ → ℝ → ℂ} {φ ψ : ℝ → ℂ}

-- Proof sketch: apply the logarithmic expansion argument from the textbook pointwise in `t` to
-- compare `φs n t ^ n` with `exp ((n : ℂ) * (φs n t - 1))`, and use continuity at `0` to control
-- the branch issues exactly as in the proof of Theorem 16.6.
/-- Theorem 16.6 (1): for a sequence of CFPs on `ℝ`, pointwise convergence of `φₙ(t)^n` to a
function continuous at `0` is equivalent to pointwise convergence of `n (φₙ(t) - 1)` to a function
continuous at `0`. -/
theorem cfp_power_limit_iff_linearized_limit
    (hφs : ∀ n : ℕ, IsCFP (φs n)) :
    (∃ φ : ℝ → ℂ,
      (∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t))) ∧ ContinuousAt φ 0) ↔
      ∃ ψ : ℝ → ℂ,
        (∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t))) ∧
          ContinuousAt ψ 0 := sorry

-- Proof sketch: for each fixed `t`, compare `n * log (φs n t)` with `n * (φs n t - 1)` via the
-- Taylor expansion of `log` at `1`, then exponentiate the limit relation.
/-- Theorem 16.6 (2): if `φₙ(t)^n → φ(t)` and `n (φₙ(t) - 1) → ψ(t)` pointwise, and `φ` is
continuous at `0`, then `φ = exp ∘ ψ`. -/
theorem cfp_power_limit_eq_cexp_linearized_limit
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0)
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t))) :
    φ = fun t : ℝ ↦ Complex.exp (ψ t) := sorry

-- Proof sketch: apply the one-dimensional Lévy continuity theorem directly to the CFP sequence
-- `φs n` and the pointwise power-limit hypothesis, using continuity of the limit at the origin to
-- conclude that the limit is again a CFP.
/-- Theorem 16.6 (3): if `φₙ(t)^n → φ(t)` pointwise and `φ` is continuous at `0`, then the limit
function `φ` is again a CFP. In particular, under the full hypotheses of Theorem 16.6, the
identified limit `φ = e^ψ` is a CFP. -/
theorem cfp_power_limit_exists_probabilityMeasure_charFun_eq
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0) :
    IsCFP φ := sorry

end
