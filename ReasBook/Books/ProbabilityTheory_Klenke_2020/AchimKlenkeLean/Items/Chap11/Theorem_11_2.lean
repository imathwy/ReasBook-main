import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Theorem_9_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Finset

universe u

variable {Ω : Type u}

section DoobLp

variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ℕ m0} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {X : ℕ → Ω → ℝ}

local macro:max "absMaxUpTo(" X:term ", " n:term ", " ω:term ")" : term =>
  `((range ($n + 1)).sup' nonempty_range_add_one fun k ↦ |($X k $ω)|)

local macro:max "terminalAbsRpow(" X:term ", " p:term ", " n:term ", " ω:term ")" : term =>
  `(Real.rpow |($X $n $ω)| $p)

local macro:max "absMaxUpToRpow(" X:term ", " p:term ", " n:term ", " ω:term ")" : term =>
  `(Real.rpow (absMaxUpTo($X, $n, $ω)) $p)

/- Theorem 11.2 is `source-facing`: it packages the textbook `L^p` corollaries of Doob's discrete
maximal inequality. Its `core/canonical` owner abstraction is `MeasureTheory.maximal_ineq`, and
its `bridge/view` layer for the transformed process `n ↦ |X n| ^ p` is the earlier project theorem
`submartingale_abs_rpow`; this file keeps only the source-level inequalities rather than a parallel
wrapper API for either ingredient. -/
recall MeasureTheory.maximal_ineq
recall submartingale_abs_rpow

/-- Theorem 11.2 (1): for a martingale or a nonnegative submartingale, Doob's `L^p` tail estimate
controls the event `{|X|*_n ≥ λ}` by the terminal `p`-th moment. -/
-- Proof sketch: if `X` is a martingale, apply the convex-function result from Theorem 9.35 to the
-- process `|X|^p`; if `X` is already a nonnegative submartingale, apply the same argument directly.
-- Then use Lemma 11.1, i.e. Doob's maximal inequality for nonnegative submartingales, with the
-- submartingale `k ↦ |X_k|^p`.
theorem doobLp_tail_bound
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p threshold : ℝ}
    (hp : 1 ≤ p) (hthreshold : 0 < threshold)
    (n : ℕ) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | threshold ≤ absMaxUpTo(X, n, ω)} ≤
      ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := sorry

/-- Theorem 11.2 (2): for every nonnegative exponent `p`, the terminal `p`-th moment is bounded by
the `p`-th moment of the running maximal process. This is the left inequality in clause (ii),
isolated in the minimal exponent range actually used by its pointwise proof. -/
-- Proof sketch: for every `ω`, the terminal absolute value `|X n ω|` is one of the terms entering
-- the maximum `|X|*_n ω`, so pointwise monotonicity of `x ↦ x^p` on `ℝ≥0` for `p ≥ 0` and
-- monotonicity of the lower integral give the estimate.
theorem doobLp_terminalMoment_le_runningMaxMoment
    {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) ∂μ := sorry

/-- Theorem 11.2 (3): for `p > 1`, the `p`-th moment of the running maximal process is bounded by
the classical Doob constant `(p / (p - 1))^p` times the terminal `p`-th moment. This is the right
inequality in clause (ii). -/
-- Proof sketch: integrate the tail estimate from clause (1) against `p λ^(p-1)`, truncate the
-- running maximum at level `K`, apply Hölder's inequality to the truncated moments, and then pass
-- to the limit `K → ∞`.
theorem doobLp_runningMaxMoment_le
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := sorry

end DoobLp
