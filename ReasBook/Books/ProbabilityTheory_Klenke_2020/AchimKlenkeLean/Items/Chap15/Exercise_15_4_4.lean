import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

/- Exercise 15.4.4 is `source-facing`: its public objects are the characteristic function of the
common law and the empirical averages themselves. The owner abstractions are the canonical law map
`charFun` and the chapter's i.i.d. shorthand `IsIID`; the file therefore keeps the textbook
conclusions directly visible while avoiding parallel local wrappers. -/

-- Proof sketch: a characteristic function comes from a probability law, so the derivative criterion
-- for `charFun` at `0` forces the derivative to be purely imaginary; extract the real coefficient.
/-- Exercise 15.4.4 (1): if the characteristic function of a real probability law is
differentiable at `0`, then its derivative at `0` is `i m` for some real `m`. -/
theorem hasDerivAt_charFun_zero_eq_real_mul_I
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {dphi : ℂ}
    (hphi : HasDerivAt (charFun μ) dphi 0) :
    ∃ m : ℝ, dphi = (m : ℂ) * Complex.I := sorry

section IIDAverage

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: for the common law `P.map (X 0)`, differentiate the `n`th power relation for the
-- characteristic function of normalized partial sums and combine it with the weak law of large
-- numbers for i.i.d. averages.
/-- Exercise 15.4.4 (2): for a `0`-based Lean i.i.d. sequence `X 0, X 1, ...` representing the
textbook sequence `X₁, X₂, ...`, the common characteristic function has derivative `i m` at `0`
exactly when the empirical averages converge in probability to `m`. -/
theorem hasDerivAt_charFun_map_zero_iff_tendstoInMeasure_average
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX_iid : IsIID X P) (m : ℝ) :
    HasDerivAt (charFun (P.map (X 0))) ((m : ℂ) * Complex.I) 0 ↔
      TendstoInMeasure P
        (fun n ω ↦ (∑ i ∈ Finset.range n, X i ω) / n)
        atTop
        (fun _ ↦ m) := sorry

end IIDAverage

-- Proof sketch: use the derivative-at-zero criterion for characteristic functions together with
-- the nonnegativity assumption, then identify the limiting truncated first moment with the full
-- expectation and conclude integrability of `id`.
/-- Exercise 15.4.4 (3): if a real probability law is supported on `[0, ∞)` and its
characteristic function is differentiable at `0`, then the first moment is finite and the
derivative at `0` equals the expectation multiplied by `i`. Equivalently,
`μ[id] = -Complex.I * φ'(0) < ∞`. -/
theorem integrable_id_of_nonnegative_hasDerivAt_charFun_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {dphi : ℂ}
    (hphi : HasDerivAt (charFun μ) dphi 0)
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) :
    Integrable id μ ∧ dphi = (μ[id] : ℂ) * Complex.I := sorry

-- Proof sketch: choose a heavy-tailed real probability law whose positive and negative tails
-- cancel in the first derivative of the characteristic function, while the absolute first moment
-- remains infinite.
/-- Exercise 15.4.4 (4): there exists a real probability distribution whose characteristic
function is differentiable at `0` although the absolute first moment is infinite. -/
theorem exists_probabilityMeasure_differentiableAt_charFun_zero_not_integrable_id :
    ∃ μ : ProbabilityMeasure ℝ,
      DifferentiableAt ℝ (charFun (μ : Measure ℝ)) 0 ∧
        ¬ Integrable id (μ : Measure ℝ) := sorry
