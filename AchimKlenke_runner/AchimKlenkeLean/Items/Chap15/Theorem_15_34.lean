import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: apply the converse implication from the characteristic-function/moment theory to
-- the probability law `μ`. The assumed `2n`-times differentiability at `0` yields integrability
-- of `x ↦ x^(2n)` under `μ`, and then the `2n`th iterated derivative identifies with the even
-- moment up to the factor `(-1)^n`.
/-- Theorem 15.34: if the characteristic function of a probability law on `ℝ` has a `2n`th
iterated derivative at `0` in the canonical sense that each intermediate iterated derivative has
the next one as its derivative at `0`, then the even moment equals `(-1)^n` times that derivative
and is finite. -/
theorem even_moment_eq_neg_one_pow_mul_charFun_iterated_deriv_at_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ)
    (hphi :
      ∀ m < 2 * n,
        HasDerivAt (iteratedDeriv m (charFun μ)) (iteratedDeriv (m + 1) (charFun μ) 0) 0) :
    (moment id (2 * n) μ : ℂ) = (-1 : ℂ) ^ n * iteratedDeriv (2 * n) (charFun μ) 0 ∧
      Integrable (fun x : ℝ ↦ x ^ (2 * n)) μ := sorry

/-- Realization-level bridge for Theorem 15.34 via a specified law. -/
theorem even_moment_eq_neg_one_pow_mul_charFun_iterated_deriv_at_zero_of_hasLaw
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {μ : Measure ℝ}
    (hX : HasLaw X μ P) (n : ℕ)
    (hphi :
      ∀ m < 2 * n,
        HasDerivAt (iteratedDeriv m (charFun μ)) (iteratedDeriv (m + 1) (charFun μ) 0) 0) :
    (moment X (2 * n) P : ℂ) = (-1 : ℂ) ^ n * iteratedDeriv (2 * n) (charFun μ) 0 ∧
      Integrable (fun ω ↦ X ω ^ (2 * n)) P := sorry
