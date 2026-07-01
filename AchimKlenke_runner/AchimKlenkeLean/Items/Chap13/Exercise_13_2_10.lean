import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Xn Y : ℕ → Ω → ℝ} {X : Ω → ℝ}
variable
    (hY_law : ∀ n, HasLaw (Y n) (gaussianReal 0 ⟨((n + 1 : ℝ)⁻¹), by positivity⟩) P)

-- Proof sketch: for every `ε > 0`, the event `{ω | ε ≤ |Yₙ ω|}` depends only on the law of `Yₙ`;
-- rewrite its probability using `hY_law n`, identify it with the corresponding Gaussian tail
-- probability for variance `(n + 1)⁻¹`, and show that this tail tends to `0` as the variance
-- shrinks to `0`.
/-- A Gaussian perturbation whose variances are `(n + 1)⁻¹` converges to `0` in probability. -/
theorem gaussian_noise_tendstoInMeasure_zero :
    TendstoInMeasure P Y atTop 0 := sorry

-- Proof sketch: first use `gaussian_noise_tendstoInMeasure_zero` to obtain `Yₙ → 0` in
-- probability. For the forward implication, apply the canonical owner theorem
-- `TendstoInDistribution.add_of_tendstoInMeasure_const` to `Xₙ` and `Yₙ`. For the reverse
-- implication, apply the same theorem to `Xₙ + Yₙ` and `-Yₙ`.
/-- Exercise 13.2.10: with Lean's `0`-based indexing, the textbook Gaussian laws
`\mathcal{N}_{0,1/n}` are represented as `gaussianReal 0 ((n + 1)⁻¹)`. Under this shrinking
Gaussian perturbation, `Xₙ` converges in distribution to `X` if and only if `Xₙ + Yₙ` converges
in distribution to `X`. -/
theorem tendstoInDistribution_iff_add_gaussian_noise :
    TendstoInDistribution Xn atTop X (fun _ ↦ P) P ↔
      TendstoInDistribution (Xn + Y) atTop X (fun _ ↦ P) P := sorry

end
