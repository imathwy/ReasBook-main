

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_9_39 (from Items/Chap09) -/
open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {ℱ : Filtration ℕ mΩ} {μ : Measure Ω}

-- Proof sketch: for the forward implication, use the one-step martingale identity together with
-- predictability and local boundedness to show that every stochastic integral is again a
-- martingale. For the converse, test the hypothesis on the indicator integrand
-- `H_n = 1_{\\{n = n₀\\}}`, whose integral isolates the increment `X n₀ - X (n₀ - 1)`.
/-- Theorem 9.39 (1): an adapted real-valued process with integrable initial value is a martingale
iff every stochastic integral against a locally bounded predictable integrand is a martingale. -/
theorem martingale_iff_stochasticIntegral_martingale [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_adapted : Adapted ℱ X) (hX0_int : Integrable (X 0) μ) :
    Martingale X ℱ μ ↔
      ∀ H : ℕ → Ω → ℝ,
        IsPredictable ℱ H →
          IsLocallyBoundedProcess H →
            Martingale (stochasticIntegral H X) ℱ μ := sorry

-- Proof sketch: the forward implication uses the standard stability of submartingales under
-- stochastic integration by nonnegative locally bounded predictable integrands. For the converse,
-- test on the same single-step indicator integrands as in part (1), which are nonnegative and
-- recover the one-step submartingale inequality for `X`.
/-- Theorem 9.39 (2): an adapted real-valued process with integrable initial value is a
submartingale iff every stochastic integral against a nonnegative locally bounded predictable
integrand is a submartingale. -/
theorem submartingale_iff_stochasticIntegral_submartingale [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_adapted : Adapted ℱ X) (hX0_int : Integrable (X 0) μ) :
    Submartingale X ℱ μ ↔
      ∀ H : ℕ → Ω → ℝ,
        IsPredictable ℱ H →
          IsLocallyBoundedProcess H →
            (∀ n ω, 0 ≤ H n ω) →
              Submartingale (stochasticIntegral H X) ℱ μ := sorry

-- Proof sketch: apply the submartingale statement to `-X` and use the equivalence between
-- supermartingales and submartingales of the negated process, together with
-- `stochasticIntegral H (-X) = -stochasticIntegral H X`.
/-- Theorem 9.39 (3): an adapted real-valued process with integrable initial value is a
supermartingale iff every stochastic integral against a nonnegative locally bounded predictable
integrand is a supermartingale. -/
theorem supermartingale_iff_stochasticIntegral_supermartingale [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_adapted : Adapted ℱ X) (hX0_int : Integrable (X 0) μ) :
    Supermartingale X ℱ μ ↔
      ∀ H : ℕ → Ω → ℝ,
        IsPredictable ℱ H →
          IsLocallyBoundedProcess H →
            (∀ n ω, 0 ≤ H n ω) →
              Supermartingale (stochasticIntegral H X) ℱ μ := sorry

end ProbabilityTheory
