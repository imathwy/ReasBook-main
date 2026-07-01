import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

-- Proof sketch: apply Fatou's lemma to the nonnegative functions `f - min (f_n) f` and
-- `f_n - min (f_n) f` to identify the limit of the integrals of `min (f_n) f`, deduce that `f`
-- is integrable from the assumed convergence of `∫ f_n`, and then rewrite `‖f_n - f‖` using the
-- decomposition through `min (f_n) f`.
/-- Exercise 4.2.2: if nonnegative integrable functions `f_n` converge almost everywhere to a
function `f` and the integrals `∫ f_n dμ` converge to `I`, then `f` is integrable and the
`L¹`-distance to `f` has limit `I - ∫ f dμ`. -/
theorem scheffe_of_nonnegative_ae_tendsto
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {I : ℝ}
    (hfSeq_int : ∀ n, Integrable (fSeq n) μ)
    (hfSeq_nonneg : ∀ n, 0 ≤ᵐ[μ] fSeq n)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x)))
    (h_integral_tendsto : Tendsto (fun n ↦ ∫ x, fSeq n x ∂μ) atTop (𝓝 I)) :
    Integrable f μ ∧
      Tendsto (fun n ↦ ∫ x, ‖fSeq n x - f x‖ ∂μ) atTop
        (𝓝 (I - ∫ x, f x ∂μ)) := sorry
