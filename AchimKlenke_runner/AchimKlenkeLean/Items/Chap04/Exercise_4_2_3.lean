import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {E : Type u} [NormedAddCommGroup E]

-- Proof sketch: apply Tonelli/Fubini to the nonnegative function `(n, t) ↦ ‖f ((n + 1) * t)‖` on
-- `ℕ × [0, ∞)`, use the change of variables `x = (n + 1) t` to bound the iterated integral by a
-- convergent multiple of `∫_[0,∞) ‖f x‖ dx`, and conclude that the sampled series is absolutely
-- summable for almost every `t`.
theorem ae_summable_norm_at_nat_multiples_of_integrableOn_Ici (f : ℝ → E)
    (hf : IntegrableOn f (Ici 0)) :
    ∀ᵐ t ∂(volume.restrict (Ici 0)), Summable (fun n ↦ ‖f ((n + 1) * t)‖) := sorry

/-- Exercise 4.2.3: if `f` is Lebesgue integrable on `[0, ∞)`, then for Lebesgue-almost every
`t ∈ [0, ∞)` the sampled series `∑ n = 1 to ∞, f (n t)` converges absolutely. In Lean's `0`-based
indexing, this is the summability of `n ↦ |f ((n + 1) * t)|`. -/
theorem ae_summable_abs_at_nat_multiples_of_integrableOn_Ici (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ici 0)) :
    ∀ᵐ t ∂(volume.restrict (Ici 0)), Summable (fun n ↦ |f ((n + 1) * t)|) := by
  simpa [Real.norm_eq_abs] using ae_summable_norm_at_nat_multiples_of_integrableOn_Ici f hf
