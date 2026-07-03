import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

/- Definition II.2-extra-1: the textbook notion that `f` is holomorphic at `z₀` is the canonical
mathlib predicate `DifferentiableAt ℂ f z₀`. -/
#check (DifferentiableAt ℂ : (ℂ → ℂ) → ℂ → Prop)

/-- The textbook difference-quotient criterion for holomorphicity at a point. -/
theorem differentiableAt_complex_iff_exists_tendsto_difference_quotient
    {f : ℂ → ℂ} {z₀ : ℂ} :
    DifferentiableAt ℂ f z₀ ↔
      ∃ f' : ℂ,
        Tendsto (fun u ↦ (f (z₀ + u) - f z₀) / u) (𝓝[≠] (0 : ℂ)) (𝓝 f') := by
  constructor
  · intro hf
    refine ⟨deriv f z₀, ?_⟩
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hf.hasDerivAt.tendsto_slope_zero
  · rintro ⟨f', hf'⟩
    exact ((hasDerivAt_iff_tendsto_slope_zero).2 <| by
      simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        hf').differentiableAt
