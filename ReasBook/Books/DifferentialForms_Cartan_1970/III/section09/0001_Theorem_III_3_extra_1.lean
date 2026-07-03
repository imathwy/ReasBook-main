import Mathlib.Analysis.Complex.Schwarz

open Metric Set

-- Declarations for this item will be appended below by the statement pipeline.

/-
These are source-facing `bridge/view` corollaries of mathlib's Schwarz lemma API on `ball c R`.
The owner declarations are `Complex.norm_le_norm_of_mapsTo_ball` and
`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`.
-/
/-- Theorem III.3-extra-1 (1): a holomorphic self-map of the unit disc that fixes the origin
satisfies `‖f z‖ ≤ ‖z‖` for every `z` in the unit disc. -/
-- Proof sketch: strengthen the codomain hypothesis from `Metric.ball 0 1`
-- to `Metric.closedBall 0 1`,
-- then apply `Complex.norm_le_norm_of_mapsTo_ball` with radius `1`.
theorem schwarz_lemma_norm_le (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h_maps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (h₀ : f 0 = 0) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖f z‖ ≤ ‖z‖ := by
  exact Complex.norm_le_norm_of_mapsTo_ball hf
    (fun w hw ↦ ball_subset_closedBall (h_maps hw)) h₀ (mem_ball_zero_iff.mp hz)

/-- Theorem III.3-extra-1 (2): if equality `‖f z₀‖ = ‖z₀‖` holds at some nonzero point `z₀`
of the unit disc, then `f` is multiplication by a complex number of norm `1` on the whole unit
disc. -/
-- Proof sketch: rewrite the equality hypothesis as `‖Complex.dslope f 0 z₀‖ = 1`,
-- apply `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div` with `c = 0` and `R₁ = R₂ = 1`,
-- and simplify the resulting affine expression to `fun z ↦ λ * z`.
theorem schwarz_lemma_rigidity (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h_maps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (h₀ : f 0 = 0) {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hz₀_ne : z₀ ≠ 0)
    (h_eq : ‖f z₀‖ = ‖z₀‖) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ EqOn f (fun z ↦ a * z) (ball (0 : ℂ) 1) := by
  have h_maps' : MapsTo f (ball (0 : ℂ) 1) (closedBall (f 0) 1) := by
    intro z hz
    simpa [h₀] using ball_subset_closedBall (h_maps hz)
  have h_dslope : ‖dslope f 0 z₀‖ = 1 := by
    have hz₀_norm_ne : ‖z₀‖ ≠ 0 := norm_ne_zero_iff.mpr hz₀_ne
    have hnorm : ‖z₀‖ * ‖dslope f 0 z₀‖ = ‖z₀‖ := by
      simpa [sub_zero, h_eq] using congrArg norm (sub_smul_dslope_of_zero h₀ z₀)
    have hnorm' : ‖z₀‖ * ‖dslope f 0 z₀‖ = ‖z₀‖ * 1 := by
      simpa using hnorm
    exact mul_left_cancel₀ hz₀_norm_ne hnorm'
  refine ⟨dslope f 0 z₀, h_dslope, ?_⟩
  simpa [h₀, sub_zero, smul_eq_mul, mul_comm] using
    Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hf h_maps' hz₀ (by simpa using h_dslope)
