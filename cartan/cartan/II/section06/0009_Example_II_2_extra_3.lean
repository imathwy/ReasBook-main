import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Metric

variable {f : ℂ → ℂ} {c a : ℂ} {R : ℝ}

-- Proof sketch: apply `hf.circleIntegral_sub_inv_smul ha` on the positively oriented circle
-- bounding the disc, then rewrite scalar multiplication on `ℂ` as ordinary multiplication.
/-- Example II.2-extra-3 (1): if `f` is holomorphic on a neighborhood of the closed disc centered
at `c` with radius `R`, then for every `a` in the open disc the positively oriented boundary
integral of `f z / (z - a)` is `2π i f(a)`. -/
theorem circleIntegral_div_sub_eq_two_pi_I_mul_of_mem_ball
    (hf : DiffContOnCl ℂ f (ball c R)) (ha : a ∈ ball c R) :
    (∮ z in C(c, R), f z / (z - a)) = (2 * Real.pi * Complex.I : ℂ) * f a := by
  simpa [smul_eq_mul, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm] using
    hf.circleIntegral_sub_inv_smul ha

-- Proof sketch: when `a ∉ closedBall c R`, the quotient `z ↦ f z / (z - a)` is holomorphic
-- on a neighborhood of the closed disc, so `DiffContOnCl.circleIntegral_eq_zero` applies.
/-- Example II.2-extra-3 (2): if `f` is holomorphic on a neighborhood of the closed disc centered
at `c` with radius `R`, then for every `a` outside the closed disc the positively oriented
boundary integral of `f z / (z - a)` is zero. -/
theorem circleIntegral_div_sub_eq_zero_of_not_mem_closedBall
    (hR : 0 ≤ R) (hf : DiffContOnCl ℂ f (ball c R)) (ha : a ∉ closedBall c R) :
    (∮ z in C(c, R), f z / (z - a)) = 0 := by
  have h_inv : DiffContOnCl ℂ (fun z ↦ (z - a)⁻¹) (ball c R) :=
    ((differentiable_id.sub_const a).diffContOnCl).inv fun z hz hza ↦ ha <| by
      exact (sub_eq_zero.mp hza) ▸ closure_ball_subset_closedBall hz
  have h_div : DiffContOnCl ℂ (fun z ↦ f z / (z - a)) (ball c R) := by
    simpa [smul_eq_mul, div_eq_inv_mul] using h_inv.smul hf
  simpa using h_div.circleIntegral_eq_zero hR
