/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

section Chap04
section Section01

open Filter Topology

/-- Definition 4.1.1: For an interval `I ⊆ ℝ`, a function `f : ℝ → ℝ`, and
`c ∈ I`, if the limit `L = lim_{x → c} (f x - f c) / (x - c)` exists, then `f`
is differentiable at `c`, `L` is the derivative `f' c`, and the quotient
`(f x - f c) / (x - c)` is the difference quotient. If the limit exists at
every `c ∈ I`, then `f` is differentiable on `I` and yields a derivative
function `f' : I → ℝ`. -/
noncomputable def differenceQuotient (f : ℝ → ℝ) (c x : ℝ) : ℝ :=
  (f x - f c) / (x - c)

/-- The book's notion of differentiability on a subset of `ℝ` via the limit of
the difference quotient. -/
def DifferentiableAtOn (I : Set ℝ) (f : ℝ → ℝ) (c : ℝ) : Prop :=
  c ∈ I ∧
    ∃ L : ℝ,
      Tendsto (fun x => differenceQuotient f c x)
        (nhdsWithin c {x | x ≠ c}) (𝓝 L)

/-- The derivative value provided by the existence of the difference-quotient
limit. -/
noncomputable def derivativeAtOn (I : Set ℝ) (f : ℝ → ℝ) (c : ℝ)
    (h : DifferentiableAtOn I f c) : ℝ :=
  Classical.choose h.2

/-- The book's differentiability notion agrees with mathlib's `HasDerivAt`
formulation. -/
lemma differentiableAtOn_iff_hasDerivAt {I : Set ℝ} {f : ℝ → ℝ} {c : ℝ} :
    DifferentiableAtOn I f c ↔ c ∈ I ∧ ∃ L : ℝ, HasDerivAt f L c := by
  constructor
  · rintro ⟨hcI, L, hL⟩
    refine ⟨hcI, L, ?_⟩
    apply (hasDerivAt_iff_tendsto_slope).2
    simpa [differenceQuotient, slope_fun_def_field] using hL
  · rintro ⟨hcI, L, hL⟩
    refine ⟨hcI, L, ?_⟩
    have hL' : Tendsto (slope f c) (𝓝[≠] c) (𝓝 L) :=
      (hasDerivAt_iff_tendsto_slope).1 hL
    simpa [differenceQuotient, slope_fun_def_field] using hL'

/-- If a function is differentiable at every point of an interval, the
derivative defines a function `I → ℝ`. -/
noncomputable def derivativeOn (I : Set ℝ) (f : ℝ → ℝ)
    (h : ∀ c ∈ I, DifferentiableAtOn I f c) : I → ℝ :=
  fun x => derivativeAtOn I f x.1 (h x.1 x.property)

/-- Example 4.1.2: For `f x = x^2` on `ℝ`, the derivative at any `c` satisfies
`f' c = 2c`, since the difference quotient simplifies to `x + c` and its limit
as `x → c` is `2c`. -/
lemma hasDerivAt_sq (c : ℝ) : HasDerivAt (fun x => x ^ 2) (2 * c) c := by
  -- Derivative of `x ↦ x` is `1`, so apply the product rule to `fun x ↦ x * x`.
  have h_id : HasDerivAt (fun x : ℝ => x) 1 c := by
    simpa using (hasDerivAt_id c)
  simpa [pow_two, two_mul] using h_id.mul h_id

/-- Example 4.1.3: For an affine function `f x = a * x + b` with real coefficients,
the difference quotient simplifies to `a`, so the derivative at any point `c` is
the constant slope `a`. -/
lemma hasDerivAt_affine (a b c : ℝ) :
    HasDerivAt (fun x => a * x + b) a c := by
  -- Derivative of the linear part is the constant slope `a`.
  have h_linear : HasDerivAt (fun x => a * x) a c := by
    simpa [mul_one] using (hasDerivAt_id c).const_mul a
  -- Adding a constant does not affect the derivative.
  simpa using h_linear.add_const b

/-- Example 4.1.4: The square-root function `f x = √x` is differentiable for
`x > 0`, and for each `c > 0` its derivative is `1 / (2√c)`. -/
lemma hasDerivAt_sqrt_pos {c : ℝ} (hc : 0 < c) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt c)) c := by
  have hc' : c ≠ 0 := ne_of_gt hc
  simpa using Real.hasDerivAt_sqrt hc'

/-- Example 4.1.5: The absolute-value function is not differentiable at the
origin, since the difference quotient is `1` for `x > 0` and `-1` for `x < 0`.
-/
lemma differenceQuotient_abs_pos {x : ℝ} (hx : 0 < x) :
    differenceQuotient (fun x : ℝ => |x|) 0 x = 1 := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  simp [differenceQuotient, abs_zero, abs_of_pos hx, hx_ne]

lemma differenceQuotient_abs_neg {x : ℝ} (hx : x < 0) :
    differenceQuotient (fun x : ℝ => |x|) 0 x = -1 := by
  have hx_ne : x ≠ 0 := ne_of_lt hx
  have hx_div : (-x) / x = -1 := by
    have hx_self : x / x = (1 : ℝ) := by simpa using div_self hx_ne
    simp [neg_div, hx_self]
  simp [differenceQuotient, abs_zero, abs_of_neg hx, hx_div]

lemma abs_not_differentiable_at_zero :
    ¬ DifferentiableAt ℝ (fun x : ℝ => |x|) 0 := by
  simp [not_differentiableAt_abs_zero]

/-- Proposition 4.1.6: If a real function is differentiable at a point of an
interval, then it is continuous at that point. -/
theorem differentiableAt_real_continuousAt {f : ℝ → ℝ} {c : ℝ}
 (h : DifferentiableAt ℝ f c) : ContinuousAt f c := by
  simpa using h.continuousAt

/-- Proposition 4.1.7 (Linearity): Let `I` be an interval and let `f g : ℝ → ℝ`
be differentiable at `c ∈ I`, with `α : ℝ`. (i) For `h x = α * f x`, the
derivative satisfies `deriv h c = α * deriv f c`. (ii) For `h x = f x + g x`,
the derivative satisfies `deriv h c = deriv f c + deriv g c`. -/
theorem deriv_const_mul_at {f : ℝ → ℝ} {c α : ℝ}
    (hf : DifferentiableAt ℝ f c) :
    DifferentiableAt ℝ (fun x => α * f x) c ∧
      deriv (fun x => α * f x) c = α * deriv f c := by
  classical
  have h :=
    (hf.hasDerivAt.const_mul α :
      HasDerivAt (fun x => α * f x) (α * deriv f c) c)
  exact ⟨h.differentiableAt, h.deriv⟩

theorem deriv_add_at {f g : ℝ → ℝ} {c : ℝ}
    (hf : DifferentiableAt ℝ f c) (hg : DifferentiableAt ℝ g c) :
    DifferentiableAt ℝ (fun x => f x + g x) c ∧
      deriv (fun x => f x + g x) c = deriv f c + deriv g c := by
  classical
  have h :=
    (hf.hasDerivAt.add hg.hasDerivAt :
      HasDerivAt (fun x => f x + g x) (deriv f c + deriv g c) c)
  exact ⟨h.differentiableAt, h.deriv⟩

/-- Proposition 4.1.8 (Product rule): For an interval `I` and functions
`f g : ℝ → ℝ` differentiable at `c ∈ I`, the product `h x = f x * g x` is
differentiable at `c`, and its derivative satisfies
`deriv h c = f c * deriv g c + deriv f c * g c`. -/
theorem deriv_mul_at {I : Set ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (_hc : c ∈ I) (hf : DifferentiableAt ℝ f c) (hg : DifferentiableAt ℝ g c) :
    DifferentiableAt ℝ (fun x => f x * g x) c ∧
      deriv (fun x => f x * g x) c =
        f c * deriv g c + deriv f c * g c := by
  classical
  have h :=
    (hf.hasDerivAt.mul hg.hasDerivAt :
      HasDerivAt (fun x => f x * g x) (deriv f c * g c + f c * deriv g c) c)
  refine ⟨h.differentiableAt, ?_⟩
  simpa [add_comm] using h.deriv

/-- Proposition 4.1.9 (Quotient rule): For an interval `I` and functions
`f g : ℝ → ℝ` differentiable at `c ∈ I`, with `g x ≠ 0` for all `x ∈ I`, the
quotient `h x = f x / g x` is differentiable at `c`, and its derivative
satisfies `deriv h c = (deriv f c * g c - f c * deriv g c) / (g c)^2`. -/
theorem deriv_div_at {I : Set ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hc : c ∈ I) (hf : DifferentiableAt ℝ f c) (hg : DifferentiableAt ℝ g c)
    (hgnz : ∀ x ∈ I, g x ≠ 0) :
    DifferentiableAt ℝ (fun x => f x / g x) c ∧
      deriv (fun x => f x / g x) c =
        (deriv f c * g c - f c * deriv g c) / (g c) ^ 2 := by
  classical
  have hgnz' : g c ≠ 0 := hgnz c hc
  have h :
      HasDerivAt (fun x => f x / g x)
        ((deriv f c * g c - f c * deriv g c) / (g c) ^ 2) c := by
    simpa using (hf.hasDerivAt.div hg.hasDerivAt hgnz')
  exact ⟨h.differentiableAt, h.deriv⟩

/-- Helper lemma for Proposition 4.1.10: differentiability of the composition
arises from the chain rule for `HasDerivAt`. -/
lemma hasDerivAt_comp_at {f g : ℝ → ℝ} {c : ℝ}
    (hgd : DifferentiableAt ℝ g c) (hfd : DifferentiableAt ℝ f (g c)) :
    HasDerivAt (fun x => f (g x)) (deriv f (g c) * deriv g c) c := by
  classical
  simpa using (hfd.hasDerivAt.comp c hgd.hasDerivAt)

/-- Proposition 4.1.10 (Chain rule): Let `I₁, I₂` be intervals, with
`g : ℝ → ℝ` differentiable at `c ∈ I₁` and taking values in `I₂`, and
`f : ℝ → ℝ` differentiable at `g c`. If `h x = f (g x)`, then `h` is
differentiable at `c` with derivative `deriv f (g c) * deriv g c`. -/
theorem deriv_comp_at {f g : ℝ → ℝ} {c : ℝ}
    (hgd : DifferentiableAt ℝ g c) (hfd : DifferentiableAt ℝ f (g c)) :
    DifferentiableAt ℝ (fun x => f (g x)) c ∧
      deriv (fun x => f (g x)) c = deriv f (g c) * deriv g c := by
  classical
  have h := hasDerivAt_comp_at hgd hfd
  exact ⟨h.differentiableAt, h.deriv⟩

end Section01
end Chap04
