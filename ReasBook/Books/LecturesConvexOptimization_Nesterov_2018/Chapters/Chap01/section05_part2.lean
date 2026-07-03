import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_1_5_10 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {L : NNReal} {f : E → ℝ}
variable (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))

include hf hgrad

/- Lemma 1.5.10 is source-facing in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the first-order Taylor remainder bound and its quadratic upper/lower companions
* core/canonical: the owner hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` from
  Definition 1.5.2 together with the affine Taylor-model owner `firstOrderTaylorModelAt f x`
* bridge/view: evaluation of the owner model via `firstOrderTaylorModelAt_apply`

Primitive data:
* a function `f`
* a Lipschitz constant `L`
* a base point `x`

Derived API:
* the absolute remainder estimate
* the quadratic upper and lower bounds obtained by comparing `f y` with the owner affine model

The statements are written on a real Hilbert space; specializing `E` to `EuclideanSpace ℝ (Fin n)`
recovers the textbook `ℝⁿ` formulation. -/

-- Proof sketch: restrict `f` to the segment `t ↦ x + t • (y - x)`, apply the fundamental theorem
-- of calculus to the derivative `⟪∇ f (x + t • (y - x)), y - x⟫`, subtract the affine term at
-- `x`, and bound the integrand using the `L`-Lipschitz estimate for `∇ f`.
omit hf hgrad

/-- Helper for Lemma 1.5.10: the corrected segment remainder has derivative equal to the gradient
increment paired with the segment direction. -/
private lemma segment_corrected_remainder_hasDerivAt
    (hf : ContDiff ℝ 1 f) (x d : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ f (x + u • d) - f x - u * inner ℝ (∇ f x) d)
      (inner ℝ (∇ f (x + t • d) - ∇ f x) d) t := by
  -- Differentiate the restriction of `f` to the affine line through `x` in direction `d`.
  have hdiff : DifferentiableAt ℝ f (x + t • d) :=
    hf.differentiable_one.differentiableAt
  have hseg : HasDerivAt (fun u : ℝ ↦ f (x + u • d)) ((fderiv ℝ f (x + t • d)) d) t := by
    have hline : HasDerivAt (fun u : ℝ ↦ x + u • d) d t := by
      simpa [one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)
    simpa [Function.comp] using (hdiff.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  -- The affine correction contributes exactly the constant gradient term at `x`.
  have hlin : HasDerivAt (fun u : ℝ ↦ u * inner ℝ (∇ f x) d) (inner ℝ (∇ f x) d) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (inner ℝ (∇ f x) d)
  have hmain :
      HasDerivAt (fun u : ℝ ↦ f (x + u • d) - f x - u * inner ℝ (∇ f x) d)
        (((fderiv ℝ f (x + t • d)) d) - inner ℝ (∇ f x) d) t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hseg.sub ((hasDerivAt_const t (f x)).add hlin)
  -- Rewrite the Fréchet derivative through the gradient pairing to obtain the source formula.
  convert hmain using 1
  rw [inner_sub_left]
  rw [inner_gradient_left (y := d) hdiff]

/-- Helper for Lemma 1.5.10: the corrected segment remainder vanishes at `0` and equals the
first-order Taylor remainder at `1`. -/
private lemma segment_corrected_remainder_endpoints
    (x y : E) :
    let d := y - x
    let R : ℝ → ℝ := fun t ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d
    R 0 = 0 ∧ R 1 = f y - firstOrderTaylorModelAt f x y := by
  -- Evaluating at the endpoints turns the corrected path into the target remainder.
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Lemma 1.5.10: on `(0,1)` the corrected segment remainder has derivative bounded by
`L t ‖d‖²`. -/
private lemma segment_corrected_remainder_deriv_abs_le
    (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))
    (x d : E) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun u : ℝ ↦ f (x + u • d) - f x - u * inner ℝ (∇ f x) d) t|
      ≤ (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
  -- Start from the explicit derivative formula for the corrected path.
  have hderivAt := segment_corrected_remainder_hasDerivAt (f := f) hf x d t
  rw [hderivAt.deriv]
  have hinner :
      |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤ ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ := by
    simpa [real_inner_comm] using abs_real_inner_le_norm (∇ f (x + t • d) - ∇ f x) d
  have hgrad_bound : ‖∇ f (x + t • d) - ∇ f x‖ ≤ (L : ℝ) * ‖(x + t • d) - x‖ := by
    simpa [dist_eq_norm] using hgrad.norm_sub_le (x + t • d) x
  have hseg_norm : ‖(x + t • d) - x‖ = t * ‖d‖ := by
    calc
      ‖(x + t • d) - x‖ = ‖t • d‖ := by simp
      _ = |t| * ‖d‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ = t * ‖d‖ := by rw [abs_of_pos ht.1]
  -- Combine Cauchy-Schwarz with the Lipschitz gradient estimate along the segment.
  calc
    |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤ ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ := hinner
    _ ≤ ((L : ℝ) * ‖(x + t • d) - x‖) * ‖d‖ := by gcongr
    _ = ((L : ℝ) * (t * ‖d‖)) * ‖d‖ := by rw [hseg_norm]
    _ = (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by ring

include hf hgrad

/-- Lemma 1.5.10: if `f` belongs to the textbook class `C^{1,1}_L(ℝⁿ)`, then the first-order
Taylor remainder at `x` along `y - x` is bounded in absolute value by `(L / 2) ‖y - x‖²`. -/
lemma norm_taylor_remainder_le_half_lipschitzGradient_mul_sq
    (x y : E) :
    |f y - firstOrderTaylorModelAt f x y| ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let d : E := y - x
  -- Restrict `f` to the segment from `x` to `y` and record continuity on `[0,1]`.
  have hcont :
      ContinuousOn (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Icc (0 : ℝ) 1) := by
    have hsegCont : Continuous (fun t : ℝ ↦ f (x + t • d)) :=
      hf.continuous.comp (by fun_prop)
    have hlinCont : Continuous (fun t : ℝ ↦ t * inner ℝ (∇ f x) d) := by
      fun_prop
    exact ((hsegCont.sub continuous_const).sub hlinCont).continuousOn
  -- The derivative formula makes the corrected path differentiable on the open interval.
  have hdiff :
      DifferentiableOn ℝ (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact (segment_corrected_remainder_hasDerivAt (f := f) hf x d t).differentiableAt
      |>.differentiableWithinAt
  -- Apply the integral bound for a one-variable path with controlled derivative.
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
      (B := fun t : ℝ ↦ (L : ℝ) * t * ‖d‖ ^ (2 : ℕ))
      (a := (0 : ℝ)) (b := 1)
      (by norm_num) hcont hdiff
      (Filter.Eventually.of_forall fun t ht_mem ↦
        segment_corrected_remainder_deriv_abs_le (f := f) hf hgrad x d ht_mem)
      (by
        simpa [mul_assoc] using
          (show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
            intervalIntegrable_id).const_mul ((L : ℝ) * ‖d‖ ^ (2 : ℕ)))
  -- Rewrite the endpoint values back to the Taylor remainder from the statement.
  have hendpoint := segment_corrected_remainder_endpoints (f := f) x y
  have hR0 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 0 = 0 := by
    simpa [d] using hendpoint.1
  have hR1 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 1 =
        f y - firstOrderTaylorModelAt f x y := by
    simpa [d] using hendpoint.2
  rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hbound
  calc
    |f y - firstOrderTaylorModelAt f x y| ≤
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) := hbound
    _ = ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      -- Compute the scalar integral `∫₀¹ t dt = 1 / 2`.
      calc
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) =
            ∫ t in (0 : ℝ)..1, ((L : ℝ) * ‖d‖ ^ (2 : ℕ)) * t := by
              congr with t
              ring
        _ = ((L : ℝ) * ‖d‖ ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
              rw [intervalIntegral.integral_const_mul]
        _ = ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
              rw [integral_id]
              norm_num
              ring
    _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      simp [d]

-- Proof sketch: apply the core remainder estimate
-- `norm_taylor_remainder_le_half_lipschitzGradient_mul_sq`, then use that `a ≤ b` follows from
-- `|a| ≤ b`.
/-- The canonical first-order Taylor model at `x` gives a quadratic upper bound for `f y`. -/
lemma taylor_upper_bound_of_contDiffOne_withLipschitzGradient
    (x y : E) :
    f y ≤ firstOrderTaylorModelAt f x y + ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  have hrem :=
    abs_le.mp <| norm_taylor_remainder_le_half_lipschitzGradient_mul_sq hf hgrad x y
  linarith [hrem.2]

-- Proof sketch: apply the core remainder estimate
-- `norm_taylor_remainder_le_half_lipschitzGradient_mul_sq`, then use that `-b ≤ a` follows from
-- `|a| ≤ b` and rearrange.
/-- The canonical first-order Taylor model at `x` also gives the corresponding quadratic lower
bound for `f y`. -/
lemma taylor_lower_bound_of_contDiffOne_withLipschitzGradient
    (x y : E) :
    f y ≥ firstOrderTaylorModelAt f x y - ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  have hrem :=
    abs_le.mp <| norm_taylor_remainder_le_half_lipschitzGradient_mul_sq hf hgrad x y
  linarith [hrem.1]

omit hf hgrad

end

/-! ### Lemma_1_5_11 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {M : NNReal} {f : E → ℝ}

/- Lemma 1.5.11 is source-facing in second-order smooth optimization.

Source/core/bridge triage:
* source-facing: the gradient linearization remainder bound and the second-order Taylor-model
  error bound
* core/canonical: the owner hypothesis `HasLipschitzContinuousHessian M f`, written on the theorem
  surface as `f ∈ C22[M]`, together with the Hessian owner `hessian f x` and the quadratic owner
  model `secondOrderTaylorModelAt f x`
* bridge/view: evaluation of the owner model at `y`

Primary domain:
* second-order smooth optimization on real Hilbert spaces

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian M f`
* `HasLipschitzContinuousHessian.norm_sub_le`
* `hessian`
* `secondOrderTaylorModelAt`

Best owner abstraction:
* the canonical owner `HasLipschitzContinuousHessian M f`, written on the theorem surface as
  `f ∈ C22[M]`, together with the Hessian owner `hessian f x` and the owner quadratic model
  `secondOrderTaylorModelAt f x`

Primitive data:
* `f`
* `M`
* the base point `x`

Derived API:
* `HasLipschitzContinuousHessian.gradient_deviation_le`
* `HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le`

No extra local wrapper is introduced here; downstream files should use the owner hypothesis
`f ∈ C22[M]` together with the owner theorems below directly. -/

namespace HasLipschitzContinuousHessian

/-- Helper for Lemma 1.5.11: the Riesz map turns the dual-valued Fréchet derivative of a scalar
field into the primal gradient vector. -/
private abbrev rieszToPrimal : StrongDual ℝ E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Helper for Lemma 1.5.11: the affine segment `t ↦ x + t • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Lemma 1.5.11: a `C22` function has a continuous gradient field. -/
private theorem gradient_continuous (hf : f ∈ C22[M]) : Continuous (∇ f) := by
  let D : StrongDual ℝ E →L[ℝ] E := rieszToPrimal
  have hfd : Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)
  -- The gradient is the Riesz image of the Fréchet derivative.
  simpa [gradient, D] using D.continuous.comp hfd

/-- Helper for Lemma 1.5.11: the gradient has Fréchet derivative equal to the Hessian. -/
private theorem gradient_hasFDerivAt (hf : f ∈ C22[M]) (x : E) :
    HasFDerivAt (∇ f) (hessian f x) x := by
  let D : StrongDual ℝ E →L[ℝ] E := rieszToPrimal
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      (hf.contDiff.contDiffAt (x := x)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hgradDiff : DifferentiableAt ℝ (∇ f) x := by
    -- Rewrite the gradient through the Riesz map and compose differentiable maps.
    simpa [gradient, D] using D.differentiableAt.comp x hfdiff
  -- The derivative of the gradient is the Hessian by definition.
  simpa [hessian] using hgradDiff.hasFDerivAt

/-- Helper for Lemma 1.5.11: integrating the Hessian action along the segment recovers the
gradient increment. -/
private theorem segment_gradient_integral_eq
    (hf : f ∈ C22[M]) (x d : E) :
    ∇ f (x + d) - ∇ f x = ∫ t in 0..1, hessian f (x + t • d) d := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ ∇ f (x + s • d)) (hessian f (x + t • d) d) t := by
    intro t ht
    -- Differentiate the gradient after restricting it to the affine segment.
    simpa [Function.comp] using
      (gradient_hasFDerivAt (hf := hf) (x := x + t • d)).comp_hasDerivAt t
        (line_hasDerivAt x d t)
  have hcont :
      Continuous (fun t : ℝ ↦ hessian f (x + t • d) d) := by
    have hcontH : Continuous (fun t : ℝ ↦ hessian f (x + t • d)) :=
      (HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact hcontH.clm_apply continuous_const
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ hessian f (x + t • d) d) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  -- Apply the fundamental theorem of calculus to the gradient restriction.
  symm
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Helper for Lemma 1.5.11: the Hessian Lipschitz estimate gives the quadratic segment bound for
the linearized Hessian action. -/
private theorem segment_hessian_action_bound
    (hf : f ∈ C22[M]) (x d : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(hessian f (x + t • d) - hessian f x) d‖ ≤ (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
  have hnorm :
      ‖hessian f (x + t • d) - hessian f x‖ ≤ (M : ℝ) * ‖t • d‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      HasLipschitzContinuousHessian.norm_sub_le hf (x + t • d) x
  -- Convert the operator-norm bound into the action bound on the displacement vector.
  calc
    ‖(hessian f (x + t • d) - hessian f x) d‖
      ≤ ‖hessian f (x + t • d) - hessian f x‖ * ‖d‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((M : ℝ) * ‖t • d‖) * ‖d‖ := by
        gcongr
    _ = ((M : ℝ) * (t * ‖d‖)) * ‖d‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ = (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
        ring

/-- Helper for Lemma 1.5.11: the scalar restriction of `f` to a segment satisfies the usual first
fundamental-theorem identity. -/
private theorem segment_scalar_integral_eq
    (hf : f ∈ C22[M]) (x d : E) :
    f (x + d) - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d := by
  let φ : ℝ → ℝ := fun t ↦ f (x + t • d)
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    have hdiff : DifferentiableAt ℝ f (x + t • d) :=
      (hf.contDiff.contDiffAt (x := x + t • d)).differentiableAt (by norm_num)
    have hcomp :
        HasDerivAt (fun s : ℝ ↦ f (x + s • d))
          (fderiv ℝ f (x + t • d) d) t := by
      exact hdiff.hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt x d t)
    -- Rewrite the scalar derivative through the gradient pairing.
    simpa [φ, ψ, hdiff.hasGradientAt.fderiv_apply] using hcomp
  have hcont : Continuous ψ := by
    have hcontGrad : Continuous (fun t : ℝ ↦ ∇ f (x + t • d)) :=
      (gradient_continuous (hf := hf)).comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact hcontGrad.inner continuous_const
  have hint : IntervalIntegrable ψ MeasureTheory.volume 0 1 := hcont.intervalIntegrable 0 1
  -- Apply the fundamental theorem of calculus to the scalar restriction of `f`.
  symm
  simpa [φ, ψ] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Helper for Lemma 1.5.11: differentiating the segment gradient pairing produces the Hessian
quadratic form along the segment. -/
private theorem segment_gradient_pair_hasDerivAt
    (hf : f ∈ C22[M]) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d)
      (inner ℝ (hessian f (x + t • d) d) d) t := by
  have hgrad :
      HasDerivAt (fun s : ℝ ↦ ∇ f (x + s • d)) (hessian f (x + t • d) d) t := by
    -- Differentiate the gradient field along the affine segment first.
    simpa [Function.comp] using
      (gradient_hasFDerivAt (hf := hf) (x := x + t • d)).comp_hasDerivAt t
        (line_hasDerivAt x d t)
  -- Then pair with the fixed displacement vector.
  simpa using hgrad.inner ℝ (hasDerivAt_const t d)

/-- Helper for Lemma 1.5.11: the scalar first-order remainder of the segment gradient pairing is
the integral of the Hessian difference along the segment. -/
private theorem segment_gradient_pair_remainder_eq_integral
    (hf : f ∈ C22[M]) (x d : E) (u : ℝ) :
    inner ℝ (∇ f (x + u • d)) d - inner ℝ (∇ f x) d -
        u * inner ℝ (hessian f x d) d =
      ∫ s in 0..u, inner ℝ ((hessian f (x + s • d) - hessian f x) d) d := by
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
  let θ : ℝ → ℝ := fun t ↦ inner ℝ (hessian f (x + t • d) d) d
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) u,
        HasDerivAt (fun s : ℝ ↦ ψ s - s * θ 0) (θ t - θ 0) t := by
    intro t ht
    -- Subtract the constant linearization term before applying FTC once more.
    simpa [ψ, θ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using
      (segment_gradient_pair_hasDerivAt (hf := hf) (x := x) (d := d) t).sub
        ((hasDerivAt_id t).mul_const (θ 0))
  have hcontθ : Continuous θ := by
    have hcontHd : Continuous (fun t : ℝ ↦ hessian f (x + t • d) d) := by
      have hcontH : Continuous (fun t : ℝ ↦ hessian f (x + t • d)) :=
        (HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
          (continuous_const.add (continuous_id.smul continuous_const))
      exact hcontH.clm_apply continuous_const
    exact hcontHd.inner continuous_const
  have hint : IntervalIntegrable (fun t : ℝ ↦ θ t - θ 0) MeasureTheory.volume 0 u :=
    (hcontθ.sub continuous_const).intervalIntegrable 0 u
  have hftc :
      ∫ s in 0..u, (θ s - θ 0) = (ψ u - u * θ 0) - (ψ 0 - 0 * θ 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- Rewrite the FTC identity in the Hessian-difference form used later.
  calc
    inner ℝ (∇ f (x + u • d)) d - inner ℝ (∇ f x) d - u * inner ℝ (hessian f x d) d
      = (ψ u - u * θ 0) - (ψ 0 - 0 * θ 0) := by
          simp [ψ, θ]
          ring
    _ = ∫ s in 0..u, (θ s - θ 0) := by
          symm
          exact hftc
    _ = ∫ s in 0..u, inner ℝ ((hessian f (x + s • d) - hessian f x) d) d := by
          congr with s
          simp [θ, inner_sub_left]

/-- Helper for Lemma 1.5.11: integrating the scalar first-order remainder identity over the outer
segment parameter yields the source-style double-integral second-order remainder. -/
private theorem second_order_remainder_eq_double_integral
    (hf : f ∈ C22[M]) (x d : E) :
    f (x + d) - f x - inner ℝ (∇ f x) d -
        (1 / 2 : ℝ) * inner ℝ (hessian f x d) d =
      ∫ u in 0..1, ∫ s in 0..u, inner ℝ ((hessian f (x + s • d) - hessian f x) d) d := by
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
  let θ : ℝ → ℝ := fun t ↦ inner ℝ (hessian f (x + t • d) d) d
  have hcontψ : Continuous ψ := by
    have hcontGrad : Continuous (fun t : ℝ ↦ ∇ f (x + t • d)) :=
      (gradient_continuous (hf := hf)).comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact hcontGrad.inner continuous_const
  have hintψ : IntervalIntegrable ψ MeasureTheory.volume 0 1 := hcontψ.intervalIntegrable 0 1
  have hintConst : IntervalIntegrable (fun _ : ℝ ↦ ψ 0) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hintLin : IntervalIntegrable (fun u : ℝ ↦ u * θ 0) MeasureTheory.volume 0 1 :=
    (continuous_id.mul continuous_const).intervalIntegrable 0 1
  have houter :
      f (x + d) - f x - inner ℝ (∇ f x) d -
          (1 / 2 : ℝ) * inner ℝ (hessian f x d) d =
        ∫ u in 0..1, (ψ u - ψ 0 - u * θ 0) := by
    -- First rewrite the scalar remainder as an outer integral of the gradient-pairing remainder.
    rw [segment_scalar_integral_eq (hf := hf) (x := x) (d := d)]
    rw [show inner ℝ (∇ f x) d = ψ 0 by simp [ψ]]
    rw [show inner ℝ (hessian f x d) d = θ 0 by simp [θ]]
    rw [show (fun u : ℝ ↦ ψ u - ψ 0 - u * θ 0) = fun u ↦ (ψ u - ψ 0) - u * θ 0 by rfl]
    rw [intervalIntegral.integral_sub (hintψ.sub hintConst) hintLin]
    rw [intervalIntegral.integral_sub hintψ hintConst]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
    ring
  have hdouble :
      ∫ u in 0..1, (ψ u - ψ 0 - u * θ 0) =
        ∫ u in 0..1, ∫ s in 0..u, inner ℝ ((hessian f (x + s • d) - hessian f x) d) d := by
    -- Then integrate the pointwise gradient-pairing remainder formula in the outer variable.
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro u hu
    simpa [ψ, θ] using
      segment_gradient_pair_remainder_eq_integral (hf := hf) (x := x) (d := d) u
  exact houter.trans hdouble

/-- Helper for Lemma 1.5.11: the Hessian Lipschitz estimate gives the cubic segment bound for the
quadratic Hessian form. -/
private theorem segment_hessian_quadratic_bound
    (hf : f ∈ C22[M]) (x d : E) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |inner ℝ ((hessian f (x + s • d) - hessian f x) d) d| ≤
      (M : ℝ) * s * ‖d‖ ^ (3 : ℕ) := by
  -- Pair the action bound with the displacement vector once more.
  calc
    |inner ℝ ((hessian f (x + s • d) - hessian f x) d) d|
      ≤ ‖(hessian f (x + s • d) - hessian f x) d‖ * ‖d‖ := by
        simpa [real_inner_comm] using
          abs_real_inner_le_norm ((hessian f (x + s • d) - hessian f x) d) d
    _ ≤ ((M : ℝ) * s * ‖d‖ ^ (2 : ℕ)) * ‖d‖ := by
        gcongr
        exact segment_hessian_action_bound (hf := hf) (x := x) (d := d) hs
    _ = (M : ℝ) * s * ‖d‖ ^ (3 : ℕ) := by
        ring

/-- Lemma 1.5.11 (1): if `f ∈ C_M^{2,2}(ℝⁿ)`, then the first-order Taylor remainder of the
gradient at `x`, linearized by the Hessian `hessian f x`, is bounded by
`(M / 2) ‖y - x‖²`. -/
-- Proof sketch: write `∇ f y - ∇ f x` as the integral of the Hessian along the segment from `x`
-- to `y`, subtract the constant Hessian term at `x`, and estimate the resulting integral using
-- the global Lipschitz bound on `x ↦ hessian f x`.
theorem gradient_deviation_le
    (hf : f ∈ C22[M])
    (x y : E) :
    ‖∇ f y - ∇ f x - hessian f x (y - x)‖ ≤
      ((M : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let d : E := y - x
  have hy : x + d = y := by
    simp [d]
  have hcontIntegrand :
      Continuous (fun t : ℝ ↦ (hessian f (x + t • d) - hessian f x) d) := by
    have hcontH : Continuous (fun t : ℝ ↦ hessian f (x + t • d) - hessian f x) :=
      ((HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
    exact hcontH.clm_apply continuous_const
  have hintIntegrand :
      IntervalIntegrable (fun t : ℝ ↦ (hessian f (x + t • d) - hessian f x) d)
        MeasureTheory.volume 0 1 :=
    hcontIntegrand.intervalIntegrable 0 1
  have hintBound :
      IntervalIntegrable (fun t : ℝ ↦ (M : ℝ) * t * ‖d‖ ^ (2 : ℕ))
        MeasureTheory.volume 0 1 :=
    ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hmono :
      ∫ t in 0..1, ‖(hessian f (x + t • d) - hessian f x) d‖
        ≤ ∫ t in 0..1, (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
    -- Bound the integrand pointwise on the whole segment.
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hintIntegrand.norm hintBound ?_
    intro t ht
    exact segment_hessian_action_bound (hf := hf) (x := x) (d := d) ht
  have hrewrite :
      ∇ f y - ∇ f x - hessian f x d =
        ∫ t in 0..1, (hessian f (x + t • d) - hessian f x) d := by
    -- Rewrite the remainder as an integral of Hessian differences.
    rw [← hy, segment_gradient_integral_eq (hf := hf) (x := x) (d := d)]
    rw [show hessian f x d = ∫ t in 0..1, hessian f x d by
      simpa using (intervalIntegral.integral_const (a := (0 : ℝ)) (b := 1) (hessian f x d)).symm]
    have hsub0 :
        ∫ t in 0..1, (hessian f (x + t • d)) d - (hessian f x) d =
          (∫ t in 0..1, (hessian f (x + t • d)) d) - ∫ t in 0..1, (hessian f x) d := by
      simpa using
        (intervalIntegral.integral_sub
          (f := fun t : ℝ ↦ (hessian f (x + t • d)) d)
          (g := fun _ : ℝ ↦ (hessian f x) d)
          (μ := MeasureTheory.volume)
          (((HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
              (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
            |>.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1))
    have hsub :
        (∫ t in 0..1, (hessian f (x + t • d)) d) - ∫ t in 0..1, (hessian f x) d =
          ∫ t in 0..1, (hessian f (x + t • d)) d - (hessian f x) d := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub0.symm
    calc
      (∫ t in 0..1, (hessian f (x + t • d)) d) - ∫ t in 0..1, (hessian f x) d
        = ∫ t in 0..1, (hessian f (x + t • d)) d - (hessian f x) d := hsub
      _ = ∫ t in 0..1, (hessian f (x + t • d) - hessian f x) d := by
          refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro t ht
          simp
  -- Integrate the pointwise Hessian bound and compute `∫₀¹ t = 1 / 2`.
  calc
    ‖∇ f y - ∇ f x - hessian f x d‖
      = ‖∫ t in 0..1, (hessian f (x + t • d) - hessian f x) d‖ := by
          rw [hrewrite]
    _ ≤ ∫ t in 0..1, ‖(hessian f (x + t • d) - hessian f x) d‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm
            (f := fun t : ℝ ↦ (hessian f (x + t • d) - hessian f x) d)
            (a := (0 : ℝ)) (b := 1) (show (0 : ℝ) ≤ 1 by norm_num)
    _ ≤ ∫ t in 0..1, (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := hmono
    _ = ((M : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
          calc
            ∫ t in 0..1, (M : ℝ) * t * ‖d‖ ^ (2 : ℕ)
              = ∫ t in 0..1, ((M : ℝ) * ‖d‖ ^ (2 : ℕ)) * t := by
                  congr with t
                  ring
            _ = ((M : ℝ) * ‖d‖ ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                  rw [intervalIntegral.integral_const_mul, integral_id]
                  norm_num
            _ = ((M : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
                  ring
    _ = ((M : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
          simp [d]

/-- Lemma 1.5.11 (2): if `f ∈ C_M^{2,2}(ℝⁿ)`, then the second-order Taylor remainder of `f` at
`x` is bounded by `(M / 6) ‖y - x‖³`. -/
-- Proof sketch: compose `f` with the segment `τ ↦ x + τ • (y - x)`, use the double-integral form
-- of the second-order Taylor remainder on `[0, 1]`, identify the quadratic part with
-- `secondOrderTaylorModelAt f x y`, and bound the cubic integrand by the Hessian Lipschitz
-- estimate together with `|⟪A d, d⟫| ≤ ‖A‖ ‖d‖²`.
theorem secondOrderTaylorModel_error_le
    (hf : f ∈ C22[M])
    (x y : E) :
    |f y - secondOrderTaylorModelAt f x y| ≤
      ((M : ℝ) / 6) * ‖y - x‖ ^ (3 : ℕ) := by
  let d : E := y - x
  let r : ℝ → ℝ := fun u ↦
    inner ℝ (∇ f (x + u • d)) d - inner ℝ (∇ f x) d -
      u * inner ℝ (hessian f x d) d
  have hy : x + d = y := by
    simp [d]
  have hcont_r : Continuous r := by
    have hcontGrad : Continuous (fun u : ℝ ↦ ∇ f (x + u • d)) :=
      (gradient_continuous (hf := hf)).comp
        (continuous_const.add (continuous_id.smul continuous_const))
    have hconstGrad : Continuous (fun _ : ℝ ↦ inner ℝ (∇ f x) d) := continuous_const
    have hlin : Continuous (fun u : ℝ ↦ inner ℝ (hessian f x d) d * u) :=
      continuous_const.mul continuous_id
    -- The outer remainder is built from continuous pieces.
    simpa [r, mul_comm] using (hcontGrad.inner continuous_const).sub hconstGrad |>.sub hlin
  have hint_r : IntervalIntegrable r MeasureTheory.volume 0 1 := hcont_r.intervalIntegrable 0 1
  have hint_const_grad :
      IntervalIntegrable (fun _ : ℝ ↦ inner ℝ (∇ f x) d) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hint_lin :
      IntervalIntegrable (fun u : ℝ ↦ inner ℝ (hessian f x d) d * u) MeasureTheory.volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hint_bound :
      IntervalIntegrable (fun u : ℝ ↦ (((M : ℝ) / 2) * ‖d‖ ^ (3 : ℕ)) * u ^ (2 : ℕ))
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have houter :
      f y - secondOrderTaylorModelAt f x y = ∫ u in 0..1, r u := by
    -- Rewrite the scalar second-order remainder as the integral of the first-order remainder of
    -- the segment gradient pairing.
    rw [secondOrderTaylorModelAt_apply, ← hy]
    have hmodel :
        f (x + d) -
            (f x + inner ℝ (∇ f x) (x + d - x) +
              (1 / 2 : ℝ) * inner ℝ (hessian f x (x + d - x)) (x + d - x)) =
          f (x + d) - f x - inner ℝ (∇ f x) d -
            (1 / 2 : ℝ) * inner ℝ (hessian f x d) d := by
      simp
      ring
    rw [hmodel, segment_scalar_integral_eq (hf := hf) (x := x) (d := d)]
    have hsplit :
        ∫ u in 0..1, inner ℝ (∇ f (x + u • d)) d =
          (∫ u in 0..1, r u) +
            (inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d * (1 / 2 : ℝ)) := by
      have hEqInt :
          ∫ u in 0..1, inner ℝ (∇ f (x + u • d)) d =
            ∫ u in 0..1, inner ℝ (∇ f x) d + (inner ℝ (hessian f x d) d * u + r u) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro u hu
        simp [r]
        ring
      have hmain :
          ∫ u in 0..1, inner ℝ (∇ f x) d + (inner ℝ (hessian f x d) d * u + r u) =
            inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d * (1 / 2 : ℝ) +
              ∫ u in 0..1, r u := by
        rw [intervalIntegral.integral_add hint_const_grad (hint_lin.add hint_r)]
        rw [intervalIntegral.integral_const]
        rw [intervalIntegral.integral_add hint_lin hint_r]
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      exact hEqInt.trans <| hmain.trans <| by ring
    rw [hsplit]
    ring_nf
  have hr_bound :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        |r u| ≤ (((M : ℝ) / 2) * ‖d‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
    intro u hu
    have hintInner :
        IntervalIntegrable
          (fun s : ℝ ↦ inner ℝ ((hessian f (x + s • d) - hessian f x) d) d)
          MeasureTheory.volume 0 u := by
      have hcontInner :
          Continuous (fun s : ℝ ↦ inner ℝ ((hessian f (x + s • d) - hessian f x) d) d) := by
        have hcontHd :
            Continuous (fun s : ℝ ↦ (hessian f (x + s • d) - hessian f x) d) := by
          have hcontH :
              Continuous (fun s : ℝ ↦ hessian f (x + s • d) - hessian f x) :=
            ((HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
              (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
          exact hcontH.clm_apply continuous_const
        exact hcontHd.inner continuous_const
      exact hcontInner.intervalIntegrable 0 u
    have hintMajorant :
        IntervalIntegrable (fun s : ℝ ↦ (M : ℝ) * s * ‖d‖ ^ (3 : ℕ))
          MeasureTheory.volume 0 u :=
      ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 u
    have hmono :
        ∫ s in 0..u, |inner ℝ ((hessian f (x + s • d) - hessian f x) d) d|
          ≤ ∫ s in 0..u, (M : ℝ) * s * ‖d‖ ^ (3 : ℕ) := by
      -- Bound the inner Hessian remainder by the cubic Lipschitz majorant on `[0,u]`.
      refine intervalIntegral.integral_mono_on hu.1 hintInner.norm hintMajorant ?_
      intro s hs
      exact segment_hessian_quadratic_bound (hf := hf) (x := x) (d := d)
        ⟨hs.1, hs.2.trans hu.2⟩
    have hremainder :
        r u =
          ∫ s in 0..u, inner ℝ ((hessian f (x + s • d) - hessian f x) d) d := by
      exact segment_gradient_pair_remainder_eq_integral (hf := hf) (x := x) (d := d) u
    -- Estimate the inner remainder by integrating the cubic majorant on `[0,u]`.
    calc
      |r u|
        = |∫ s in 0..u, inner ℝ ((hessian f (x + s • d) - hessian f x) d) d| := by
            rw [hremainder]
      _ ≤ ∫ s in 0..u, |inner ℝ ((hessian f (x + s • d) - hessian f x) d) d| := by
            exact intervalIntegral.abs_integral_le_integral_abs (f := fun s : ℝ ↦
              inner ℝ ((hessian f (x + s • d) - hessian f x) d) d) hu.1
      _ ≤ ∫ s in 0..u, (M : ℝ) * s * ‖d‖ ^ (3 : ℕ) := hmono
      _ = (((M : ℝ) / 2) * ‖d‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
            calc
              ∫ s in 0..u, (M : ℝ) * s * ‖d‖ ^ (3 : ℕ)
                = ∫ s in 0..u, ((M : ℝ) * ‖d‖ ^ (3 : ℕ)) * s := by
                    congr with s
                    ring
              _ = ((M : ℝ) * ‖d‖ ^ (3 : ℕ)) * (u ^ (2 : ℕ) / 2) := by
                    rw [intervalIntegral.integral_const_mul, integral_id]
                    ring
              _ = (((M : ℝ) / 2) * ‖d‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
                    ring
  have hmono_outer :
      ∫ u in 0..1, |r u| ≤
        ∫ u in 0..1, (((M : ℝ) / 2) * ‖d‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
    -- Apply the pointwise quadratic remainder bound on the full outer interval.
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hint_r.norm hint_bound ?_
    intro u hu
    exact hr_bound u hu
  -- Integrate the pointwise bound `|r(u)| ≤ (M / 2) ‖d‖³ u²` and compute `∫₀¹ u² = 1 / 3`.
  calc
    |f y - secondOrderTaylorModelAt f x y| = |∫ u in 0..1, r u| := by
      rw [houter]
    _ ≤ ∫ u in 0..1, |r u| := by
      exact intervalIntegral.abs_integral_le_integral_abs (f := r) (show (0 : ℝ) ≤ 1 by norm_num)
    _ ≤ ∫ u in 0..1, (((M : ℝ) / 2) * ‖d‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := hmono_outer
    _ = ((M : ℝ) / 6) * ‖d‖ ^ (3 : ℕ) := by
          rw [intervalIntegral.integral_const_mul, integral_pow]
          ring
    _ = ((M : ℝ) / 6) * ‖y - x‖ ^ (3 : ℕ) := by
          simp [d]

end HasLipschitzContinuousHessian

end

end

/-! ### Theorem_1_5_12 (from Chap01) -/
open scoped Gradient MatrixOrder

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 1.5.12 is source-facing at the Euclidean matrix view of Hessian-Lipschitz control.

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian M f`, written on the theorem surface as `f ∈ C22[M]`, via
  Definition 1.5.3;
* `hessian f x`, the intrinsic Hessian owner from Definition 1.4.16;
* `hessianMatrix` from Definition 1.4.16;
* `fderiv_gradient_isSymmetric_of_contDiffAt` and `hessianMatrix_isSymm_of_contDiffAt` from
  Theorem 1.4.19;
* `ContinuousLinearMap.isPositive_iff` and `Matrix.isPositive_toEuclideanLin_iff`.

Owner abstraction:
* the Hessian operator `fderiv ℝ (∇ f) x`, with `hessianMatrix f x` as its Euclidean matrix view.

Primitive data:
* `f`
* `M`
* `x`
* `y`

Derived API:
* the operator-norm estimate `HasLipschitzContinuousHessian.norm_sub_le hf y x`
* the intrinsic Loewner bounds on `hessian f x` below;
* the Euclidean matrix Loewner bounds obtained from that intrinsic theorem through
  `hessianMatrix_toEuclideanLin`
-/

/-- If `f` has `M`-Lipschitz Hessian, then the intrinsic Hessians at `x` and `y` differ by at
most `M ‖y - x‖ I` in Loewner order. -/
theorem hessian_loewner_bounds_of_hessian_lipschitz
    {M : NNReal} {f : E → ℝ} (hf : f ∈ C22[M]) (x y : E) :
    let s : ℝ := (M : ℝ) * ‖y - x‖
    hessian f x - s • 1 ≤ hessian f y ∧
      hessian f y ≤ hessian f x + s • 1 := by
  let Δ : E →L[ℝ] E := hessian f y - hessian f x
  let s : ℝ := (M : ℝ) * ‖y - x‖
  have hΔ_symm : Δ.IsSymmetric := by
    dsimp [Δ]
    exact (fderiv_gradient_isSymmetric_of_contDiffAt
      (hf.contDiff.contDiffAt : ContDiffAt ℝ 2 f y)).sub
      (fderiv_gradient_isSymmetric_of_contDiffAt
        (hf.contDiff.contDiffAt : ContDiffAt ℝ 2 f x))
  have hΔ_norm : ‖Δ‖ ≤ s := by
    dsimp [Δ, s]
    exact HasLipschitzContinuousHessian.norm_sub_le hf y x
  have hquad_bound (u : E) :
      |inner ℝ (Δ u) u| ≤ s * ‖u‖ ^ (2 : ℕ) := by
    calc
      |inner ℝ (Δ u) u| ≤ ‖Δ u‖ * ‖u‖ := by
        simpa [real_inner_comm] using abs_real_inner_le_norm (Δ u) u
      _ ≤ (‖Δ‖ * ‖u‖) * ‖u‖ := by
        gcongr
        exact Δ.le_opNorm u
      _ = ‖Δ‖ * ‖u‖ ^ (2 : ℕ) := by ring
      _ ≤ s * ‖u‖ ^ (2 : ℕ) := by
        gcongr
  have hsI_symm : (s • (1 : E →L[ℝ] E)).IsSymmetric := by
    intro u v
    simp [real_inner_smul_left, real_inner_smul_right]
  have hupper_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) - Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.sub hΔ_symm
    · intro u
      have hu : inner ℝ (Δ u) u ≤ s * ‖u‖ ^ (2 : ℕ) := (abs_le.mp (hquad_bound u)).2
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) - Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) - inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_sub_left]
      rw [hrewrite]
      linarith
  have hlower_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) + Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.add hΔ_symm
    · intro u
      have hu : -(s * ‖u‖ ^ (2 : ℕ)) ≤ inner ℝ (Δ u) u := (abs_le.mp (hquad_bound u)).1
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) + Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) + inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_add_left]
      rw [hrewrite]
      linarith
  constructor
  · rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hlower_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlower_nonneg
  · rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hupper_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hupper_nonneg

section Euclidean

variable {n : ℕ}

local notation "EFin" => EuclideanSpace ℝ (Fin n)

/-- Theorem 1.5.12: if `f : ℝⁿ → ℝ` has `M`-Lipschitz Hessian, then `∇² f x` and `∇² f y`
differ by at most `M ‖y - x‖ I` in the Loewner order. -/
-- Proof sketch: apply the intrinsic Hessian comparison theorem above in the Hilbert-space owner
-- `hessian f x`, then transport the two operator inequalities through the Euclidean matrix bridge
-- `hessianMatrix_toEuclideanLin`.
theorem hessianMatrix_loewner_bounds_of_hessian_lipschitz
    {M : NNReal} {f : EFin → ℝ} (hf : f ∈ C22[M]) (x y : EFin) :
    let s : ℝ := (M : ℝ) * ‖y - x‖
    ∇² f x - s • 1 ≤ ∇² f y ∧
      ∇² f y ≤ ∇² f x + s • 1 := by
  let s : ℝ := (M : ℝ) * ‖y - x‖
  have hcore := hessian_loewner_bounds_of_hessian_lipschitz hf x y
  dsimp [s] at hcore ⊢
  rcases hcore with ⟨hlower, hupper⟩
  have hlower_pos :
      (hessian f y - (hessian f x - s • (1 : EFin →L[ℝ] EFin))).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hlower
  have hupper_pos :
      ((hessian f x + s • (1 : EFin →L[ℝ] EFin)) - hessian f y).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hupper
  constructor
  · refine sub_nonneg.mp ?_
    rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    change
      (((∇² f y - (∇² f x - s • 1)).toEuclideanLin : EFin →ₗ[ℝ] EFin)).IsPositive
    have hbridge :
        ((∇² f y - (∇² f x - s • 1)).toEuclideanLin : EFin →ₗ[ℝ] EFin) =
          ((hessian f y - (hessian f x - s • (1 : EFin →L[ℝ] EFin))) : EFin →ₗ[ℝ] EFin) := by
      calc
        ((∇² f y - (∇² f x - s • 1)).toEuclideanLin : EFin →ₗ[ℝ] EFin)
            = ((∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin) -
                (((∇² f x).toEuclideanLin : EFin →ₗ[ℝ] EFin) - s • LinearMap.id) := by
                    simp
        _ = (hessian f y : EFin →ₗ[ℝ] EFin) -
              ((hessian f x : EFin →ₗ[ℝ] EFin) - s • LinearMap.id) := by
                rw [hessianMatrix_toEuclideanLin, hessianMatrix_toEuclideanLin]
        _ = ((hessian f y - (hessian f x - s • (1 : EFin →L[ℝ] EFin))) : EFin →ₗ[ℝ] EFin) := by
              ext z
              simp
    rw [hbridge]
    exact hlower_pos.toLinearMap
  · refine sub_nonneg.mp ?_
    rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    change
      (((∇² f x + s • 1 - ∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin)).IsPositive
    have hbridge :
        ((∇² f x + s • 1 - ∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin) =
          (((hessian f x + s • (1 : EFin →L[ℝ] EFin)) - hessian f y) : EFin →ₗ[ℝ] EFin) := by
      calc
        ((∇² f x + s • 1 - ∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin)
            = ((∇² f x).toEuclideanLin : EFin →ₗ[ℝ] EFin) +
                s • LinearMap.id - ((∇² f y).toEuclideanLin : EFin →ₗ[ℝ] EFin) := by
                    simp
        _ = (hessian f x : EFin →ₗ[ℝ] EFin) + s • LinearMap.id -
              (hessian f y : EFin →ₗ[ℝ] EFin) := by
                rw [hessianMatrix_toEuclideanLin, hessianMatrix_toEuclideanLin]
        _ = (((hessian f x + s • (1 : EFin →L[ℝ] EFin)) - hessian f y) : EFin →ₗ[ℝ] EFin) := by
              ext z
              simp
    rw [hbridge]
    exact hupper_pos.toLinearMap

end Euclidean

end
