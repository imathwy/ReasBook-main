import Mathlib
import FirstOrderMethodsinOptimization.Chap05.Definition_5_1
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_61

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DualNorm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 10.65 is `source-facing`: it is the one-step sufficient-decrease estimate for the
non-Euclidean gradient method. Domain sampling points to the Chapter 5 smoothness owner
`is_l_smooth_on`, Chapter 10's dual-norm owner surface `‖·‖_*`, Chapter 6's positive-scalar
owner `PosReal`, and Chapter 10's primal-counterpart owner `Λ[·]` for the chosen descent
direction. The primitive data are therefore just the current point `x`, the positive curvature
parameter `L`, and the chosen primal counterpart `xDagger`; the trial iterate is the displayed
update `x - (‖f'(x)‖_* / L) • xDagger`, not an additional packaged owner. -/

-- Proof sketch: use `hf` on `Set.univ` to obtain differentiability of `f` at `x` and the
-- descent estimate for the pair
-- `(x, x - (‖f'(x)‖_* / L) • xDagger)`. Rewrite the derivative pairing with
-- `apply_eq_norm_of_mem_primalCounterparts hDagger`, and reduce the squared norm term with
-- `norm_eq_one_of_mem_primalCounterparts (by intro h; simpa [h] using hDagger) hDagger`.
/-- Helper for Lemma 10.65: global smoothness on `Set.univ` yields the Fréchet-derivative
descent inequality along any chord. -/
lemma is_l_smooth_on_univ_fderiv_descent
    {f : E → ℝ} {Lf : NNReal} (hf : is_l_smooth_on f Set.univ Lf)
    (x y : E) :
    f y ≤ f x + fderiv ℝ f x (y - x) + ((Lf : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  rcases (is_l_smooth_on_iff.mp hf) with ⟨hdiff, hLip⟩
  let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  let a0 : ℝ := fderiv ℝ f x (y - x)
  let s : ℝ := ‖y - x‖ ^ (2 : ℕ)
  let B : ℝ → ℝ := fun t ↦ f x + t * a0 + ((Lf : ℝ) / 2) * t ^ (2 : ℕ) * s
  have hdiff_all : ∀ z : E, DifferentiableAt ℝ f z := fun z ↦ hdiff z (by simp)
  have hLip_all :
      ∀ z w : E, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ (Lf : ℝ) * ‖z - w‖ := fun z w ↦
    hLip z (by simp) w (by simp)
  have hφ_deriv :
      ∀ t : ℝ,
        HasDerivAt φ (fderiv ℝ f (AffineMap.lineMap x y t) (y - x)) t := by
    intro t
    -- Differentiate the restriction of `f` to the segment from `x` to `y`.
    simpa [φ] using
      HasFDerivAt.comp_hasDerivAt
        (x := t)
        (l := f)
        (f := AffineMap.lineMap x y)
        (hdiff_all _).hasFDerivAt
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hφ_deriv t).continuousAt.continuousWithinAt
  have hB_deriv : ∀ t : ℝ, HasDerivAt B (a0 + (Lf : ℝ) * t * s) t := by
    intro t
    have hlin : HasDerivAt (fun u : ℝ ↦ u * a0) a0 t := by
      simpa [one_mul] using (hasDerivAt_id t).mul_const a0
    have hquad :
        HasDerivAt
          (fun u : ℝ ↦ ((Lf : ℝ) / 2) * u ^ (2 : ℕ) * s)
          ((Lf : ℝ) * t * s) t := by
      -- The barrier derivative is exactly the linear growth term used in the comparison.
      simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_pow 2 t).const_mul ((Lf : ℝ) / 2)).mul_const s)
    -- Add the linearization term and the quadratic barrier.
    convert ((hasDerivAt_const t (f x)).add hlin).add hquad using 1
    · simp [a0, s, add_comm]
  have hB_cont : ContinuousOn B (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hB_deriv t).continuousAt.continuousWithinAt
  have hbound :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        fderiv ℝ f (AffineMap.lineMap x y t) (y - x) ≤ a0 + (Lf : ℝ) * t * s := by
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have hline_norm :
        ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
      calc
        ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by
          simp [AffineMap.lineMap_apply_module']
        _ = ‖t‖ * ‖y - x‖ := norm_smul _ _
        _ = t * ‖y - x‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    have hnorm :
        ‖(fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x)‖ ≤
          (Lf : ℝ) * t * s := by
      calc
        ‖(fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x)‖
            ≤ ‖fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x‖ * ‖y - x‖ := by
              exact (fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x).le_opNorm (y - x)
        _ ≤ ((Lf : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
              exact mul_le_mul_of_nonneg_right
                (hLip_all (AffineMap.lineMap x y t) x) (norm_nonneg _)
        _ = ((Lf : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
              rw [hline_norm]
        _ = (Lf : ℝ) * t * s := by
              dsimp [s]
              rw [pow_two]
              ring
    have hlinear :
        (fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x) ≤
          (Lf : ℝ) * t * s := by
      exact (le_abs_self _).trans hnorm
    have hrewrite :
        (fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x) =
          fderiv ℝ f (AffineMap.lineMap x y t) (y - x) - a0 := by
      simp [a0]
    rw [hrewrite] at hlinear
    linarith
  have hcompare :=
    image_le_of_deriv_right_le_deriv_boundary
      hφ_cont
      (fun t ht ↦ (hφ_deriv t).hasDerivWithinAt)
      (by simp [φ, B])
      hB_cont
      (fun t ht ↦ (hB_deriv t).hasDerivWithinAt)
      hbound
  -- Evaluate the one-dimensional comparison at the right endpoint of the segment.
  have hendpoint : φ 1 ≤ B 1 := hcompare (by simp)
  simpa [φ, B, a0, s, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    pow_two, mul_assoc, mul_left_comm, mul_comm] using hendpoint

/-- Helper for Lemma 10.65: the primal-counterpart equality rewrites the linear term in the
non-Euclidean step. -/
lemma scaled_primal_counterpart_pairing
    {a : E →L[ℝ] ℝ} {xDagger : E} (hDagger : xDagger ∈ Λ[a]) (L : PosReal) :
    a (-(‖a‖ / (L : ℝ)) • xDagger) = -((‖a‖ / (L : ℝ)) * ‖a‖) := by
  -- Expand the scalar action and use the norm-attainment identity from `Λ[a]`.
  calc
    a (-(‖a‖ / (L : ℝ)) • xDagger) = (-(‖a‖ / (L : ℝ))) * a xDagger := by
      simp
    _ = -((‖a‖ / (L : ℝ)) * ‖a‖) := by
      rw [apply_eq_norm_of_mem_primalCounterparts hDagger]
      ring

/-- Helper for Lemma 10.65: the step direction has squared norm at most the square of its
scalar coefficient because primal counterparts lie in the unit ball. -/
lemma scaled_primal_counterpart_norm_sq_le
    {a : E →L[ℝ] ℝ} {xDagger : E} (hDagger : xDagger ∈ Λ[a]) (L : PosReal) :
    ‖-(‖a‖ / (L : ℝ)) • xDagger‖ ^ (2 : ℕ) ≤ (‖a‖ / (L : ℝ)) ^ (2 : ℕ) := by
  have hscale_nonneg : 0 ≤ ‖a‖ / (L : ℝ) := by
    exact div_nonneg (norm_nonneg _) L.2.le
  have hnorm :
      ‖-(‖a‖ / (L : ℝ)) • xDagger‖ ≤ ‖a‖ / (L : ℝ) := by
    calc
      ‖-(‖a‖ / (L : ℝ)) • xDagger‖ = (‖a‖ / (L : ℝ)) * ‖xDagger‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hscale_nonneg]
      _ ≤ (‖a‖ / (L : ℝ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hDagger.1 hscale_nonneg
      _ = ‖a‖ / (L : ℝ) := by
        ring
  have hleft_nonneg : 0 ≤ ‖-(‖a‖ / (L : ℝ)) • xDagger‖ := norm_nonneg _
  have hright_nonneg : 0 ≤ ‖a‖ / (L : ℝ) := hscale_nonneg
  -- Square the norm bound to match the quadratic remainder term.
  nlinarith [hnorm, hleft_nonneg, hright_nonneg]

/-- Lemma 10.65: if `f` is globally `L_f`-smooth and `xDagger ∈ Λ_{f'(x)}`, then the
non-Euclidean trial point
`x - (‖f'(x)‖_* / L) • xDagger`
satisfies the sufficient-decrease inequality
`f(x - (‖f'(x)‖_* / L) • xDagger) ≤ f(x) - ((L - L_f / 2) / L^2) ‖f'(x)‖_*^2`. -/
theorem non_euclidean_gradient_method_sufficient_decrease
    {f : E → ℝ} {Lf : NNReal} (hf : is_l_smooth_on f Set.univ Lf)
    (x : E) (L : PosReal) (xDagger : E)
    (hDagger : xDagger ∈ Λ[fderiv ℝ f x]) :
    f (x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger) ≤
      f x -
        (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) *
          ‖fderiv ℝ f x‖_* ^ 2 := by
  set a : E →L[ℝ] ℝ := fderiv ℝ f x
  set α : ℝ := ‖a‖ / (L : ℝ)
  set d : E := -α • xDagger
  have htrial : x + d = x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger := by
    simp [a, α, d, sub_eq_add_neg]
  have hdescent :
      f (x + d) ≤ f x + a d + ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
    -- Apply the Banach-space descent lemma to the trial point `x + d`.
    simpa [a, d] using
      is_l_smooth_on_univ_fderiv_descent (f := f) (Lf := Lf) hf x (x + d)
  have hpair : a d = -((α : ℝ) * ‖a‖) := by
    -- The primal-counterpart equality identifies the linear term with `-α ‖a‖`.
    simpa [α, d] using scaled_primal_counterpart_pairing (a := a) (xDagger := xDagger) hDagger L
  have hnorm_sq : ‖d‖ ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by
    -- The unit-ball part of `Λ[a]` controls the norm of the step direction.
    simpa [α, d] using scaled_primal_counterpart_norm_sq_le (a := a) (xDagger := xDagger) hDagger L
  have hquad :
      ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) ≤ ((Lf : ℝ) / 2) * α ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hnorm_sq (by positivity)
  have hL_ne : (L : ℝ) ≠ 0 := by
    exact ne_of_gt L.2
  have hcoeff :
      f x + (-((α : ℝ) * ‖a‖) + ((Lf : ℝ) / 2) * α ^ (2 : ℕ)) =
        f x - (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) * ‖a‖ ^ (2 : ℕ) := by
    -- Normalize the coefficient of `‖a‖²` to the textbook form.
    dsimp [α]
    field_simp [hL_ne]
    ring
  have hmain :
      f (x + d) ≤
        f x - (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) * ‖a‖ ^ (2 : ℕ) := by
    calc
      f (x + d) ≤ f x + a d + ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := hdescent
      _ = f x + (-((α : ℝ) * ‖a‖) + ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ)) := by
            rw [hpair]
            ring
      _ ≤ f x + (-((α : ℝ) * ‖a‖) + ((Lf : ℝ) / 2) * α ^ (2 : ℕ)) := by
            linarith
      _ = f x - (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) * ‖a‖ ^ (2 : ℕ) := hcoeff
  -- Rewrite the trial point and derivative norm back to the source-facing statement.
  simpa [a, htrial] using hmain

end
