import Mathlib
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22»
import DifferentialForms_Cartan_1970.IV.section16.«0002_Theorem_IV_4_extra_2»
import DifferentialForms_Cartan_1970.IV.section17.«0012_Exercise_4».CircleBoundaryGeometry

open Filter InnerProductSpace Laplacian Metric Real Set Topology
open scoped BigOperators InnerProductSpace
/-- Helper for Exercise 4: integrating a real `1`-form along the positive circle path is the
textbook `θ`-integral after the linear reparametrization `θ = 2π t`. -/
lemma curveIntegral_positive_circle_path_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℝ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in positive_circle_path a r, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  let h : ℝ → ℝ := fun θ ↦ ω (circleMap a r θ) (deriv (circleMap a r) θ)
  have hcongr :
      ∫ t in (0 : ℝ)..1,
          ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t) =
        ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
    -- On the open interval, the path extension is exactly the standard circle parametrization.
    have hcongr_ae :
        (fun t ↦
            ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t))
          =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
              (fun t ↦ (2 * Real.pi : ℝ) • h (t * (2 * Real.pi))) := by
      rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hlocal :
          (positive_circle_path a r).extend =ᶠ[nhds t]
            fun s : ℝ ↦ circleMap a r (s * (2 * Real.pi)) := by
        have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
        filter_upwards [hIoo] with s hs
        rw [Path.extend_apply (positive_circle_path a r) ⟨hs.1.le, hs.2.le⟩]
        simp [positive_circle_path, mul_comm]
      have hderiv :
          deriv (positive_circle_path a r).extend t =
            (2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi)) := by
        rw [Filter.EventuallyEq.deriv_eq hlocal]
        simpa using
          (((hasDerivAt_circleMap a r (t * (2 * Real.pi))).scomp t
            (hasDerivAt_mul_const (2 * Real.pi : ℝ))).deriv)
      have hext :
          (positive_circle_path a r).extend t = circleMap a r (t * (2 * Real.pi)) :=
        Filter.EventuallyEq.eq_of_nhds hlocal
      -- Evaluate the `1`-form on the chain-rule tangent vector of the circle.
      calc
        ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t) =
            ω (circleMap a r (t * (2 * Real.pi)))
              ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) := by
          rw [hext, hderiv]
        _ = (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
          change
            ω (circleMap a r (t * (2 * Real.pi)))
                ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) =
              (2 * Real.pi : ℝ) •
                ω (circleMap a r (t * (2 * Real.pi))) (deriv (circleMap a r) (t * (2 * Real.pi)))
          rw [map_smul]
    exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
  have hsmul :
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) =
        (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := by
    simpa using intervalIntegral.integral_smul (a := (0 : ℝ)) (b := 1)
      (r := (2 * Real.pi : ℝ)) (f := fun t ↦ h (t * (2 * Real.pi)))
  -- First rewrite the curve integral as a parameter integral, then perform the `θ = 2π t`
  -- change of variables.
  rw [curveIntegral_eq_intervalIntegral_deriv]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t) =
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := hcongr
    _ = (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := hsmul
    _ = ∫ θ in (0 : ℝ) * (2 * Real.pi)..1 * (2 * Real.pi), h θ := by
      simpa using (intervalIntegral.smul_integral_comp_mul_right
        (f := h) (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi))
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, h θ := by
      simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
        MeasureTheory.restrict_Ioc_eq_restrict_Icc]

/-- Helper for Exercise 4: the closed-path wrapper used by the oriented-boundary API does not
change the positive-circle integral. -/
lemma curveIntegral_positive_circle_toClosedPath_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℝ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  -- Remove the harmless endpoint cast inserted by `toClosedPath.toPath`, then use the explicit
  -- parametrization of the positive circle.
  calc
    ∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, ω z =
        ∫ᶜ z in positive_circle_path a r, ω z := by
          rw [toClosedPath_toPath_eq_cast]
          simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
          exact curveIntegral_positive_circle_path_eq_intervalIntegral (ω := ω)

/-- Helper for Exercise 4: varying the real coordinate in `Complex.mk` differentiates to the
horizontal unit direction. -/
lemma hasDerivAt_complex_mk_re (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.mk t y) 1 x := by
  -- The horizontal line is the real-axis embedding followed by translation.
  have hrepr : (fun t : ℝ ↦ Complex.mk t y) = fun t : ℝ ↦ (t : ℂ) + y * Complex.I := by
    funext t
    apply Complex.ext <;> simp [Complex.mk]
  rw [hrepr]
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add (y * Complex.I)

/-- Helper for Exercise 4: varying the imaginary coordinate in `Complex.mk` differentiates to the
vertical unit direction `I`. -/
lemma hasDerivAt_complex_mk_im (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.mk x t) Complex.I y := by
  -- The vertical line is the real-axis embedding, then multiplication by `I`, then translation.
  have hrepr : (fun t : ℝ ↦ Complex.mk x t) = fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * Complex.I := by
    funext t
    apply Complex.ext <;> simp [Complex.mk]
  rw [hrepr]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ)

/-- Helper for Exercise 4: the real and imaginary coordinates of a complex tangent encode
multiplication by `-I`. -/
lemma complex_mk_im_neg_re_eq_neg_I_mul (v : ℂ) :
    Complex.mk v.im (-v.re) = -Complex.I * v := by
  -- Expanding both sides shows the expected quarter-turn identity.
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Helper for Exercise 4: differentiating the first derivative along the vertical real line in a
fixed tangent direction gives the corresponding `I,v` entry of the second iterated derivative. -/
lemma hasDerivAt_fderiv_apply_const_along_vertical {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z v : ℂ} (hz : z ∈ D) :
    HasDerivAt (fun y : ℝ ↦ fderiv ℝ f (Complex.mk z.re y) v)
      (iteratedFDeriv ℝ 2 f z ![Complex.I, v]) z.im := by
  -- Package the second derivative as a derivative of the derivative field, then compose with the
  -- vertical coordinate line before the final `fderiv_clm_apply` rewrite.
  have h2 : ContDiffAt ℝ 2 f z := hf.contDiffAt (hD.mem_nhds hz)
  have hfd :
      DifferentiableAt ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z := by
    exact (((h2.fderiv_right_succ).clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ ↦ v) z)).differentiableAt one_ne_zero)
  have hline :
      HasDerivAt (fun y : ℝ ↦ fderiv ℝ f (Complex.mk z.re y) v)
        (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z Complex.I) z.im := by
    simpa [Function.comp] using
      hfd.hasFDerivAt.comp_hasDerivAt z.im (hasDerivAt_complex_mk_im z.re z.im)
  -- Unfold the derivative of the derivative field only at the endpoint to identify the
  -- iterated Fréchet derivative component.
  convert hline using 1
  rw [fderiv_clm_apply (h2.fderiv_right_succ.differentiableAt one_ne_zero)
    (differentiableAt_const v)]
  simpa [iteratedFDeriv_two_apply]

/-- Helper for Exercise 4: differentiating the first derivative along the horizontal real line in
a fixed tangent direction gives the corresponding `1,v` entry of the second iterated derivative. -/
lemma hasDerivAt_fderiv_apply_const_along_horizontal {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z v : ℂ} (hz : z ∈ D) :
    HasDerivAt (fun x : ℝ ↦ fderiv ℝ f (Complex.mk x z.im) v)
      (iteratedFDeriv ℝ 2 f z ![1, v]) z.re := by
  -- Package the second derivative as a derivative of the derivative field, then compose with the
  -- horizontal coordinate line before the final `fderiv_clm_apply` rewrite.
  have h2 : ContDiffAt ℝ 2 f z := hf.contDiffAt (hD.mem_nhds hz)
  have hfd :
      DifferentiableAt ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z := by
    exact (((h2.fderiv_right_succ).clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ ↦ v) z)).differentiableAt one_ne_zero)
  have hline :
      HasDerivAt (fun x : ℝ ↦ fderiv ℝ f (Complex.mk x z.im) v)
        (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z 1) z.re := by
    simpa [Function.comp] using
      hfd.hasFDerivAt.comp_hasDerivAt z.re (hasDerivAt_complex_mk_re z.re z.im)
  -- Unfold the derivative of the derivative field only at the endpoint to identify the
  -- iterated Fréchet derivative component.
  convert hline using 1
  rw [fderiv_clm_apply (h2.fderiv_right_succ.differentiableAt one_ne_zero)
    (differentiableAt_const v)]
  simpa [iteratedFDeriv_two_apply]

/-- Helper for Exercise 4: evaluating the Green-Riemann boundary form on a tangent vector is the
Fréchet derivative applied to the quarter-turned tangent. -/
lemma boundary_form_apply_eq_fderiv_rotated_tangent {f : ℂ → ℝ} (z v : ℂ) :
    (((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy) z v) =
      fderiv ℝ f z (Complex.mk v.im (-v.re)) := by
  -- Normalize the planar differential form first, then rewrite the rotated tangent in the real
  -- basis `{1, I}` so the linearity of `fderiv` applies directly.
  rw [Complex.planarDifferentialForm_apply]
  have hsplit :
      Complex.mk v.im (-v.re) = v.im • (1 : ℂ) + (-v.re) • Complex.I := by
    apply Complex.ext <;> simp [Complex.mk]
  calc
    v.re * (-fderiv ℝ f z Complex.I) + v.im * fderiv ℝ f z 1
      = v.im • fderiv ℝ f z 1 + (-v.re) • fderiv ℝ f z Complex.I := by
          ring
    _ = fderiv ℝ f z (v.im • (1 : ℂ) + (-v.re) • Complex.I) := by
          rw [map_add, map_smul, map_smul]
    _ = fderiv ℝ f z (Complex.mk v.im (-v.re)) := by
          rw [hsplit]

/-- Helper for Exercise 4: quarter-turning the angular circle tangent gives the radial vector on
the same circle. -/
lemma rotated_circle_tangent_eq_radial_vector {a : ℂ} {r θ : ℝ} :
    Complex.mk (deriv (circleMap a r) θ).im (-(deriv (circleMap a r) θ).re) = circleMap 0 r θ := by
  -- The standard circle derivative is `circleMap 0 r θ * I`, and multiplying by `-I` rotates it
  -- back to the radial vector.
  rw [complex_mk_im_neg_re_eq_neg_I_mul, deriv_circleMap]
  ring_nf
  simp

/-- Helper for Exercise 4: the Green-Riemann boundary `1`-form on the circle is exactly the radial
derivative multiplied by the radius. -/
lemma circle_boundary_form_eq_radial_deriv_mul_radius {f : ℂ → ℝ} {a : ℂ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (circleMap a r θ)) :
    (((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy)
        (circleMap a r θ) (deriv (circleMap a r) θ)) =
      deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
  -- Route correction: first rewrite the Green boundary form as one `fderiv` evaluation on the
  -- rotated tangent, then convert that tangent into the radial vector before using the radius
  -- derivative of `circleMap`.
  have hradial :
      HasDerivAt (fun s : ℝ ↦ f (circleMap a s θ))
        (fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I))) r := by
    -- Compose the Fréchet derivative of `f` with the affine radius parametrization.
    simpa using
      (hf.hasFDerivAt.comp r
        (hasDerivAt_circleMap_radius a θ r).hasFDerivAt).hasDerivAt
  have hradial_deriv :
      deriv (fun s : ℝ ↦ f (circleMap a s θ)) r =
        fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := hradial.deriv
  calc
    (((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy)
        (circleMap a r θ) (deriv (circleMap a r) θ)) =
      fderiv ℝ f (circleMap a r θ)
        (Complex.mk (deriv (circleMap a r) θ).im (-(deriv (circleMap a r) θ).re)) := by
          rw [boundary_form_apply_eq_fderiv_rotated_tangent]
    _ = fderiv ℝ f (circleMap a r θ) (circleMap 0 r θ) := by
          rw [rotated_circle_tangent_eq_radial_vector]
    _ = fderiv ℝ f (circleMap a r θ) (r • Complex.exp (θ * Complex.I)) := by
          simp [circleMap, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = r * fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := by
          rw [ContinuousLinearMap.map_smul]
          simp [smul_eq_mul, mul_comm]
    _ = deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
          rw [hradial_deriv]
          ring

/-- Helper for Exercise 4: specialize the oriented-boundary Green-Riemann formula to the singleton
positive boundary circle of a closed disc before any concrete derivative rewrites. -/
lemma singleton_closedBall_green_riemann_formula_specialization {D : Set ℂ} (hD : IsOpen D)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall a r ⊆ D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    (∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, (P dx + Q dy) z) =
      ∫ z in Metric.closedBall a r, (dQdx z - dPdy z) := by
  classical
  -- Route correction: package the `Unit`-indexed oriented-boundary theorem once, then collapse the
  -- singleton boundary sum before introducing the concrete Fréchet-derivative data.
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (positive_circle_path a r).toClosedPath
  simpa [Γ] using
    (orientedBoundary_green_riemann_formula (Γ := Γ)
      (hΓ := closedBallBoundary_isOrientedBoundaryOf hr) (hKD := hclosed) (hD := hD)
      (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
      hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx)

/-- Helper for Exercise 4: Green-Riemann on the singleton positively oriented boundary of a closed
disc is first packaged on the raw closed-path integral surface. -/
lemma singleton_closedBall_green_riemann_formula {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hclosed : Metric.closedBall a r ⊆ D) :
    (∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath,
        ((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy) z) =
      ∫ z in Metric.closedBall a r,
        (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
  have hP_cont :
      ContinuousOn (fun w : ℂ ↦ -fderiv ℝ f w Complex.I) D := by
    -- Evaluate the continuous derivative field on the fixed vertical basis vector, then negate.
    simpa using
      (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).clm_apply
        continuousOn_const |>.neg
  have hQ_cont :
      ContinuousOn (fun w : ℂ ↦ fderiv ℝ f w 1) D := by
    -- Evaluate the continuous derivative field on the fixed horizontal basis vector.
    simpa using
      (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).clm_apply
        continuousOn_const
  have hiter_cont : ContinuousOn (iteratedFDeriv ℝ 2 f) D :=
    ContinuousOn.continuousOn_iteratedFDeriv (k := 2) hf hD le_rfl
  have hdQdx_cont :
      ContinuousOn (fun z : ℂ ↦ iteratedFDeriv ℝ 2 f z ![1, 1]) D := by
    -- The second derivative field is continuous, and evaluation on a fixed pair is continuous.
    intro z hz
    change ContinuousWithinAt
      ((fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ ℂ) ℝ => A ![1, 1]) ∘
        iteratedFDeriv ℝ 2 f) D z
    exact (continuous_eval_const (![1, 1] : Fin 2 → ℂ)).continuousAt.comp_continuousWithinAt
      (hiter_cont z hz)
  have hdPdy_cont :
      ContinuousOn (fun z : ℂ ↦ -(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) D := by
    -- The vertical second partial inherits continuity from the same iterated derivative field.
    have hII_cont :
        ContinuousOn (fun z : ℂ ↦ iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]) D := by
      intro z hz
      change ContinuousWithinAt
        ((fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ ℂ) ℝ =>
            A ![Complex.I, Complex.I]) ∘
          iteratedFDeriv ℝ 2 f) D z
      exact ContinuousAt.comp_continuousWithinAt
        ((continuous_eval_const (![Complex.I, Complex.I] : Fin 2 → ℂ)).continuousAt)
        (hiter_cont z hz)
    simpa using hII_cont.neg
  have hP_dy :
      ∀ z ∈ D,
        HasDerivAt (fun y : ℝ ↦ (-fderiv ℝ f (Complex.mk z.re y) Complex.I))
          (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) z.im := by
    intro z hz
    -- Differentiate the vertical derivative slice, then negate the resulting scalar function.
    simpa using
      (hasDerivAt_fderiv_apply_const_along_vertical hD hf (z := z) (v := Complex.I) hz).neg
  have hQ_dx :
      ∀ z ∈ D,
        HasDerivAt (fun x : ℝ ↦ fderiv ℝ f (Complex.mk x z.im) 1)
          (iteratedFDeriv ℝ 2 f z ![1, 1]) z.re := by
    intro z hz
    -- Differentiate the horizontal derivative slice in the fixed horizontal direction.
    simpa using
      (hasDerivAt_fderiv_apply_const_along_horizontal hD hf (z := z) (v := (1 : ℂ)) hz)
  -- Route correction: feed the current `ContDiffOn` continuity/derivative data into the already
  -- stable singleton-boundary Green wrapper instead of unfolding the disc integral again.
  simpa using
    singleton_closedBall_green_riemann_formula_specialization (hD := hD) (a := a) (r := r)
      hr hclosed hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx

/-- Helper for Exercise 4: on the open disc domain used in Green-Riemann, the Green area
integrand is exactly the within-Laplacian. -/
lemma green_disc_integrand_eq_laplacianWithin {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z : ℂ} (hz : z ∈ D) :
    (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) =
      (Δ[D] f) z := by
  -- On an open set, the within-Laplacian is the ordinary Laplacian, whose complex-plane formula
  -- is the sum of the horizontal and vertical second partials.
  have hΔ :
      (Δ[D] f) z =
        (iteratedFDeriv ℝ 2 f z ![1, 1]) + (iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]) := by
    rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane f hD.uniqueDiffOn hz,
      iteratedFDerivWithin_eq_iteratedFDeriv hD.uniqueDiffOn (hf.contDiffAt (hD.mem_nhds hz)) hz]
  calc
    (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) =
        (iteratedFDeriv ℝ 2 f z ![1, 1]) + (iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]) := by
          ring
    _ = (Δ[D] f) z := hΔ.symm

/-- Helper for Exercise 4: differentiating the radial slice `s ↦ f (circleMap a s θ)` is the
Fréchet derivative of `f` applied to the fixed unit direction `exp (θ I)`. -/
lemma deriv_circleMap_comp_eq_fderiv_exp {f : ℂ → ℝ} {a : ℂ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (circleMap a r θ)) :
    deriv (fun s : ℝ ↦ f (circleMap a s θ)) r =
      fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := by
  -- Compose the derivative of `f` with the affine radius parameterization of the circle.
  simpa using
    (hf.hasFDerivAt.comp r (hasDerivAt_circleMap_radius a θ r).hasFDerivAt).hasDerivAt.deriv
