import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file lives in the complex-analysis/Laplacian part of the chapter. The
-- source-facing holomorphic owner is `DifferentiableOn ℂ`; the primitive data are the open set,
-- the map, and the point in the domain. The raw operator `Complex.normSq` is only a bridge/view,
-- since mathlib exposes the textbook pointwise surface through `Complex.normSq_eq_norm_sq`, and
-- nearby section files already use `‖f z‖ ^ 2` for the same quantity.

open Laplacian
open InnerProductSpace
open Topology
open scoped InnerProductSpace

variable {D : Set ℂ} {f : ℂ → ℂ} {z : ℂ}

/-- Helper for Exercise 1: the real Fréchet derivative of a holomorphic function on the basis
`{1, I}` is determined by the complex derivative. -/
lemma holomorphic_fderiv_apply_one_I {f : ℂ → ℂ} {z : ℂ}
    (h : DifferentiableAt ℂ f z) :
    fderiv ℝ f z 1 = deriv f z ∧ fderiv ℝ f z Complex.I = Complex.I * deriv f z := by
  constructor
  · -- Apply the real-linear derivative identity at the basis vector `1`.
    simpa using
      congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) h.hasDerivAt.complexToReal_fderiv.fderiv
  · -- Apply the same identity at `I`, where real scalar multiplication becomes complex
    -- multiplication by `I`.
    have hI :=
      congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) h.hasDerivAt.complexToReal_fderiv.fderiv
    simpa [ContinuousLinearMap.smul_apply, mul_comm] using hI

/-- Helper for Exercise 1: differentiating the square of a real-valued function gives the usual
`2 g dg` formula when evaluated on a direction. -/
lemma fderiv_sq_apply {g : ℂ → ℝ} {z v : ℂ} (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun w ↦ g w ^ 2) z v = 2 * g z * fderiv ℝ g z v := by
  -- Rewrite `g^2` as a product so the scalar product rule applies directly.
  rw [show (fun w ↦ g w ^ 2) = g * g by
    ext w
    rw [Pi.mul_apply, sq]]
  rw [fderiv_mul hg hg]
  rw [ContinuousLinearMap.add_apply]
  simp [ContinuousLinearMap.smul_apply]
  ring

/-- Helper for Exercise 1: the second directional derivative of a square splits into the positive
gradient term and the base-value times the second derivative. -/
lemma iteratedFDeriv_two_sq_apply {g : ℂ → ℝ} {z v : ℂ} (hg : ContDiffAt ℝ 2 g z) :
    iteratedFDeriv ℝ 2 (fun w ↦ g w ^ 2) z ![v, v] =
      2 * (fderiv ℝ g z v) ^ 2 + 2 * g z * iteratedFDeriv ℝ 2 g z ![v, v] := by
  -- Differentiate the first-derivative square identity on a neighborhood of `z`.
  have hsq :
      (fun w ↦ fderiv ℝ (fun y ↦ g y ^ 2) w v) =ᶠ[𝓝 z] fun w ↦ 2 * g w * fderiv ℝ g w v := by
    filter_upwards [hg.eventually (by simp)] with w hw
    exact fderiv_sq_apply (z := w) (v := v) (hw.differentiableAt (by norm_num))
  have hg₁ : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hsq_cont : ContDiffAt ℝ 2 (fun w ↦ g w ^ 2) z := by
    simpa [sq] using hg.mul hg
  have hsqd : DifferentiableAt ℝ (fderiv ℝ (fun w ↦ g w ^ 2)) z :=
    hsq_cont.fderiv_right_succ.differentiableAt one_ne_zero
  have hgd : DifferentiableAt ℝ (fun w ↦ fderiv ℝ g w v) z := by
    exact (((hg.fderiv_right_succ).clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ ↦ v) z)).differentiableAt one_ne_zero)
  have hsecond :
      fderiv ℝ (fun w ↦ fderiv ℝ g w v) z v = iteratedFDeriv ℝ 2 g z ![v, v] := by
    -- Bundle the derivative map until the final evaluation at the fixed direction `v`.
    rw [fderiv_clm_apply (hg.fderiv_right_succ.differentiableAt one_ne_zero)
      (differentiableAt_const v)]
    simpa [iteratedFDeriv_two_apply]
  calc
    iteratedFDeriv ℝ 2 (fun w ↦ g w ^ 2) z ![v, v]
      = fderiv ℝ (fun w ↦ fderiv ℝ (fun y ↦ g y ^ 2) w v) z v := by
          rw [fderiv_clm_apply hsqd (differentiableAt_const v)]
          simpa [iteratedFDeriv_two_apply]
    _ = fderiv ℝ (fun w ↦ 2 * g w * fderiv ℝ g w v) z v := by
          rw [Filter.EventuallyEq.fderiv_eq hsq]
  -- Now differentiate the product `w ↦ (2 * g w) * dg(w, v)` explicitly.
  have hmul :=
    congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
      (fderiv_mul (c := ((2 : ℝ) • g)) (d := fun w ↦ fderiv ℝ g w v) (x := z)
        (hg₁.const_smul (2 : ℝ)) hgd)
  rw [show (fun w ↦ 2 * g w * fderiv ℝ g w v) = ((2 : ℝ) • g) * fun w ↦ fderiv ℝ g w v by
    funext w
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]]
  rw [show fderiv ℝ (((2 : ℝ) • g) * fun w ↦ fderiv ℝ g w v) z v =
      ((((2 : ℝ) • g z) • fderiv ℝ (fun w ↦ fderiv ℝ g w v) z) +
        (fderiv ℝ g z v • fderiv ℝ (((2 : ℝ) • g)) z)) v by
      simpa [ContinuousLinearMap.add_apply] using hmul]
  have hfirst :
      fderiv ℝ (((2 : ℝ) • g)) z v = 2 * fderiv ℝ g z v := by
    rw [fderiv_const_smul hg₁]
    simp [ContinuousLinearMap.smul_apply, two_mul]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hfirst, hsecond]
  ring

/-- Helper for Exercise 1: the directional derivative of the reciprocal is the usual
`-(dg)/g^2`. -/
lemma fderiv_inv_comp_apply {g : ℂ → ℝ} {z v : ℂ}
    (hg : DifferentiableAt ℝ g z) (hz : g z ≠ 0) :
    fderiv ℝ (fun w ↦ (g w)⁻¹) z v = -fderiv ℝ g z v / (g z) ^ 2 := by
  -- View the reciprocal as a composition with the scalar inverse map.
  rw [show (fun w ↦ (g w)⁻¹) = (fun x : ℝ ↦ x⁻¹) ∘ g by rfl]
  rw [fderiv_comp z (differentiableAt_inv hz) hg]
  simp [fderiv_inv, ContinuousLinearMap.comp_apply, div_eq_mul_inv, pow_two, mul_comm]

/-- Helper for Exercise 1: differentiating `log ∘ g` in a fixed direction gives `dg/g`. -/
lemma fderiv_log_apply {g : ℂ → ℝ} {z v : ℂ}
    (hg : DifferentiableAt ℝ g z) (hz : 0 < g z) :
    fderiv ℝ (fun w ↦ Real.log (g w)) z v = fderiv ℝ g z v / g z := by
  rw [fderiv.log hg hz.ne']
  simp [ContinuousLinearMap.smul_apply, div_eq_mul_inv, mul_comm]

/-- Helper for Exercise 1: the second directional derivative of `log ∘ g` is
`g''/g - (dg)^2/g^2`. -/
lemma iteratedFDeriv_two_log_apply {g : ℂ → ℝ} {z v : ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hz : 0 < g z) :
    iteratedFDeriv ℝ 2 (fun w ↦ Real.log (g w)) z ![v, v] =
      iteratedFDeriv ℝ 2 g z ![v, v] / g z - (fderiv ℝ g z v) ^ 2 / (g z) ^ 2 := by
  -- Differentiate the logarithmic first-derivative identity on a positive neighborhood.
  have hpos : {w : ℂ | 0 < g w} ∈ 𝓝 z := by
    exact hg.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hz)
  have hlog :
      (fun w ↦ fderiv ℝ (fun y ↦ Real.log (g y)) w v) =ᶠ[𝓝 z]
        (fun w ↦ fderiv ℝ g w v / g w) := by
    filter_upwards [hg.eventually (by simp), hpos] with w hw hwpos
    exact fderiv_log_apply (z := w) (v := v) (hw.differentiableAt (by norm_num)) hwpos
  have hg₁ : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hlog_cont : ContDiffAt ℝ 2 (fun w ↦ Real.log (g w)) z := by
    exact ((analyticAt_log hz).contDiffAt : ContDiffAt ℝ 2 Real.log (g z)).comp z hg
  have hlogd : DifferentiableAt ℝ (fderiv ℝ (fun w ↦ Real.log (g w))) z :=
    hlog_cont.fderiv_right_succ.differentiableAt one_ne_zero
  have hgd : DifferentiableAt ℝ (fun w ↦ fderiv ℝ g w v) z := by
    exact (((hg.fderiv_right_succ).clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ ↦ v) z)).differentiableAt one_ne_zero)
  have hginv : DifferentiableAt ℝ (fun w ↦ (g w)⁻¹) z :=
    (differentiableAt_inv hz.ne').comp z hg₁
  have hsecond :
      fderiv ℝ (fun w ↦ fderiv ℝ g w v) z v = iteratedFDeriv ℝ 2 g z ![v, v] := by
    -- Bundle the derivative map until the final evaluation at `v`.
    rw [fderiv_clm_apply (hg.fderiv_right_succ.differentiableAt one_ne_zero)
      (differentiableAt_const v)]
    simpa [iteratedFDeriv_two_apply]
  calc
    iteratedFDeriv ℝ 2 (fun w ↦ Real.log (g w)) z ![v, v]
      = fderiv ℝ (fun w ↦ fderiv ℝ (fun y ↦ Real.log (g y)) w v) z v := by
          rw [fderiv_clm_apply hlogd (differentiableAt_const v)]
          simpa [iteratedFDeriv_two_apply]
    _ = fderiv ℝ (fun w ↦ fderiv ℝ g w v / g w) z v := by
          rw [Filter.EventuallyEq.fderiv_eq hlog]
  -- Rewrite the quotient as a product with the inverse and differentiate the factors.
  rw [show (fun w ↦ fderiv ℝ g w v / g w) =
      (fun w ↦ fderiv ℝ g w v * (g w)⁻¹) by
      funext w
      rw [div_eq_mul_inv]]
  have hmul :=
    congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
      (fderiv_mul (c := fun w ↦ fderiv ℝ g w v) (d := fun w ↦ (g w)⁻¹) (x := z) hgd hginv)
  have hmul' :
      fderiv ℝ (fun w ↦ fderiv ℝ g w v * (g w)⁻¹) z v =
        (((fderiv ℝ g z v) • fderiv ℝ (fun w ↦ (g w)⁻¹) z) +
          ((g z)⁻¹ • fderiv ℝ (fun w ↦ fderiv ℝ g w v) z)) v := by
    simpa [Pi.mul_apply, ContinuousLinearMap.add_apply] using hmul
  rw [hmul']
  have hInv :
      fderiv ℝ (fun w ↦ (g w)⁻¹) z v = -fderiv ℝ g z v / (g z) ^ 2 :=
    fderiv_inv_comp_apply (z := z) (v := v) hg₁ hz.ne'
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hsecond, hInv]
  ring

/-- Helper for Exercise 1: the Laplacian of the square of a harmonic real-valued function equals
twice the sum of the squared basis derivatives. -/
lemma laplacian_sq_of_harmonicAt {g : ℂ → ℝ} (hg : HarmonicAt g z) :
    Δ (fun w ↦ g w ^ 2) z =
      2 * ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) := by
  -- Route correction: keep the second-derivative bookkeeping at Laplacian level and only use
  -- harmonicity to eliminate the `g * Δg` contribution at the end.
  have hΔg : iteratedFDeriv ℝ 2 g z ![1, 1] + iteratedFDeriv ℝ 2 g z ![Complex.I, Complex.I] = 0 := by
    simpa [laplacian_eq_iteratedFDeriv_complexPlane] using hg.2.eq_of_nhds
  calc
    Δ (fun w ↦ g w ^ 2) z
      = iteratedFDeriv ℝ 2 (fun w ↦ g w ^ 2) z ![1, 1] +
          iteratedFDeriv ℝ 2 (fun w ↦ g w ^ 2) z ![Complex.I, Complex.I] := by
            simpa [laplacian_eq_iteratedFDeriv_complexPlane]
    _ = 2 * (fderiv ℝ g z 1) ^ 2 + 2 * g z * iteratedFDeriv ℝ 2 g z ![1, 1] +
          (2 * (fderiv ℝ g z Complex.I) ^ 2 +
            2 * g z * iteratedFDeriv ℝ 2 g z ![Complex.I, Complex.I]) := by
            rw [iteratedFDeriv_two_sq_apply (z := z) (v := 1) hg.1,
              iteratedFDeriv_two_sq_apply (z := z) (v := Complex.I) hg.1]
  calc
    2 * (fderiv ℝ g z 1) ^ 2 + 2 * g z * iteratedFDeriv ℝ 2 g z ![1, 1] +
        (2 * (fderiv ℝ g z Complex.I) ^ 2 + 2 * g z * iteratedFDeriv ℝ 2 g z ![Complex.I, Complex.I])
        =
          2 * ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) +
            2 * g z *
              (iteratedFDeriv ℝ 2 g z ![1, 1] + iteratedFDeriv ℝ 2 g z ![Complex.I, Complex.I]) := by
        ring
    _ = 2 * ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) := by
        rw [hΔg]
        ring

/-- Helper for Exercise 1: the Laplacian of `Real.log ∘ g` splits into the Laplacian term of `g`
and the negative squared-gradient correction. -/
lemma laplacian_log_of_pos {g : ℂ → ℝ} (hg : ContDiffAt ℝ 2 g z) (hz : 0 < g z) :
    Δ (fun w ↦ Real.log (g w)) z =
      Δ g z / g z - ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) / (g z) ^ 2 := by
  -- Route correction: differentiate the bundled first-derivative identity for `Real.log ∘ g`
  -- and only evaluate in the basis directions after the second derivative is assembled.
  calc
    Δ (fun w ↦ Real.log (g w)) z
      = iteratedFDeriv ℝ 2 (fun w ↦ Real.log (g w)) z ![1, 1] +
          iteratedFDeriv ℝ 2 (fun w ↦ Real.log (g w)) z ![Complex.I, Complex.I] := by
            simpa [laplacian_eq_iteratedFDeriv_complexPlane]
    _ = (iteratedFDeriv ℝ 2 g z ![1, 1] / g z - (fderiv ℝ g z 1) ^ 2 / (g z) ^ 2) +
          (iteratedFDeriv ℝ 2 g z ![Complex.I, Complex.I] / g z -
            (fderiv ℝ g z Complex.I) ^ 2 / (g z) ^ 2) := by
            rw [iteratedFDeriv_two_log_apply (z := z) (v := 1) hg hz,
              iteratedFDeriv_two_log_apply (z := z) (v := Complex.I) hg hz]
    _ = Δ g z / g z - ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) / (g z) ^ 2 := by
            simp [laplacian_eq_iteratedFDeriv_complexPlane]
            ring

/-- Helper for Exercise 1: for a holomorphic function, the real derivatives on the basis
directions have total squared norm `2 ‖f'‖²`. -/
lemma norm_sq_fderiv_basis_sum_of_holomorphic {f : ℂ → ℂ} {z : ℂ}
    (h : DifferentiableAt ℂ f z) :
    ‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2 = 2 * ‖deriv f z‖ ^ 2 := by
  -- Reduce both directional values to the complex derivative.
  rcases holomorphic_fderiv_apply_one_I h with ⟨h1, hI⟩
  rw [h1, hI]
  simp [Complex.norm_I]
  ring

/-- Helper for Exercise 1: the real and imaginary parts of the real Fréchet derivative are the
Fréchet derivatives of the real and imaginary parts. -/
lemma fderiv_re_im_apply {f : ℂ → ℂ} {z v : ℂ} (h : DifferentiableAt ℂ f z) :
    fderiv ℝ (fun w ↦ (f w).re) z v = (fderiv ℝ f z v).re ∧
      fderiv ℝ (fun w ↦ (f w).im) z v = (fderiv ℝ f z v).im := by
  -- Apply the real and imaginary continuous linear maps to the real derivative of `f`.
  have hR : DifferentiableAt ℝ f z := h.restrictScalars ℝ
  constructor
  · rw [show (fun w ↦ (f w).re) = fun w ↦ Complex.reCLM (f w) by rfl]
    rw [fderiv_clm_apply (differentiableAt_const Complex.reCLM) hR]
    simp
  · rw [show (fun w ↦ (f w).im) = fun w ↦ Complex.imCLM (f w) by rfl]
    rw [fderiv_clm_apply (differentiableAt_const Complex.imCLM) hR]
    simp

/-- Helper for Exercise 1: the squared gradient of `w ↦ ‖f w‖²` on the basis `{1, I}` collapses
to `4 ‖f z‖² ‖f'(z)‖²`. -/
lemma normSq_gradient_basis_sum_of_holomorphic {f : ℂ → ℂ} {z : ℂ}
    (h : DifferentiableAt ℂ f z) :
    (fderiv ℝ (fun w ↦ ‖f w‖ ^ 2) z 1) ^ 2 + (fderiv ℝ (fun w ↦ ‖f w‖ ^ 2) z Complex.I) ^ 2 =
      4 * ‖f z‖ ^ 2 * ‖deriv f z‖ ^ 2 := by
  -- Differentiate the real/imaginary square decomposition of `‖f‖²`.
  rcases holomorphic_fderiv_apply_one_I h with ⟨h1, hI⟩
  have hR : DifferentiableAt ℝ f z := h.restrictScalars ℝ
  have hRe : DifferentiableAt ℝ (fun w ↦ (f w).re) z := by
    exact (differentiableAt_const Complex.reCLM).clm_apply hR
  have hIm : DifferentiableAt ℝ (fun w ↦ (f w).im) z := by
    exact (differentiableAt_const Complex.imCLM).clm_apply hR
  have hNorm (v : ℂ) :
      fderiv ℝ (fun w ↦ ‖f w‖ ^ 2) z v =
        2 * ((f z).re * fderiv ℝ (fun w ↦ (f w).re) z v +
          (f z).im * fderiv ℝ (fun w ↦ (f w).im) z v) := by
    have hnorm :
        (fun w ↦ ‖f w‖ ^ 2) = (fun w ↦ (f w).re ^ 2) + fun w ↦ (f w).im ^ 2 := by
      funext w
      simp [Pi.add_apply]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [hnorm, fderiv_add (by simpa [sq] using hRe.mul hRe) (by simpa [sq] using hIm.mul hIm)]
    rw [ContinuousLinearMap.add_apply, fderiv_sq_apply (z := z) (v := v) hRe,
      fderiv_sq_apply (z := z) (v := v) hIm]
    ring
  have hRe1 := (fderiv_re_im_apply (z := z) (v := 1) h).1
  have hIm1 := (fderiv_re_im_apply (z := z) (v := 1) h).2
  have hReI := (fderiv_re_im_apply (z := z) (v := Complex.I) h).1
  have hImI := (fderiv_re_im_apply (z := z) (v := Complex.I) h).2
  rw [hNorm 1, hNorm Complex.I, hRe1, hIm1, hReI, hImI, h1, hI]
  simp [Complex.mul_re, Complex.mul_im, RCLike.norm_sq_eq_def]
  ring

/-- Helper for Exercise 1: the real and imaginary basis derivatives recover the squared norm of the
real Fréchet derivative. -/
lemma re_im_fderiv_sq_sum {f : ℂ → ℂ} {z v : ℂ} (h : DifferentiableAt ℂ f z) :
    (fderiv ℝ (fun w ↦ (f w).re) z v) ^ 2 + (fderiv ℝ (fun w ↦ (f w).im) z v) ^ 2 =
      ‖fderiv ℝ f z v‖ ^ 2 := by
  -- Rewrite both sides in terms of the real and imaginary parts of `fderiv`.
  rw [(fderiv_re_im_apply (z := z) (v := v) h).1, (fderiv_re_im_apply (z := z) (v := v) h).2]
  simp [RCLike.norm_sq_eq_def]
  ring

/-- Exercise 1 (1): if `f` is holomorphic on the open set `D`, then at every `z ∈ D` the
Laplacian of the squared modulus `|f|^2`, written pointwise as `w ↦ ‖f w‖ ^ 2`, is
`4 |f'(z)|^2`. -/
theorem laplacian_normSq_of_holomorphicOn (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hz : z ∈ D) :
    Δ (fun w ↦ ‖f w‖ ^ 2) z = 4 * ‖deriv f z‖ ^ 2 := by
  -- Route correction: decompose `‖f‖²` into squares of the harmonic real and imaginary parts.
  have hA : AnalyticAt ℂ f z := hf.analyticOnNhd hD z hz
  have hdiff : DifferentiableAt ℂ f z := hA.differentiableAt
  have hre := hA.harmonicAt_re
  have him := hA.harmonicAt_im
  have hre_sq : ContDiffAt ℝ 2 (fun w ↦ (f w).re ^ 2) z := by
    simpa [sq] using hre.1.mul hre.1
  have him_sq : ContDiffAt ℝ 2 (fun w ↦ (f w).im ^ 2) z := by
    simpa [sq] using him.1.mul him.1
  have hnorm :
      (fun w ↦ ‖f w‖ ^ 2) = (fun w ↦ (f w).re ^ 2) + fun w ↦ (f w).im ^ 2 := by
    funext w
    simp [Pi.add_apply]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hnorm]
  have hLap :
      Δ ((fun w ↦ (f w).re ^ 2) + fun w ↦ (f w).im ^ 2) z =
        Δ (fun w ↦ (f w).re ^ 2) z + Δ (fun w ↦ (f w).im ^ 2) z := by
    simpa using hre_sq.laplacian_add him_sq
  rw [hLap]
  rw [laplacian_sq_of_harmonicAt (z := z) hre, laplacian_sq_of_harmonicAt (z := z) him]
  calc
    2 * ((fderiv ℝ (fun z ↦ (f z).re) z 1) ^ 2 + (fderiv ℝ (fun z ↦ (f z).re) z Complex.I) ^ 2) +
        2 * ((fderiv ℝ (fun z ↦ (f z).im) z 1) ^ 2 + (fderiv ℝ (fun z ↦ (f z).im) z Complex.I) ^ 2)
        =
          2 * (((fderiv ℝ (fun z ↦ (f z).re) z 1) ^ 2 + (fderiv ℝ (fun z ↦ (f z).im) z 1) ^ 2) +
            ((fderiv ℝ (fun z ↦ (f z).re) z Complex.I) ^ 2 +
              (fderiv ℝ (fun z ↦ (f z).im) z Complex.I) ^ 2)) := by
            ring
    _ = 2 * (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) := by
          rw [re_im_fderiv_sq_sum (z := z) (v := 1) hdiff,
            re_im_fderiv_sq_sum (z := z) (v := Complex.I) hdiff]
  rw [norm_sq_fderiv_basis_sum_of_holomorphic hdiff]
  ring

/-- Exercise 1 (2): if `f` is holomorphic on the open set `D`, then at every `z ∈ D` the
Laplacian of `log (1 + |f|^2)`, written as `Real.log (1 + ‖f z‖ ^ 2)`, is
`4 |f'(z)|^2 / (1 + |f(z)|^2)^2`. -/
theorem laplacian_log_one_add_normSq_of_holomorphicOn (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) (hz : z ∈ D) :
    Δ (fun w : ℂ ↦ Real.log (1 + ‖f w‖ ^ 2)) z =
      4 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2 := by
  -- Route correction: apply the Laplacian-level logarithm identity to `g = 1 + ‖f‖²`.
  set g : ℂ → ℝ := fun w ↦ 1 + ‖f w‖ ^ 2
  have hA : AnalyticAt ℂ f z := hf.analyticOnNhd hD z hz
  have hdiff : DifferentiableAt ℂ f z := hA.differentiableAt
  have hre := hA.harmonicAt_re
  have him := hA.harmonicAt_im
  have hre_sq : ContDiffAt ℝ 2 (fun w ↦ (f w).re ^ 2) z := by
    simpa [sq] using hre.1.mul hre.1
  have him_sq : ContDiffAt ℝ 2 (fun w ↦ (f w).im ^ 2) z := by
    simpa [sq] using him.1.mul him.1
  have hnorm :
      (fun w ↦ ‖f w‖ ^ 2) = (fun w ↦ (f w).re ^ 2) + fun w ↦ (f w).im ^ 2 := by
    funext w
    simp [Pi.add_apply]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hcontNorm : ContDiffAt ℝ 2 (fun w ↦ ‖f w‖ ^ 2) z := by
    rw [hnorm]
    exact hre_sq.add him_sq
  have hcontg : ContDiffAt ℝ 2 g z := by
    simpa [g, Pi.add_apply] using (contDiffAt_const.add hcontNorm)
  have hpos : 0 < g z := by
    positivity
  have hLog :
      Δ (fun w : ℂ ↦ Real.log (g w)) z =
        Δ g z / g z - ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) / (g z) ^ 2 := by
    simpa using laplacian_log_of_pos (z := z) (g := g) hcontg hpos
  rw [hLog]
  have hΔg :
      Δ g z = Δ (fun w ↦ ‖f w‖ ^ 2) z := by
    simpa [g, Pi.add_apply] using (contDiffAt_const.laplacian_add hcontNorm)
  have hgrad1 :
      fderiv ℝ g z 1 = fderiv ℝ (fun w ↦ ‖f w‖ ^ 2) z 1 := by
    simpa [Pi.add_apply] using
      congrArg (fun L : ℂ →L[ℝ] ℝ => L 1)
        (fderiv_add (differentiableAt_const (1 : ℝ)) (hcontNorm.differentiableAt (by norm_num)))
  have hgradI :
      fderiv ℝ g z Complex.I = fderiv ℝ (fun w ↦ ‖f w‖ ^ 2) z Complex.I := by
    simpa [Pi.add_apply] using
      congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I)
        (fderiv_add (differentiableAt_const (1 : ℝ)) (hcontNorm.differentiableAt (by norm_num)))
  rw [hΔg, hgrad1, hgradI, laplacian_normSq_of_holomorphicOn hD hf hz,
    normSq_gradient_basis_sum_of_holomorphic hdiff]
  change 4 * ‖deriv f z‖ ^ 2 / g z - (4 * ‖f z‖ ^ 2 * ‖deriv f z‖ ^ 2) / (g z) ^ 2 =
    4 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2
  have hone : g z ≠ 0 := by positivity
  field_simp [hone]
  ring
