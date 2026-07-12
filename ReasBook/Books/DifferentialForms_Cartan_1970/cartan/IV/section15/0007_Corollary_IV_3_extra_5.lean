import Mathlib.Analysis.Complex.Harmonic.Analytic
import DifferentialForms_Cartan_1970.II.section05.«0023_Theorem_3»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Complex InnerProductSpace Set

-- Domain sampling: this corollary is `source-facing`, while the global existence owner is the
-- chapter theorem `hasPrimitiveOn_of_isOpen_of_isSimplyConnected_of_isClosedOn`. The primitive
-- data is the closed one-form attached to the harmonic complex partial; the holomorphic potential
-- and the real-part comparison are derived from that owner together with
-- `HasPrimitiveOn.isExactOn` and `IsOpen.exists_eq_add_of_fderiv_eq`.

/-- Helper for Corollary IV.3-extra-5: taking the real part of the scalar form attached to the
harmonic complex partial recovers the real Fréchet derivative of `g`. -/
lemma re_comp_realScalarOneForm_complex_partial_eq_fderiv {g : ℂ → ℝ} (z : ℂ) :
    Complex.reCLM.comp
        (Complex.realScalarOneForm (fun w ↦ fderiv ℝ g w 1 - I * fderiv ℝ g w I) z) =
      fderiv ℝ g z := by
  -- Decompose a tangent vector in the real basis `1, I` and compare both sides on that basis.
  ext v
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    apply Complex.ext <;> simp
  calc
    (Complex.reCLM.comp
          (Complex.realScalarOneForm (fun w ↦ fderiv ℝ g w 1 - I * fderiv ℝ g w I) z)) v
        =
          (Complex.reCLM.comp
            (Complex.realScalarOneForm
              (fun w ↦ fderiv ℝ g w 1 - I * fderiv ℝ g w I) z))
            (v.re • (1 : ℂ) + v.im • I) := by
      exact congrArg
        (Complex.reCLM.comp
          (Complex.realScalarOneForm (fun w ↦ fderiv ℝ g w 1 - I * fderiv ℝ g w I) z)) hv
    _ =
          v.re • (fderiv ℝ g z) 1 + v.im • (fderiv ℝ g z) I := by
      rw [map_add, map_smul, map_smul]
      simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
    _ = (fderiv ℝ g z) (v.re • (1 : ℂ) + v.im • I) := by
      rw [map_add, map_smul, map_smul]
    _ = (fderiv ℝ g z) v := by
      exact congrArg (fderiv ℝ g z) hv.symm

/-- Corollary IV.3-extra-5. If `D` is a simply connected open set, any real harmonic function on
`D` is the real part of a holomorphic function on `D`. -/
theorem harmonicOnNhd_exists_analyticOnNhd_re_eq_of_isSimplyConnected {D : Set ℂ}
    (hD_open : IsOpen D) (hD_sc : IsSimplyConnected D) {g : ℂ → ℝ}
    (hg : HarmonicOnNhd g D) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f D ∧ D.EqOn (fun z ↦ (f z).re) g := by
  let ω : ℂ → ℂ := fun z ↦ fderiv ℝ g z 1 - I * fderiv ℝ g z I
  -- The source proof controls the harmonic complex partial, which is holomorphic on `D`.
  have hω_diff : DifferentiableOn ℂ ω D := by
    intro z hz
    exact (HarmonicAt.differentiableAt_complex_partial (hg z hz)).differentiableWithinAt
  have hω_cont : ContinuousOn (Complex.realScalarOneForm ω) D := by
    -- The scalar one-form is just the complex partial times the identity form `dz`.
    have hone : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) D := continuousOn_const
    have hform :
        Complex.realScalarOneForm ω = fun z ↦ ω z • (1 : ℂ →L[ℝ] ℂ) := by
      funext z
      exact Complex.realScalarOneForm_eq_smul ω z
    rw [hform]
    exact hω_diff.continuousOn.smul hone
  have hω_closed : IsClosedOn (Complex.realScalarOneForm ω) D := by
    -- Local holomorphic primitives of the complex partial provide local primitives of the form.
    intro z hz
    rcases holomorphic_has_local_primitive hD_open hω_diff hz with ⟨r, hr, hball, hExact⟩
    refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
    simpa [Complex.realScalarOneForm] using hExact.hasPrimitiveOn
  have hprimitive : HasPrimitiveOn D (Complex.realScalarOneForm ω) :=
    hasPrimitiveOn_of_isOpen_of_isSimplyConnected_of_isClosedOn
      hD_open hD_sc hω_cont hω_closed
  have hω_exact : Complex.IsExactOn ω D := hprimitive.isExactOn
  rcases hω_exact with ⟨F, hF⟩
  have hF_realPrimitive : IsPrimitiveOn D (Complex.realScalarOneForm ω) F := by
    -- Passing from complex to real Fréchet derivatives turns `F' = ω` into a primitive of
    -- the associated real-linear one-form.
    intro z hz
    simpa [Complex.realScalarOneForm_eq_smul] using (hF z hz).complexToReal_fderiv
  have hFre_primitive :
      IsPrimitiveOn D (fun z ↦ Complex.reCLM.comp (Complex.realScalarOneForm ω z))
        (fun z ↦ (F z).re) := by
    -- Composing the primitive with `Re` gives a primitive for the real part of the one-form.
    simpa [Function.comp] using hF_realPrimitive.comp Complex.reCLM
  have hg_primitive :
      IsPrimitiveOn D (fun z ↦ Complex.reCLM.comp (Complex.realScalarOneForm ω z)) g := by
    -- The harmonic function itself has the same real derivative field.
    intro z hz
    have hre : Complex.reCLM.comp (ω z • (1 : ℂ →L[ℝ] ℂ)) = fderiv ℝ g z := by
      simpa [ω, Complex.realScalarOneForm_eq_smul] using
        re_comp_realScalarOneForm_complex_partial_eq_fderiv (g := g) z
    simpa [Complex.realScalarOneForm_eq_smul, hre] using
      ((hg z hz).1.differentiableAt two_ne_zero).hasFDerivAt
  have hD_pre : IsPreconnected D := hD_sc.isPathConnected.isConnected.isPreconnected
  obtain ⟨c, hc⟩ :=
    IsPrimitiveOn.sub_eqOn_const_of_isOpen_isPreconnected hD_open hD_pre
      hFre_primitive hg_primitive
  have hshift_diff : DifferentiableOn ℂ (fun z ↦ F z - c) D := by
    -- Subtracting the real constant only normalizes the primitive; it preserves holomorphicity.
    intro z hz
    have hc_diff : DifferentiableAt ℂ (fun _ : ℂ ↦ (c : ℂ)) z := by
      exact differentiableAt_const (c := (c : ℂ))
    exact ((hF z hz).differentiableAt.sub hc_diff).differentiableWithinAt
  refine ⟨fun z ↦ F z - c, hshift_diff.analyticOnNhd hD_open, ?_⟩
  -- The constant from the primitive comparison is removed by shifting `F` by that real scalar.
  intro z hz
  have hzconst : (F z).re - g z = c := hc hz
  have hzre : (F z).re = g z + c := by
    simpa [add_comm] using sub_eq_iff_eq_add'.mp hzconst
  simp [hzre]
