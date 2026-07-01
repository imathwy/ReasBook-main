import Mathlib

open scoped ComplexConjugate
open Set

attribute [local instance] Complex.finrank_real_complex_fact

-- Semantic recall tool unavailable in this session; this statement is aligned with
-- `Mathlib.Analysis.Complex.Conformal` and `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic`.

-- Declarations for this item will be appended below by the statement pipeline.

variable {D : Set ℂ} {f : ℂ → ℂ}

/-- Helper for Proposition 1.2: a real-linear endomorphism of `ℂ` vanishes once it sends both
`1` and `I` to `0`. -/
lemma complex_continuousLinearMap_eq_zero_of_apply_one_eq_zero_apply_I_eq_zero
    {g : ℂ →L[ℝ] ℂ} (h1 : g 1 = 0) (hI : g Complex.I = 0) : g = 0 := by
  -- Expand a complex number in the real basis `{1, I}` and evaluate the map on each basis vector.
  ext z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa [smul_eq_mul] using (Complex.re_add_im z).symm
  rw [hz, map_add, map_smul, map_smul, h1, hI]
  simp

/-- Helper for Proposition 1.2: differentiating `f ∘ conj` at `conj z` postcomposes the real
derivative of `f` at `z` with complex conjugation. -/
lemma fderiv_comp_conj_at {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (f ∘ conj) (conj z) =
      (fderiv ℝ f z).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  -- The chain rule identifies the derivative of the precomposition by `conj`.
  have hconj : fderiv ℝ conj (conj z) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) :=
    Complex.conjCLE.fderiv
  have hf' : DifferentiableAt ℝ f (conj (conj z)) := by
    simpa using hf
  simpa [Function.comp_apply, hconj] using
    (fderiv_comp (f := conj) (g := f) (x := conj z) hf' Complex.conjCLE.differentiableAt)

/-- Helper for Proposition 1.2: differentiating `conj ∘ f` postcomposes the real derivative of
`f` with complex conjugation. -/
lemma fderiv_conj_comp_at {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (conj ∘ f) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) := by
  -- The chain rule identifies the derivative of the postcomposition by `conj`.
  have hconj : fderiv ℝ conj (f z) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) :=
    Complex.conjCLE.fderiv
  simpa [Complex.conjCLE_apply, Function.comp_apply, hconj] using
    (fderiv_comp (f := f) (g := conj) (x := z) Complex.conjCLE.differentiableAt hf)

/-- Helper for Proposition 1.2: multiplying both vectors by the same nonzero complex number
preserves the standard oriented angle. -/
lemma complex_orientation_oangle_mul (a : ℂ) (ha : a ≠ 0) (u v : ℂ) :
    Complex.orientation.oangle (a * u) (a * v) = Complex.orientation.oangle u v := by
  -- Rewrite the oriented angle as an argument and factor out the positive real `normSq a`.
  rw [Complex.oangle, Complex.oangle]
  have hnorm : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have hmul :
      conj (a * u) * (a * v) = (Complex.normSq a : ℂ) * (conj u * v) := by
    calc
      conj (a * u) * (a * v) = (conj a * conj u) * (a * v) := by simp
      _ = (conj a * a) * (conj u * v) := by ring
      _ = (Complex.normSq a : ℂ) * (conj u * v) := by
        rw [Complex.normSq_eq_conj_mul_self]
  rw [hmul, Complex.arg_real_mul _ hnorm]

/-- Helper for Proposition 1.2: complex conjugation reverses the standard oriented angle. -/
lemma complex_orientation_oangle_conj (u v : ℂ) :
    Complex.orientation.oangle (conj u) (conj v) = -Complex.orientation.oangle u v := by
  -- Conjugating the `Complex.arg` input negates the resulting oriented angle.
  rw [Complex.oangle, Complex.oangle]
  simpa [map_mul] using (Complex.arg_conj_coe_angle (conj u * v))

/-- The canonical antiholomorphic pointwise owner from
`Mathlib.Analysis.Complex.Conformal` is equivalent, on an open domain `D`, to holomorphicity of
`conj ∘ f` on `D`. -/
theorem differentiableOn_conj_comp_iff (hD_open : IsOpen D) :
    DifferentiableOn ℂ (conj ∘ f) D ↔ ∀ z ∈ D, DifferentiableAt ℂ (f ∘ conj) (conj z) := by
  constructor
  · intro hf_anti z hz
    -- On an open set, `DifferentiableOn` upgrades to pointwise differentiability.
    have hz_diff : DifferentiableAt ℂ (conj ∘ f) z :=
      hf_anti.differentiableAt (hD_open.mem_nhds hz)
    have hfun : conj ∘ (f ∘ conj) ∘ conj = conj ∘ f := by
      funext w
      simp [Function.comp_assoc]
    have hiff :
        DifferentiableAt ℂ (conj ∘ f) z ↔ DifferentiableAt ℂ (f ∘ conj) (conj z) := by
      simpa [hfun] using
        (differentiableAt_conj_conj_iff (f := f ∘ conj) (x := z))
    -- Conjugating source and target converts the canonical owner into the source-facing one.
    exact hiff.1 hz_diff
  · intro hf_anti z hz
    have hfun : conj ∘ (f ∘ conj) ∘ conj = conj ∘ f := by
      funext w
      simp [Function.comp_assoc]
    have hiff :
        DifferentiableAt ℂ (conj ∘ f) z ↔ DifferentiableAt ℂ (f ∘ conj) (conj z) := by
      simpa [hfun] using
        (differentiableAt_conj_conj_iff (f := f ∘ conj) (x := z))
    -- Convert the source-facing pointwise owner back to pointwise antiholomorphicity.
    have hz_diff : DifferentiableAt ℂ (conj ∘ f) z := hiff.2 (hf_anti z hz)
    exact hz_diff.differentiableWithinAt

/-- Helper for Proposition 1.2: a conformal differential on `ℂ` with nonvanishing Jacobian
satisfies either the Cauchy-Riemann equation or the anti-Cauchy-Riemann equation. -/
lemma conformalAt_cauchy_riemann_or_anticauchy_riemann {z : ℂ}
    (hf : ConformalAt f z) (hdet : (fderiv ℝ f z).det ≠ 0) :
    fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1 ∨
      fderiv ℝ f z Complex.I = -Complex.I • fderiv ℝ f z 1 := by
  -- Use the pointwise holomorphic/antiholomorphic dichotomy from Mathlib.
  rcases (conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj.mp hf).1 with
      hz_holo | hz_anti
  · left
    -- The holomorphic branch is exactly the Cauchy-Riemann equation.
    exact (differentiableAt_complex_iff_differentiableAt_real (f := f) (x := z)).1 hz_holo |>.2
  · right
    -- In the antiholomorphic branch, apply the Cauchy-Riemann equation to `f ∘ conj`.
    have hf_real : DifferentiableAt ℝ f z := hf.differentiableAt
    have hcomp := fderiv_comp_conj_at (f := f) hf_real
    have hcr_comp :
        fderiv ℝ (f ∘ conj) (conj z) Complex.I =
          Complex.I • fderiv ℝ (f ∘ conj) (conj z) 1 :=
      (differentiableAt_complex_iff_differentiableAt_real (f := f ∘ conj) (x := conj z)).1 hz_anti |>.2
    have hcr_comp' :
        -(fderiv ℝ f z Complex.I) = Complex.I • fderiv ℝ f z 1 := by
      simpa [hcomp, ContinuousLinearMap.comp_apply, map_neg] using hcr_comp
    -- Negating the identity turns the minus sign into the anti-Cauchy-Riemann equation.
    have hanti :
        fderiv ℝ f z Complex.I = -Complex.I • fderiv ℝ f z 1 := by
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg] using
        congrArg Neg.neg hcr_comp'
    exact hanti

/-- Helper for Proposition 1.2: a continuously differentiable real map on an open set is
holomorphic if its real differential satisfies the Cauchy-Riemann equation everywhere on that
set. -/
lemma holomorphic_on_of_cauchy_riemann_eq (hD_open : IsOpen D) (hf_c1 : ContDiffOn ℝ 1 f D)
    (hcr : EqOn (fun z ↦ fderiv ℝ f z Complex.I) (fun z ↦ Complex.I • fderiv ℝ f z 1) D) :
    DifferentiableOn ℂ f D := by
  intro z hz
  -- Openness upgrades the `C¹` hypothesis to pointwise real differentiability.
  have hf_real : DifferentiableAt ℝ f z :=
    (hf_c1.differentiableOn_one.differentiableAt (hD_open.mem_nhds hz))
  have hcr_z : fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1 := hcr hz
  -- The Cauchy-Riemann equation converts real differentiability into complex differentiability.
  have hz_holo : DifferentiableAt ℂ f z :=
    (differentiableAt_complex_iff_differentiableAt_real (f := f) (x := z)).2 ⟨hf_real, hcr_z⟩
  exact hz_holo.differentiableWithinAt

/-- Helper for Proposition 1.2: a continuously differentiable real map on an open set is
antiholomorphic when its real differential satisfies the anti-Cauchy-Riemann equation
everywhere on that set. -/
lemma antiholomorphic_on_of_anticauchy_riemann_eq (hD_open : IsOpen D)
    (hf_c1 : ContDiffOn ℝ 1 f D)
    (hcr : EqOn (fun z ↦ fderiv ℝ f z Complex.I) (fun z ↦ -Complex.I • fderiv ℝ f z 1) D) :
    DifferentiableOn ℂ (conj ∘ f) D := by
  -- It is enough to prove the source-facing holomorphicity of `f ∘ conj`.
  refine (differentiableOn_conj_comp_iff (D := D) (f := f) hD_open).2 ?_
  intro z hz
  -- Openness upgrades the `C¹` hypothesis to pointwise real differentiability.
  have hf_real : DifferentiableAt ℝ f z :=
    (hf_c1.differentiableOn_one.differentiableAt (hD_open.mem_nhds hz))
  have hcomp := fderiv_comp_conj_at (f := f) hf_real
  have hanti_z : fderiv ℝ f z Complex.I = -Complex.I • fderiv ℝ f z 1 := hcr hz
  have hcr_comp :
      fderiv ℝ (f ∘ conj) (conj z) Complex.I =
        Complex.I • fderiv ℝ (f ∘ conj) (conj z) 1 := by
    -- Precomposing by `conj` flips the sign in the anti-Cauchy-Riemann equation.
    simpa [hcomp, ContinuousLinearMap.comp_apply, map_neg] using congrArg Neg.neg hanti_z
  have hcomp_real : DifferentiableAt ℝ (f ∘ conj) (conj z) :=
    by
      have hf_real' : DifferentiableAt ℝ f (conj (conj z)) := by
        simpa using hf_real
      simpa [Function.comp_assoc] using hf_real'.comp (conj z) Complex.conjCLE.differentiableAt
  -- The ordinary Cauchy-Riemann equation now yields complex differentiability of `f ∘ conj`.
  exact (differentiableAt_complex_iff_differentiableAt_real (f := f ∘ conj) (x := conj z)).2
    ⟨hcomp_real, hcr_comp⟩

/-- Helper for Proposition 1.2: for a holomorphic map, a nonvanishing real Jacobian forces the
complex derivative to be nonzero. -/
lemma deriv_ne_zero_of_holomorphic_det_ne_zero {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hdet : (fderiv ℝ f z).det ≠ 0) : deriv f z ≠ 0 := by
  intro hderiv
  -- If the complex derivative vanished, the real derivative would be the zero map as well.
  have hzero : fderiv ℝ f z = 0 := by
    ext w
    rw [hf.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul]
    simp [hderiv]
  have hdet_zero : (fderiv ℝ f z).det = 0 := by
    rw [ContinuousLinearMap.det, hzero]
    simpa using (LinearMap.det_zero (R := ℝ) (M := ℂ))
  exact hdet hdet_zero

/-- Proposition 1.2 (1). A continuously differentiable transformation of a connected open subset
of the complex plane with everywhere nonvanishing Jacobian preserves angles if and only if it is
either holomorphic or antiholomorphic. Here angle preservation is expressed by pointwise
conformality of the real differential, while antiholomorphicity on `D` is written in the
source-facing form that `conj ∘ f` is holomorphic on `D`. The bridge
`differentiableOn_conj_comp_iff` recovers the equivalent canonical pointwise owner on open sets.
-/
theorem conformal_on_iff_holomorphic_or_antiholomorphic_on
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hf_c1 : ContDiffOn ℝ 1 f D) (hjac : ∀ z ∈ D, (fderiv ℝ f z).det ≠ 0) :
    (∀ z ∈ D, ConformalAt f z) ↔
      DifferentiableOn ℂ f D ∨ DifferentiableOn ℂ (conj ∘ f) D := by
  constructor
  · intro hconf
    let A : ℂ → ℂ := fun z ↦ fderiv ℝ f z Complex.I
    let B : ℂ → ℂ := fun z ↦ Complex.I • fderiv ℝ f z 1
    -- The real derivative field is continuous on `D`, so both CR residuals are continuous.
    have hfderiv_cont : ContinuousOn (fderiv ℝ f) D :=
      hf_c1.continuousOn_fderiv_of_isOpen hD_open (by norm_num)
    have hA_cont : ContinuousOn A D := by
      simpa [A] using hfderiv_cont.clm_apply continuousOn_const
    have hB_cont : ContinuousOn B D := by
      simpa [B] using (hfderiv_cont.clm_apply continuousOn_const).const_smul Complex.I
    -- Pointwise conformality gives the CR-or-anti-CR sign dichotomy, hence `A² = B²`.
    have hsq : EqOn (A ^ 2) (B ^ 2) D := by
      intro z hz
      rcases conformalAt_cauchy_riemann_or_anticauchy_riemann
          (f := f) (hconf z hz) (hjac z hz) with hcr | hanti
      · simpa [A, B] using congrArg (fun w : ℂ ↦ w ^ 2) hcr
      · have hsq_neg := congrArg (fun w : ℂ ↦ w ^ 2) hanti
        simpa [A, B, smul_eq_mul, neg_mul] using hsq_neg
    -- The second CR residual never vanishes, otherwise the whole derivative would be zero.
    have hB_ne : ∀ {z : ℂ}, z ∈ D → B z ≠ 0 := by
      intro z hz hBz
      have h1 : fderiv ℝ f z 1 = 0 := by
        have hmul : Complex.I * fderiv ℝ f z 1 = 0 := by
          simpa [B, smul_eq_mul] using hBz
        exact (mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero
      have hI : fderiv ℝ f z Complex.I = 0 := by
        rcases conformalAt_cauchy_riemann_or_anticauchy_riemann
            (f := f) (hconf z hz) (hjac z hz) with hcr | hanti
        · simpa [h1, smul_eq_mul] using hcr
        · simpa [h1, smul_eq_mul] using hanti
      have hzero :
          fderiv ℝ f z = 0 :=
        complex_continuousLinearMap_eq_zero_of_apply_one_eq_zero_apply_I_eq_zero h1 hI
      have hdet_zero : (fderiv ℝ f z).det = 0 := by
        rw [ContinuousLinearMap.det, hzero]
        simpa using (LinearMap.det_zero (R := ℝ) (M := ℂ))
      exact hjac z hz hdet_zero
    -- Connectedness forces one of the two sign choices to hold on all of `D`.
    rcases hD_connected.isPreconnected.eq_or_eq_neg_of_sq_eq hA_cont hB_cont hsq @hB_ne with
        hcr | hanti
    · left
      -- The global positive sign gives holomorphicity on all of `D`.
      exact holomorphic_on_of_cauchy_riemann_eq (D := D) (f := f) hD_open hf_c1 hcr
    · right
      -- The global negative sign gives antiholomorphicity on all of `D`.
      have hanti' :
          EqOn (fun z ↦ fderiv ℝ f z Complex.I) (fun z ↦ -Complex.I • fderiv ℝ f z 1) D := by
        intro z hz
        simpa [A, B, Pi.neg_apply] using hanti hz
      exact antiholomorphic_on_of_anticauchy_riemann_eq (D := D) (f := f) hD_open hf_c1 hanti'
  · rintro (hf_holo | hf_anti) z hz
    · -- A holomorphic map with nonzero Jacobian is conformal at each point.
      have hz_holo : DifferentiableAt ℂ f z := hf_holo.differentiableAt (hD_open.mem_nhds hz)
      have hz_deriv_ne : deriv f z ≠ 0 :=
        deriv_ne_zero_of_holomorphic_det_ne_zero (f := f) hz_holo (hjac z hz)
      exact hz_holo.conformalAt hz_deriv_ne
    · -- For the antiholomorphic branch, use the source-facing pointwise owner from the bridge.
      have hanti_pt :
          ∀ w ∈ D, DifferentiableAt ℂ (f ∘ conj) (conj w) :=
        (differentiableOn_conj_comp_iff (D := D) (f := f) hD_open).1 hf_anti
      have hz_anti : DifferentiableAt ℂ (f ∘ conj) (conj z) := hanti_pt z hz
      have hz_nonzero : fderiv ℝ f z ≠ 0 := by
        intro hzero
        have hdet_zero : (fderiv ℝ f z).det = 0 := by
          rw [ContinuousLinearMap.det, hzero]
          simpa using (LinearMap.det_zero (R := ℝ) (M := ℂ))
        exact hjac z hz hdet_zero
      exact (conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj (f := f) (z := z)).2
        ⟨Or.inr hz_anti, hz_nonzero⟩

/-- Proposition 1.2 (2). At each point of an open domain where `f` is holomorphic, the real
differential preserves the orientation of angles. -/
theorem holomorphic_on_preserves_oriented_angles
    (hD_open : IsOpen D) (hf_holo : DifferentiableOn ℂ f D)
    {z : ℂ} (hz : z ∈ D) (hjac : (fderiv ℝ f z).det ≠ 0) (u v : ℂ) :
    Complex.orientation.oangle ((fderiv ℝ f z) u) ((fderiv ℝ f z) v) =
      Complex.orientation.oangle u v := by
  -- Identify the real derivative with multiplication by the complex derivative.
  have hz_holo : DifferentiableAt ℂ f z := hf_holo.differentiableAt (hD_open.mem_nhds hz)
  have hz_deriv_ne : deriv f z ≠ 0 :=
    deriv_ne_zero_of_holomorphic_det_ne_zero (f := f) hz_holo hjac
  have hfderiv_apply (w : ℂ) : (fderiv ℝ f z) w = deriv f z * w := by
    rw [hz_holo.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul]
  -- The source proof reduces the statement to invariance under multiplication by one scalar.
  rw [hfderiv_apply, hfderiv_apply]
  exact complex_orientation_oangle_mul (deriv f z) hz_deriv_ne u v

/-- Proposition 1.2 (3). At each point of an open domain where `f` is antiholomorphic, in the
source-facing sense that `conj ∘ f` is holomorphic on `D`, the real differential reverses the
orientation of angles. The bridge `differentiableOn_conj_comp_iff` recovers the equivalent
canonical pointwise owner on open sets. -/
theorem antiholomorphic_on_reverses_oriented_angles
    (hD_open : IsOpen D) (hf_anti : DifferentiableOn ℂ (conj ∘ f) D)
    {z : ℂ} (hz : z ∈ D) (hjac : (fderiv ℝ f z).det ≠ 0) (u v : ℂ) :
    Complex.orientation.oangle ((fderiv ℝ f z) u) ((fderiv ℝ f z) v) =
      -Complex.orientation.oangle u v := by
  let g : ℂ → ℂ := conj ∘ f
  -- Rewrite the differential of `f` through the holomorphic map `g = conj ∘ f`.
  have hz_g : DifferentiableAt ℂ g z := hf_anti.differentiableAt (hD_open.mem_nhds hz)
  have hfg : fderiv ℝ f z = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g z) := by
    have hg_real : DifferentiableAt ℝ g z := hz_g.restrictScalars ℝ
    have hconj : fderiv ℝ conj (g z) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) :=
      Complex.conjCLE.fderiv
    have htmp :
        fderiv ℝ (conj ∘ g) z = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g z) := by
      simpa [Function.comp_apply, hconj] using
        (fderiv_comp (f := g) (g := conj) (x := z) Complex.conjCLE.differentiableAt hg_real)
    have hfun : conj ∘ g = f := by
      funext w
      simp [g]
    simpa [hfun] using htmp
  have hfderiv_apply (w : ℂ) : (fderiv ℝ f z) w = conj (deriv g z * w) := by
    calc
      (fderiv ℝ f z) w = conj ((fderiv ℝ g z) w) := by
        rw [hfg, ContinuousLinearMap.comp_apply]
        simp
      _ = conj (deriv g z * w) := by
        rw [hz_g.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul]
  have hz_deriv_ne : deriv g z ≠ 0 := by
    intro hzero
    have h1 : fderiv ℝ f z 1 = 0 := by
      simpa [g, hzero] using hfderiv_apply 1
    have hI : fderiv ℝ f z Complex.I = 0 := by
      simpa [g, hzero] using hfderiv_apply Complex.I
    have hzero_map :
        fderiv ℝ f z = 0 :=
      complex_continuousLinearMap_eq_zero_of_apply_one_eq_zero_apply_I_eq_zero h1 hI
    have hdet_zero : (fderiv ℝ f z).det = 0 := by
      rw [ContinuousLinearMap.det, hzero_map]
      simpa using (LinearMap.det_zero (R := ℝ) (M := ℂ))
    exact hjac hdet_zero
  -- Conjugation reverses orientation, while multiplication by the holomorphic derivative preserves it.
  calc
    Complex.orientation.oangle ((fderiv ℝ f z) u) ((fderiv ℝ f z) v)
        = Complex.orientation.oangle (conj (deriv g z * u)) (conj (deriv g z * v)) := by
            rw [hfderiv_apply, hfderiv_apply]
    _ = -Complex.orientation.oangle (deriv g z * u) (deriv g z * v) := by
          rw [complex_orientation_oangle_conj]
    _ = -Complex.orientation.oangle u v := by
          rw [complex_orientation_oangle_mul (deriv g z) hz_deriv_ne]
