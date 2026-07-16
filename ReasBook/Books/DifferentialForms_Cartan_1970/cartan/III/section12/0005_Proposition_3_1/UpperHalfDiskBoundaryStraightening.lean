import DifferentialForms_Cartan_1970.cartan.III.section12.«0005_Proposition_3_1».UpperHalfDiskBoundaryRegularity

noncomputable section

open Filter
open MeasureTheory
open UpperHalfPlane
open scoped BigOperators Interval Topology

section

variable {f : ℂ → ℂ} {s : Finset ℂ}

/-- Helper for Proposition 3.1: the local diameter strip data packages directly into an explicit
affine boundary-straightening chart on `Plane`. -/
lemma upper_half_disk_affine_strip_chart_exists
    {r t₀ eps_t eps_u : ℝ} (hr : 0 < r)
    (hεt_pos : 0 < eps_t) (hεu_pos : 0 < eps_u)
    (hstrip_param : Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hstrip_side :
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∉
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) ∧
        (0 < u →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∈
            interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ))) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  let hx : ℝ ≃ₜ ℝ :=
    (Homeomorph.smulOfNeZero (4 * r) (by positivity : (4 * r) ≠ 0)).trans
      (Homeomorph.addRight (-r))
  let δ₀ : Plane ≃ₜ Plane := hx.prodCongr (Homeomorph.refl ℝ)
  let δ₁ : OpenPartialHomeomorph Plane Plane := δ₀.toOpenPartialHomeomorph
  let strip : Set Plane :=
    Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ×ˢ Set.Ioo (-eps_u) eps_u
  let δ : OpenPartialHomeomorph Plane Plane := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    simp [δ₁, δ₀, hx]
  have hsource_subset : δ.source ⊆ δ₁.source := by
    intro p hp
    exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).1
  have htarget_subset : δ.target ⊆ δ₁.target := by
    intro q hq
    exact (show q ∈ δ₁.target ∩ δ₁.symm ⁻¹' strip by simpa [δ, strip] using hq).1
  have hδ_contDiff :
      ContDiffOn ℝ 1 δ δ.source := by
    -- The restricted chart still has the same global affine forward formula.
    have hglobal :
        ContDiff ℝ 1 (fun p : Plane ↦ (((4 * r) * p.1 - r), p.2)) := by
      fun_prop
    simpa [δ, δ₁, δ₀, hx, strip] using hglobal.contDiffOn
  have hδsymm_contDiff :
      ContDiffOn ℝ 1 δ.symm δ.target := by
    -- The inverse chart is again affine: undo the translation and divide by `4r`.
    have hglobal :
        ContDiff ℝ 1 (fun p : Plane ↦ (((p.1 + r) / (4 * r)), p.2)) := by
      fun_prop
    have hsymm_formula :
        (δ.symm : Plane → Plane) = fun p : Plane ↦ (((p.1 + r) / (4 * r)), p.2) := by
      ext p
      · simp [δ, δ₁, δ₀, hx, div_eq_mul_inv, sub_eq_add_neg]
        have hadd : (Homeomorph.addRight (-r)).symm p.1 = p.1 + r := by
          simp [Homeomorph.addRight]
        rw [hadd]
        ring
      · simp [δ, δ₁, δ₀, hx]
    simpa [hsymm_formula] using hglobal.contDiffOn
  have hmap_axis :
      ∀ {t : ℝ}, t ∈ δ.horizontalAxisDomain →
        δ (t, 0) = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIoo : t ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := hstrip_param htStrip.1
    have htIcc : t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := ⟨htIoo.1.le, htIoo.2.le⟩
    calc
      δ (t, 0) = (((4 * r) * t - r), 0) := by
        simp [δ, δ₁, δ₀, hx, sub_eq_add_neg]
      _ = Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)) := by
        simp [Complex.equivRealProd]
      _ = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
        symm
        exact upper_half_disk_boundary_realCurve_eqOn_diameter_interval r htIcc
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := hδ_contDiff
      contDiffOn_symm := hδsymm_contDiff
      map_horizontal_axis := fun ht ↦ hmap_axis ht
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The base point belongs to the explicit strip centered at `(t₀, 0)`.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · intro p hp
    -- The source restriction keeps the parameter inside the local diameter branch, hence in `(0,1)`.
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).2
    have hpBranch : p.1 ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := hstrip_param hpStrip.1
    exact ⟨⟨hpBranch.1, lt_trans hpBranch.2 (by norm_num)⟩, Set.mem_univ _⟩
  · -- The chart image of the diameter branch is exactly the horizontal axis in the restricted strip.
    apply curve_image_is_horizontal_axis
    intro t ht
    exact hmap_axis ht
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          ((((4 * r) * p.1 - r : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) := by
      rw [Complex.equivRealProdCLM_symm_apply]
      simp [δ, δ₁, δ₀, hx, mul_comm, mul_left_comm, mul_assoc]
      ring
    have houtside :
        Complex.equivRealProdCLM.symm (δ p) ∉ ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
      rw [hformula]
      exact (hstrip_side hpStrip.1 hpStrip.2).1 hp.2
    exact houtside hz.2
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          ((((4 * r) * p.1 - r : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) := by
      rw [Complex.equivRealProdCLM_symm_apply]
      simp [δ, δ₁, δ₀, hx, mul_comm, mul_left_comm, mul_assoc]
      ring
    -- Positive transverse height enters the semidisk interior by the local strip estimates.
    rw [hformula]
    exact (hstrip_side hpStrip.1 hpStrip.2).2 hp.2

/-- Helper for Proposition 3.1: every regular parameter on the open diameter branch admits an
explicit affine boundary-straightening chart for the closed upper semidisk. -/
lemma upper_half_disk_boundary_diameter_branch_exists_boundary_chart
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the quantitative strip estimates are now isolated in
  -- `upper_half_disk_diameter_local_strip_data`, so the remaining work is to package that affine
  -- strip as an `OpenPartialHomeomorph` and feed the side estimates into
  -- `IsBoundaryStraighteningAt.exterior_on_right` and `.interior_on_left`.
  obtain ⟨eps_t, eps_u, hεt_pos, hεu_pos, hstrip_param, hstrip_side⟩ :=
    upper_half_disk_diameter_local_strip_data hr ht₀
  exact upper_half_disk_affine_strip_chart_exists
    hr hεt_pos hεu_pos hstrip_param hstrip_side

/-- Helper for Proposition 3.1: every regular parameter on the open upper-semicircle branch
admits an explicit radial boundary-straightening chart for the closed upper semidisk. -/
lemma upper_half_disk_boundary_arc_branch_exists_boundary_chart
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: normalize the radial tube first with
  -- `upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub`, then package the resulting
  -- radius/angle strip as the arc branch boundary chart.
  obtain ⟨eps_t, eps_u, hεt_pos, hεu_pos, hεu_lt, hstrip_param, hstrip_side⟩ :=
    upper_half_disk_arc_local_strip_data hr ht₀
  let θ : ℝ → ℝ := fun t ↦ Real.pi * (2 * t - 1)
  let γ : ℝ → ℂ := fun t ↦ circleMap 0 r (θ t)
  let n : ℝ → ℂ := fun t ↦ -Complex.exp (θ t * Complex.I)
  let tangent : ℂ := (2 * Real.pi : ℝ) • (circleMap 0 r (θ t₀) * Complex.I)
  let Ψ : Plane → ℂ := fun p ↦ γ p.1 + p.2 • n p.1
  let Φ : Plane → Plane := fun p ↦ Complex.equivRealProd (Ψ p)
  have _hkeep_radius : eps_u < r := hεu_lt
  have hθCont : ContDiffAt ℝ 1 θ t₀ := by
    -- The semicircle angle is an affine function of the source parameter.
    have hθ : ContDiff ℝ 1 θ := by
      fun_prop
    exact hθ.contDiffAt
  have hγCont : ContDiffAt ℝ 1 γ t₀ := by
    -- The boundary branch is smooth after composing `circleMap` with the affine angle.
    simpa [γ] using (contDiff_circleMap 0 r).contDiffAt.comp t₀ hθCont
  have hnCont : ContDiffAt ℝ 1 n t₀ := by
    -- The inward radial field varies smoothly along the open arc branch.
    have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
      simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
    have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
      simpa [one_mul] using hθComplex.mul contDiffAt_const
    simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner).neg
  have hγDeriv : HasDerivAt γ tangent t₀ := by
    -- Differentiate the upper-semicircle branch by the chain rule.
    simpa [γ, tangent] using
      ((hasDerivAt_circleMap 0 r (θ t₀)).scomp t₀ (upper_half_disk_arc_arg_hasDerivAt t₀))
  have htangent_formula :
      tangent = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
        Complex.exp (θ t₀ * Complex.I) := by
    -- Rewrite the chain-rule derivative into the explicit tangent form used by the frame lemma.
    calc
      tangent = ((2 * Real.pi : ℝ) : ℂ) * (circleMap 0 r (θ t₀) * Complex.I) := by
        simp [tangent, smul_eq_mul]
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) := by
            rw [circleMap, zero_add]
            simp [mul_assoc, mul_left_comm, mul_comm]
  obtain ⟨hΨcont, hΨderiv⟩ := upper_half_disk_radial_tube_hasFDerivAt
    (γ := γ) (n := n) (t₀ := t₀) (v := tangent) hγCont hγDeriv hnCont
  have hΦcont : ContDiffAt ℝ 1 Φ (t₀, 0) := by
    -- Converting the complex tube to plane coordinates preserves the `C¹` regularity.
    simpa [Φ] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_contDiffAt_iff).2 hΨcont
  let v : Plane := Complex.equivRealProd tangent
  let radial : Plane := Complex.equivRealProd (n t₀)
  have hv : v ≠ 0 := by
    -- The arc tangent is nonzero because both the radius and the exponential factor are nonzero.
    intro hv0
    have htangent : tangent = 0 := by
      exact Complex.equivRealProd.injective (by simpa [v] using hv0)
    have hscale : ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hr.ne'
    have hmul :
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) = 0 := by
      simpa [htangent_formula] using htangent
    exact Complex.exp_ne_zero (θ t₀ * Complex.I) ((mul_eq_zero.mp hmul).resolve_left hscale)
  have hrot : rot90 v = (2 * Real.pi * r) • radial := by
    -- Quarter-turning the tangent gives the inward radial direction on the semicircle.
    simpa [v, radial, n, θ, htangent_formula] using
      upper_half_disk_arc_rot90_tangent_eq_scaled_inward (r := r) (t₀ := t₀)
  obtain ⟨e₀, he₀⟩ := rot90_frame_equiv_of_ne_zero v hv
  let c : ℝ := 2 * Real.pi * r
  have hc : c ≠ 0 := by
    positivity
  let e : Plane ≃L[ℝ] Plane := (upper_half_disk_plane_second_rescale c hc).trans e₀
  have hderiv_map :
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] Plane).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight tangent +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Convert the complex tangent/normal columns to their plane-coordinate versions.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    simp [ContinuousLinearMap.comp_apply, v, radial, ContinuousLinearMap.smulRight_apply]
  have hΦderiv :
      HasFDerivAt Φ
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial)
        (t₀, 0) := by
    -- The real-plane tube has tangent column `v` and inward-normal column `radial`.
    simpa [Φ, hderiv_map] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_hasFDerivAt_iff).2 hΨderiv
  have he : (e : Plane →L[ℝ] Plane) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Rescaling the second frame coordinate turns the `rot90` column into the actual inward
    -- radial column.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    change e₀ (x, y / c) = x • v + y • radial
    calc
      e₀ (x, y / c) = x • v + (y / c) • rot90 v := by
        simpa [ContinuousLinearMap.smulRight_apply] using
          congrArg (fun f : Plane →L[ℝ] Plane => f (x, y / c)) he₀
      _ = x • v + (y / c) • (c • radial) := by
            rw [hrot]
      _ = x • v + (((y / c) * c) • radial) := by
            rw [smul_smul]
      _ = x • v + y • radial := by
            have hyc : y * c⁻¹ * c = y := by
              calc
                y * c⁻¹ * c = y * (c⁻¹ * c) := by ring
                _ = y := by simp [hc]
            simp [div_eq_mul_inv, hyc]
  have hΦderiv' : HasFDerivAt Φ (e : Plane →L[ℝ] Plane) (t₀, 0) := by
    -- This is the invertible derivative required by the inverse function theorem.
    simpa [he] using hΦderiv
  let δ₀ : OpenPartialHomeomorph Plane Plane :=
    hΦcont.toOpenPartialHomeomorph Φ hΦderiv' one_ne_zero
  let δ₁ : OpenPartialHomeomorph Plane Plane := δ₀.restrContDiff ℝ 1 (by norm_num)
  let strip : Set Plane :=
    Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ×ˢ Set.Ioo (-eps_u) eps_u
  let δ : OpenPartialHomeomorph Plane Plane := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  have hδ₀_source : (t₀, 0) ∈ δ₀.source := by
    -- The inverse function theorem keeps the base point in the source chart.
    exact hΦcont.mem_toOpenPartialHomeomorph_source hΦderiv' one_ne_zero
  have hδ₀_symm : ContDiffAt ℝ 1 δ₀.symm (Φ (t₀, 0)) := by
    -- The local inverse remains `C¹` at the image of the base point.
    simpa [δ₀, Φ] using hΦcont.to_localInverse hΦderiv' one_ne_zero
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    -- Restricting to the `C¹` locus keeps the base point available.
    simpa [δ₁, δ₀, Φ] using And.intro hδ₀_source (And.intro hΦcont hδ₀_symm)
  have hsource_subset : δ.source ⊆ δ₁.source := by
    intro p hp
    exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).1
  have htarget_subset : δ.target ⊆ δ₁.target := by
    intro q hq
    exact (show q ∈ δ₁.target ∩ δ₁.symm ⁻¹' strip by simpa [δ, strip] using hq).1
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The base point lies in the local strip because `t₀` is centered there and `0` is between
    -- `-eps_u` and `eps_u`.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · -- The source restriction keeps the first coordinate on the open arc branch.
    intro p hp
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).2
    exact ⟨⟨by linarith [(hstrip_param hpStrip.1).1], (hstrip_param hpStrip.1).2⟩, Set.mem_univ _⟩
  · -- Restricting the inverse-function chart preserves the `C¹` regularity on the smaller
    -- source.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono hsource_subset
  · -- The same inheritance applies to the local inverse on the smaller target.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono htarget_subset
  · intro t ht
    -- Along the horizontal axis, the chart reproduces the arc branch of the semidisk contour.
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) 1 :=
      ⟨(hstrip_param htStrip.1).1.le, (hstrip_param htStrip.1).2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))) := by
            simp [γ, θ]
      _ = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
            symm
            exact upper_half_disk_boundary_realCurve_eqOn_arc_interval r htIcc
  · -- The chart image of the arc branch is exactly the horizontal axis in the restricted strip.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) 1 :=
      ⟨(hstrip_param htStrip.1).1.le, (hstrip_param htStrip.1).2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))) := by
            simp [γ, θ]
      _ = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
            symm
            exact upper_half_disk_boundary_realCurve_eqOn_arc_interval r htIcc
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          circleMap 0 (r - p.2) (θ p.1) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
            rw [Complex.equivRealProdCLM_symm_apply]
            exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
            simp [Ψ]
        _ = circleMap 0 r (θ p.1) + (p.2 : ℂ) * (-Complex.exp (θ p.1 * Complex.I)) := by
            simp [γ, n, smul_eq_mul]
        _ = circleMap 0 (r - p.2) (θ p.1) := by
            rw [upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub]
    have houtside :
        Complex.equivRealProdCLM.symm (δ p) ∉ ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
      rw [hformula]
      exact (hstrip_side hpStrip.1 hpStrip.2).1 hp.2
    exact houtside hz.2
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          circleMap 0 (r - p.2) (θ p.1) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
            rw [Complex.equivRealProdCLM_symm_apply]
            exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
            simp [Ψ]
        _ = circleMap 0 r (θ p.1) + (p.2 : ℂ) * (-Complex.exp (θ p.1 * Complex.I)) := by
            simp [γ, n, smul_eq_mul]
        _ = circleMap 0 (r - p.2) (θ p.1) := by
            rw [upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub]
    -- Positive transverse height enters the semidisk interior by the local strip estimates.
    rw [hformula]
    exact (hstrip_side hpStrip.1 hpStrip.2).2 hp.2

/-- Helper for Proposition 3.1: every regular interior parameter of the explicit semidisk contour
admits a local boundary-straightening chart for the closed upper half-disk. -/
lemma upper_half_disk_boundary_exists_boundary_straightening_at_regular_point
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: first exclude the midpoint corner, then dispatch to the explicit affine or
  -- radial chart depending on whether the regular parameter lies on the diameter or the arc.
  let _ := hderiv
  rcases upper_half_disk_boundary_regular_parameter_mem_branch hr ht₀ hdiff with hdiam | harc
  · exact upper_half_disk_boundary_diameter_branch_exists_boundary_chart hr hdiam
  · exact upper_half_disk_boundary_arc_branch_exists_boundary_chart hr harc

/-- Helper for Proposition 3.1: the explicit semidisk contour is an oriented boundary of the
closed upper half-disk. -/
theorem upper_half_disk_boundary_isOrientedBoundaryOf {r : ℝ} (hr : 0 < r) :
    IsOrientedBoundaryOf ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
      (fun _ : Unit ↦ (upperHalfDiskBoundaryPath r).toClosedPath) := by
  classical
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (upperHalfDiskBoundaryPath r).toClosedPath
  change IsOrientedBoundaryOf K Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The semidisk is the intersection of a compact closed ball with the closed upper half-plane.
    let K' : Set ℂ := Metric.closedBall (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
    have hK' : IsCompact K' := by
      exact (isCompact_closedBall (0 : ℂ) r).inter_right
        (isClosed_le continuous_const Complex.continuous_im)
    convert hK' using 1
    ext z
    simp [K', K, Metric.mem_closedBall, dist_eq_norm]
  · rintro ⟨⟩
    -- The singleton closed-path family inherits the explicit contour regularity.
    simpa [Γ, Path.toClosedPath] using upper_half_disk_boundary_isPiecewiseDifferentiable r
  · rintro ⟨⟩ s t hst
    -- Simplicity is already proved directly from the diameter/arc branch decomposition.
    simpa [Γ, Path.toClosedPath] using upper_half_disk_boundary_simple_eq_or_endpoints hr hst
  · intro i j hij
    -- A singleton family is pairwise disjoint for the trivial reason.
    exact (hij rfl).elim
  · -- Collapse the singleton family back to the explicit contour and rewrite its range as the
    -- semidisk frontier.
    calc
      (⋃ i : Unit, Set.range (Γ i).toPath) = Set.range (upperHalfDiskBoundaryPath r) := by
          simpa [Γ] using upper_half_disk_boundary_singleton_iUnion_range r
      _ = frontier K := by
          simpa [K] using upper_half_disk_boundary_path_range_eq_frontier hr
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- The only geometric input not already encoded above is the regular-point straightening
    -- chart for this explicit semidisk contour.
    simpa [K, Γ] using
      upper_half_disk_boundary_exists_boundary_straightening_at_regular_point
        (r := r) hr ht₀ hdiff hderiv

end
