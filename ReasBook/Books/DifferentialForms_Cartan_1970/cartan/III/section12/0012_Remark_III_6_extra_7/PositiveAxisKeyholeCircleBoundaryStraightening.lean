import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeBoundaryStraightening

open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: moving the inner surviving circle in the radial direction
only changes its radius, so the circular tube can be rewritten without transport. -/
private lemma positiveAxisInnerArc_add_real_mul_radial_eq_circleMap_radius_add
    (ε α u : ℝ) :
    circleMap 0 ε α + (u : ℂ) * Complex.exp (α * Complex.I) =
      circleMap 0 (ε + u) α := by
  rw [circleMap, zero_add, circleMap, zero_add]
  calc
    (ε : ℂ) * Complex.exp (α * Complex.I) + (u : ℂ) * Complex.exp (α * Complex.I) =
        (((ε : ℂ) + u) * Complex.exp (α * Complex.I)) := by
          ring
    _ = (((ε + u : ℝ) : ℂ) * Complex.exp (α * Complex.I)) := by
          norm_num

/-- Helper for Remark III.6-extra-7: moving the outer surviving circle against the inward radial
direction only decreases the radius while preserving the angle. -/
private lemma positiveAxisOuterArc_add_real_mul_inward_eq_circleMap_radius_sub
    (R α u : ℝ) :
    circleMap 0 R α + (u : ℂ) * (-Complex.exp (α * Complex.I)) =
      circleMap 0 (R - u) α := by
  rw [circleMap, zero_add, circleMap, zero_add]
  calc
    (R : ℂ) * Complex.exp (α * Complex.I) + (u : ℂ) * (-Complex.exp (α * Complex.I)) =
        (((R : ℂ) - u) * Complex.exp (α * Complex.I)) := by
          ring
    _ = (((R - u : ℝ) : ℂ) * Complex.exp (α * Complex.I)) := by
          norm_num

/-- Helper for Remark III.6-extra-7: quarter-turning a circular tangent in plane coordinates
produces the radial direction scaled by the negated angular speed. -/
private lemma positiveAxis_circleMap_rot90_tangent_eq_scaled_radial
    {c θ : ℝ} :
    rot90
      (Complex.equivRealProd
        ((((c : ℂ) * Complex.I) * Complex.exp (θ * Complex.I)))) =
      (-c) • Complex.equivRealProd (Complex.exp (θ * Complex.I)) := by
  -- Compute both real coordinates directly after rewriting the quarter-turn in `Plane`.
  ext <;>
    simp [rot90, Complex.equivRealProd, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Helper for Remark III.6-extra-7: once a radial tube has the correct horizontal-axis formula,
owner-side side test, and normalized tangent/normal frame, the inverse function theorem packages
it into a local boundary-straightening chart. -/
private lemma positiveAxisRadialBoundaryStripChartExists
    {K : Set ℂ} {curve : ℝ → Plane} {γ n : ℝ → ℂ} {t₀ eps_t eps_u c : ℝ} {tangent : ℂ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hεt_pos : 0 < eps_t) (hεu_pos : 0 < eps_u)
    (hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1)
    (hγCont : ContDiffAt ℝ 1 γ t₀)
    (hnCont : ContDiffAt ℝ 1 n t₀)
    (hγDeriv : HasDerivAt γ tangent t₀)
    (hv : Complex.equivRealProd tangent ≠ 0)
    (hrot : rot90 (Complex.equivRealProd tangent) = c • Complex.equivRealProd (n t₀))
    (hc : c ≠ 0)
    (hmap_axis :
      ∀ {t : ℝ}, t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        curve t = Complex.equivRealProd (γ t))
    (hstrip_side :
      ∀ {p : Plane},
        |p.1 - t₀| < eps_t → |p.2| < eps_u →
        let z := γ p.1 + p.2 • n p.1
        (p.2 < 0 → z ∉ K) ∧
          (0 < p.2 → z ∈ interior K)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt K curve t₀ δ := by
  -- Route correction: once the owner-facing radial side test is known, the rest is the generic
  -- inverse-function packaging of the radial tube.
  let Ψ : Plane → ℂ := fun p ↦ γ p.1 + p.2 • n p.1
  let Φ : Plane → Plane := fun p ↦ Complex.equivRealProd (Ψ p)
  obtain ⟨hΨcont, hΨderiv⟩ :=
    positiveAxis_radialTube_hasFDerivAt
      (γ := γ) (n := n) (t₀ := t₀) (v := tangent) hγCont hγDeriv hnCont
  have hΦcont : ContDiffAt ℝ 1 Φ (t₀, 0) := by
    -- Converting the complex tube to `Plane` coordinates preserves the `C¹` regularity.
    simpa [Φ] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_contDiffAt_iff).2 hΨcont
  let v : Plane := Complex.equivRealProd tangent
  let radial : Plane := Complex.equivRealProd (n t₀)
  obtain ⟨e₀, he₀⟩ := rot90_frame_equiv_of_ne_zero v hv
  let e : Plane ≃L[ℝ] Plane := (positiveAxis_planeSecondRescale c hc).trans e₀
  have hderiv_map :
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] Plane).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight tangent +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- The derivative columns are exactly the tangent and radial vectors in `Plane`.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    simp [ContinuousLinearMap.comp_apply, v, radial, ContinuousLinearMap.smulRight_apply]
  have hΦderiv :
      HasFDerivAt Φ
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial)
        (t₀, 0) := by
    -- The plane-valued tube keeps the same tangent and radial columns after `equivRealProd`.
    simpa [Φ, hderiv_map] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_hasFDerivAt_iff).2 hΨderiv
  have he : (e : Plane →L[ℝ] Plane) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Rescaling the second source coordinate normalizes `rot90 v` to the actual radial column.
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
    -- This is the invertible derivative needed by the inverse function theorem.
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
    -- The local inverse is again `C¹` at the image of the base point.
    simpa [δ₀, Φ] using hΦcont.to_localInverse hΦderiv' one_ne_zero
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    -- Restricting to the `C¹` locus still keeps the base point available.
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
  · -- The centered strip contains `(t₀, 0)`.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · -- Any source point still projects to a parameter in the ambient unit interval.
    intro p hp
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).2
    exact ⟨hstrip_param hpStrip.1, Set.mem_univ _⟩
  · -- Restricting the inverse-function chart preserves the `C¹` regularity on the source.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono hsource_subset
  · -- The same inheritance applies to the local inverse on the restricted target.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono htarget_subset
  · intro t ht
    -- Along the horizontal axis, the chart reproduces the requested branch of the contour.
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = curve t := by
            simpa using (hmap_axis htStrip.1).symm
  · -- The chart image of the boundary branch is exactly the horizontal axis in the restricted
    -- strip.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = curve t := by
            simpa using (hmap_axis htStrip.1).symm
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hp₁Abs : |p.1 - t₀| < eps_t := by
      have hpLower : -eps_t < p.1 - t₀ := by
        linarith [hpStrip.1.1]
      have hpUpper : p.1 - t₀ < eps_t := by
        linarith [hpStrip.1.2]
      exact abs_lt.mpr ⟨hpLower, hpUpper⟩
    have hp₂Abs : |p.2| < eps_u := by
      have hpLower : -eps_u < p.2 := hpStrip.2.1
      have hpUpper : p.2 < eps_u := hpStrip.2.2
      exact abs_lt.mpr ⟨hpLower, hpUpper⟩
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) = γ p.1 + p.2 • n p.1 := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
            rw [Complex.equivRealProdCLM_symm_apply]
            exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
            simp [Ψ]
    have hxK : Complex.equivRealProdCLM.symm (δ p) ∈ K := hx.2
    have hxK' : γ p.1 + p.2 • n p.1 ∈ K := by
      simpa [hformula] using hxK
    exact (hstrip_side hp₁Abs hp₂Abs).1 hp.2 hxK'
  · intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hp₁Abs : |p.1 - t₀| < eps_t := by
      have hpLower : -eps_t < p.1 - t₀ := by
        linarith [hpStrip.1.1]
      have hpUpper : p.1 - t₀ < eps_t := by
        linarith [hpStrip.1.2]
      exact abs_lt.mpr ⟨hpLower, hpUpper⟩
    have hp₂Abs : |p.2| < eps_u := by
      have hpLower : -eps_u < p.2 := hpStrip.2.1
      have hpUpper : p.2 < eps_u := hpStrip.2.2
      exact abs_lt.mpr ⟨hpLower, hpUpper⟩
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) = γ p.1 + p.2 • n p.1 := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
            rw [Complex.equivRealProdCLM_symm_apply]
            exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
            simp [Ψ]
    -- Positive transverse height enters the owner by the supplied radial side test.
    simpa [hformula] using (hstrip_side hp₁Abs hp₂Abs).2 hp.2

/-- Helper for Remark III.6-extra-7: a circle point with strict annulus radius and angle in the
open major arc lies in the interior of the positive-axis wedge-annulus. -/
private lemma positiveAxisWedgeAnnulus_circleMap_mem_interior_of_majorArc
    (R ε ρ : ℝ) (hε : 0 < ε) (hεR : ε < R) (hρ : ρ ∈ Set.Ioo ε R) {φ : ℝ}
    (hφ :
      φ ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε)) :
    circleMap 0 ρ φ ∈ interior (positiveAxisWedgeAnnulus R ε) := by
  let z : ℂ := circleMap 0 ρ φ
  have hρ_pos : 0 < ρ := lt_trans hε hρ.1
  have hangle := positiveAxisKeyhole_angle_bounds hε hεR
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  have hφIcc : φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · have hupper_pos : 0 < positiveAxisKeyholeUpperAngle R ε := by
        simpa [positiveAxisKeyholeUpperAngle] using hangle.1
      exact le_of_lt (lt_trans hupper_pos hφ.1)
    · exact le_of_lt (lt_trans hφ.2 horder.2)
  have hεz : ε < ‖z‖ := by
    simpa [z, norm_circleMap_zero, abs_of_pos hρ_pos] using hρ.1
  have hzR : ‖z‖ < R := by
    simpa [z, norm_circleMap_zero, abs_of_pos hρ_pos] using hρ.2
  by_cases hzre : z.re < 0
  · -- Strictly negative real part keeps the point away from the removed positive wedge.
    exact positiveAxisWedgeAnnulus_mem_interior_of_neg_re hεz hzR hzre
  · by_cases hzim : 0 < z.im
    · -- On the upper side, the major-arc inequality is exactly the positive signed height above
      -- the upper slit boundary line.
      have hφ_lt_pi : φ < Real.pi := by
        by_contra hnot
        have hge : Real.pi ≤ φ := le_of_not_gt hnot
        have htwopi : 2 * Real.pi - φ ∈ Set.Icc (0 : ℝ) Real.pi := by
          constructor <;> linarith [hφIcc.2, hge]
        have hsin_nonpos : Real.sin φ ≤ 0 := by
          have hsin_nonneg : 0 ≤ Real.sin (2 * Real.pi - φ) :=
            Real.sin_nonneg_of_mem_Icc htwopi
          rw [Real.sin_two_pi_sub] at hsin_nonneg
          linarith
        have hz_im_nonpos : z.im ≤ 0 := by
          calc
            z.im = ρ * Real.sin φ := by simp [z, circleMap_zero_im]
            _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ_pos.le hsin_nonpos
        linarith
      have hheight' :
          0 < Real.sin φ - (ε / R) * Real.cos φ := by
        have hrewrite :
            Real.sin φ - (ε / R) * Real.cos φ =
              Real.sin (φ - Real.arctan (ε / R)) / Real.cos (Real.arctan (ε / R)) := by
          have hcos : Real.cos (Real.arctan (ε / R)) ≠ 0 := by
            exact (Real.cos_arctan_pos (ε / R)).ne'
          rw [Real.sin_sub, Real.sin_arctan, Real.cos_arctan]
          field_simp [hcos]
        rw [hrewrite]
        have hangle' : φ - Real.arctan (ε / R) ∈ Set.Ioo (0 : ℝ) Real.pi := by
          constructor
          · simpa [positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle] using hφ.1
          · have harctan_lt : Real.arctan (ε / R) < Real.pi / 2 := by
              simpa [positiveAxisKeyholeAngle] using hangle.2
            linarith
        exact div_pos (Real.sin_pos_of_mem_Ioo hangle') (Real.cos_arctan_pos (ε / R))
      have hheight :
          0 < z.im - (ε / R) * z.re := by
        calc
          z.im - (ε / R) * z.re = ρ * (Real.sin φ - (ε / R) * Real.cos φ) := by
            simp [z, circleMap_zero_re, circleMap_zero_im]
            ring
          _ > 0 := mul_pos hρ_pos hheight'
      exact positiveAxisWedgeAnnulus_mem_interior_of_upper_gap hεz hzR hzim hheight
    · by_cases hzim_neg : z.im < 0
      · -- On the lower side, the reflected signed height stays strictly positive by the same
        -- major-arc angle algebra.
        have hφ_gt_pi : Real.pi < φ := by
          by_contra hnot
          have hle : φ ≤ Real.pi := le_of_not_gt hnot
          have hsin_nonneg : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc ⟨hφIcc.1, hle⟩
          have hz_im_nonneg : 0 ≤ z.im := by
            calc
              z.im = ρ * Real.sin φ := by simp [z, circleMap_zero_im]
              _ ≥ 0 := mul_nonneg hρ_pos.le hsin_nonneg
          linarith
        have hheight' :
            0 < -Real.sin φ - (ε / R) * Real.cos φ := by
          have hrewrite :
              -Real.sin φ - (ε / R) * Real.cos φ =
                Real.sin ((2 * Real.pi - Real.arctan (ε / R)) - φ) /
                  Real.cos (Real.arctan (ε / R)) := by
            have hcos : Real.cos (Real.arctan (ε / R)) ≠ 0 := by
              exact (Real.cos_arctan_pos (ε / R)).ne'
            rw [Real.sin_sub, Real.sin_two_pi_sub, Real.cos_two_pi_sub, Real.sin_arctan,
              Real.cos_arctan]
            field_simp [hcos]
            ring
          rw [hrewrite]
          have hangle' :
              (2 * Real.pi - Real.arctan (ε / R)) - φ ∈ Set.Ioo (0 : ℝ) Real.pi := by
            constructor
            · simpa [positiveAxisKeyholeLowerAngle, positiveAxisKeyholeAngle] using hφ.2
            · have harctan_pos : 0 < Real.arctan (ε / R) := by
                simpa [positiveAxisKeyholeAngle] using hangle.1
              linarith
          exact div_pos (Real.sin_pos_of_mem_Ioo hangle') (Real.cos_arctan_pos (ε / R))
        have hheight :
            0 < -z.im - (ε / R) * z.re := by
          calc
            -z.im - (ε / R) * z.re = ρ * (-Real.sin φ - (ε / R) * Real.cos φ) := by
              simp [z, circleMap_zero_re, circleMap_zero_im]
              ring
            _ > 0 := mul_pos hρ_pos hheight'
        exact positiveAxisWedgeAnnulus_mem_interior_of_lower_gap hεz hzR hzim_neg hheight
      · -- The open major arc has no nonnegative-real point with zero imaginary part.
        have hzim_zero : z.im = 0 := le_antisymm (le_of_not_gt hzim) (le_of_not_gt hzim_neg)
        have hsin_zero : Real.sin φ = 0 := by
          have hz_im_eq : z.im = ρ * Real.sin φ := by simp [z, circleMap_zero_im]
          rw [hz_im_eq] at hzim_zero
          nlinarith
        have hsin_shift : Real.sin (φ - Real.pi) = 0 := by
          rw [Real.sin_sub]
          simp [hsin_zero]
        have hφ_eq_pi : φ = Real.pi := by
          have hshift :
              φ - Real.pi ∈ Set.Ioo (-Real.pi) Real.pi := by
            constructor
            · have hupper_pos : 0 < positiveAxisKeyholeUpperAngle R ε := by
                simpa [positiveAxisKeyholeUpperAngle] using hangle.1
              linarith [hφ.1, hupper_pos]
            · have hφ_lt_two_pi : φ < 2 * Real.pi := lt_trans hφ.2 horder.2
              linarith
          have hzero :=
            (Real.sin_eq_zero_iff_of_lt_of_lt hshift.1 hshift.2).1 hsin_shift
          linarith
        have hzre_neg : z.re < 0 := by
          calc
            z.re = ρ * Real.cos φ := by simp [z, circleMap_zero_re]
            _ = -ρ := by simp [hφ_eq_pi]
            _ < 0 := by linarith
        exact (hzre hzre_neg).elim

/-- Helper for Remark III.6-extra-7: near an interior point of the inner circular branch,
negative transverse height exits through the inner boundary while positive transverse height moves
into the wedge-annulus interior with the same major-arc angle. -/
private lemma positiveAxisInnerArcChartSideOfAnnulus
    {R ε t₀ : ℝ} (hε : 0 < ε) (hεR : ε < R) (ht₀ : t₀ ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let α := AffineMap.lineMap
        (positiveAxisKeyholeUpperAngle R ε)
        (positiveAxisKeyholeLowerAngle R ε)
        (8 * p.1 - 1)
      let z := circleMap 0 (ε + p.2) α
      (p.2 < 0 → z ∉ positiveAxisWedgeAnnulus R ε) ∧
        (0 < p.2 → z ∈ interior (positiveAxisWedgeAnnulus R ε)) := by
  let eps_t : ℝ := min (t₀ - 1 / 8) (1 / 4 - t₀) / 2
  let eps_u : ℝ := min (ε / 2) ((R - ε) / 2)
  let η : ℝ := min eps_t eps_u
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  have hεt_pos : 0 < eps_t := by
    dsimp [eps_t]
    have hleft : 0 < t₀ - 1 / 8 := sub_pos.mpr ht₀.1
    have hright : 0 < 1 / 4 - t₀ := sub_pos.mpr ht₀.2
    have hmin : 0 < min (t₀ - 1 / 8) (1 / 4 - t₀) := lt_min hleft hright
    linarith
  have hεu_pos : 0 < eps_u := by
    dsimp [eps_u]
    have hleft : 0 < ε / 2 := by positivity
    have hright : 0 < (R - ε) / 2 := by linarith
    exact lt_min hleft hright
  have hη_pos : 0 < η := lt_min hεt_pos hεu_pos
  have hε_plus : ε + eps_u < R := by
    dsimp [eps_u]
    have hmin_le : min (ε / 2) ((R - ε) / 2) ≤ (R - ε) / 2 := min_le_right _ _
    linarith
  refine ⟨η, hη_pos, ?_⟩
  intro p hp₁ hp₂
  have hp₂η : |p.2| < eps_u := lt_of_lt_of_le hp₂ (min_le_right _ _)
  have hp₁_branch : p.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ) := by
    have hp₁η : |p.1 - t₀| < eps_t := lt_of_lt_of_le hp₁ (min_le_left _ _)
    have hp₁_lower : -eps_t < p.1 - t₀ := (abs_lt.mp hp₁η).1
    have hp₁_upper : p.1 - t₀ < eps_t := (abs_lt.mp hp₁η).2
    have hleft : 1 / 8 < t₀ - eps_t := by
      dsimp [eps_t]
      have hmin_le : min (t₀ - 1 / 8) (1 / 4 - t₀) ≤ t₀ - 1 / 8 := min_le_left _ _
      have hstep : min (t₀ - 1 / 8) (1 / 4 - t₀) / 2 < t₀ - 1 / 8 := by
        linarith [ht₀.1, ht₀.2]
      linarith
    have hright : t₀ + eps_t < 1 / 4 := by
      dsimp [eps_t]
      have hmin_le : min (t₀ - 1 / 8) (1 / 4 - t₀) ≤ 1 / 4 - t₀ := min_le_right _ _
      have hstep : min (t₀ - 1 / 8) (1 / 4 - t₀) / 2 < 1 / 4 - t₀ := by
        linarith [ht₀.1, ht₀.2]
      linarith
    constructor <;> linarith
  let α : ℝ := AffineMap.lineMap
    (positiveAxisKeyholeUpperAngle R ε)
    (positiveAxisKeyholeLowerAngle R ε)
    (8 * p.1 - 1)
  have hparam : 8 * p.1 - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp₁_branch.1, hp₁_branch.2]
  have hα :
      α ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
    have hseg :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε)
          hparam
    have hneq :
        positiveAxisKeyholeUpperAngle R ε ≠ positiveAxisKeyholeLowerAngle R ε := ne_of_lt horder.1
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    simpa [α, min_eq_left (le_of_lt horder.1), max_eq_right (le_of_lt horder.1)] using hseg
  constructor
  · intro hp₂_neg hz
    have hρ_pos : 0 < ε + p.2 := by
      have hneg : -eps_u < p.2 := (abs_lt.mp hp₂η).1
      have hepsu_le : eps_u ≤ ε / 2 := min_le_left _ _
      linarith
    have hρ_lt : ε + p.2 < ε := by
      linarith
    have hz_norm : ε ≤ ε + p.2 := by
      simpa [α, norm_circleMap_zero, abs_of_pos hρ_pos] using hz.1.1
    exact (not_le_of_gt hρ_lt) hz_norm
  · intro hp₂_pos
    have hρ : ε + p.2 ∈ Set.Ioo ε R := by
      constructor
      · linarith
      · linarith [hε_plus, (abs_lt.mp hp₂η).2]
    simpa [α] using
      positiveAxisWedgeAnnulus_circleMap_mem_interior_of_majorArc R ε (ε + p.2) hε hεR hρ hα

/-- Helper for Remark III.6-extra-7: near an interior point of the outer circular branch, moving
inward enters the wedge-annulus interior while moving outward exits through the outer boundary. -/
private lemma positiveAxisOuterArcChartSideOfAnnulus
    {R ε t₀ : ℝ} (hε : 0 < ε) (hεR : ε < R) (ht₀ : t₀ ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let α := AffineMap.lineMap
        (positiveAxisKeyholeLowerAngle R ε)
        (positiveAxisKeyholeUpperAngle R ε)
        (2 * p.1 - 1)
      let z := circleMap 0 (R - p.2) α
      (p.2 < 0 → z ∉ positiveAxisWedgeAnnulus R ε) ∧
        (0 < p.2 → z ∈ interior (positiveAxisWedgeAnnulus R ε)) := by
  let eps_t : ℝ := min (t₀ - 1 / 2) (1 - t₀) / 2
  let eps_u : ℝ := (R - ε) / 2
  let η : ℝ := min eps_t eps_u
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  have hεt_pos : 0 < eps_t := by
    dsimp [eps_t]
    have hleft : 0 < t₀ - 1 / 2 := sub_pos.mpr ht₀.1
    have hright : 0 < 1 - t₀ := sub_pos.mpr ht₀.2
    have hmin : 0 < min (t₀ - 1 / 2) (1 - t₀) := lt_min hleft hright
    linarith
  have hεu_pos : 0 < eps_u := by
    dsimp [eps_u]
    linarith
  have hη_pos : 0 < η := lt_min hεt_pos hεu_pos
  have hε_minus : ε < R - eps_u := by
    dsimp [eps_u]
    linarith
  refine ⟨η, hη_pos, ?_⟩
  intro p hp₁ hp₂
  have hp₂η : |p.2| < eps_u := lt_of_lt_of_le hp₂ (min_le_right _ _)
  have hp₁_branch : p.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := by
    have hp₁η : |p.1 - t₀| < eps_t := lt_of_lt_of_le hp₁ (min_le_left _ _)
    have hp₁_lower : -eps_t < p.1 - t₀ := (abs_lt.mp hp₁η).1
    have hp₁_upper : p.1 - t₀ < eps_t := (abs_lt.mp hp₁η).2
    have hleft : 1 / 2 < t₀ - eps_t := by
      dsimp [eps_t]
      have hmin_le : min (t₀ - 1 / 2) (1 - t₀) ≤ t₀ - 1 / 2 := min_le_left _ _
      have hstep : min (t₀ - 1 / 2) (1 - t₀) / 2 < t₀ - 1 / 2 := by
        linarith [ht₀.1, ht₀.2]
      linarith
    have hright : t₀ + eps_t < 1 := by
      dsimp [eps_t]
      have hmin_le : min (t₀ - 1 / 2) (1 - t₀) ≤ 1 - t₀ := min_le_right _ _
      have hstep : min (t₀ - 1 / 2) (1 - t₀) / 2 < 1 - t₀ := by
        linarith [ht₀.1, ht₀.2]
      linarith
    constructor <;> linarith
  let α : ℝ := AffineMap.lineMap
    (positiveAxisKeyholeLowerAngle R ε)
    (positiveAxisKeyholeUpperAngle R ε)
    (2 * p.1 - 1)
  have hparam : 2 * p.1 - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp₁_branch.1, hp₁_branch.2]
  have hα :
      α ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
    have hseg :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε)
          hparam
    have hneq :
        positiveAxisKeyholeLowerAngle R ε ≠ positiveAxisKeyholeUpperAngle R ε := by
      exact ne_of_gt horder.1
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    simpa [α, min_eq_right (le_of_lt horder.1), max_eq_left (le_of_lt horder.1)] using hseg
  constructor
  · intro hp₂_neg hz
    have hρ_pos : 0 < R - p.2 := by
      linarith [hεR, hε, (abs_lt.mp hp₂η).1]
    have hρ_gt : R < R - p.2 := by
      linarith
    have hz_norm : R - p.2 ≤ R := by
      simpa [α, norm_circleMap_zero, abs_of_pos hρ_pos] using hz.1.2
    exact (not_le_of_gt hρ_gt) hz_norm
  · intro hp₂_pos
    have hρ : R - p.2 ∈ Set.Ioo ε R := by
      constructor
      · linarith [hε_minus, (abs_lt.mp hp₂η).2]
      · linarith
    simpa [α] using
      positiveAxisWedgeAnnulus_circleMap_mem_interior_of_majorArc R ε (R - p.2) hε hεR hρ hα

/-- Helper for Remark III.6-extra-7: every regular point on one of the two circular keyhole arcs
admits a local boundary-straightening chart. -/
theorem positiveAxisKeyhole_circle_branch_exists_boundary_chart
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hbranch : t₀ ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨ t₀ ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (positiveAxisWedgeAnnulus R ε)
        ((positiveAxisKeyhole R ε).toClosedPath.realCurve) t₀ δ :=
by
  -- Route correction: the circle branch now follows the same radial-tube packaging as the sibling
  -- keyhole proof, with the positive-axis owner handled by explicit major-arc side lemmas.
  rcases hbranch with htinner | htouter
  · let eps_t₀ : ℝ := min (t₀ - 1 / 8) (1 / 4 - t₀) / 2
    have hεt₀_pos : 0 < eps_t₀ := by
      dsimp [eps_t₀]
      have hleft : 0 < t₀ - 1 / 8 := sub_pos.mpr htinner.1
      have hright : 0 < 1 / 4 - t₀ := sub_pos.mpr htinner.2
      have hmin : 0 < min (t₀ - 1 / 8) (1 / 4 - t₀) := lt_min hleft hright
      linarith
    have hstrip₀ :
        Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) ⊆ Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ) := by
      intro t ht
      have hleft : 0 < t₀ - 1 / 8 := sub_pos.mpr htinner.1
      have hright : 0 < 1 / 4 - t₀ := sub_pos.mpr htinner.2
      have hmin_left : min (t₀ - 1 / 8) (1 / 4 - t₀) / 2 < t₀ - 1 / 8 := by
        have hmin_le : min (t₀ - 1 / 8) (1 / 4 - t₀) ≤ t₀ - 1 / 8 := min_le_left _ _
        linarith
      have hmin_right : min (t₀ - 1 / 8) (1 / 4 - t₀) / 2 < 1 / 4 - t₀ := by
        have hmin_le : min (t₀ - 1 / 8) (1 / 4 - t₀) ≤ 1 / 4 - t₀ := min_le_right _ _
        linarith
      constructor
      · have h18 : 1 / 8 < t₀ - eps_t₀ := by
          dsimp [eps_t₀]
          linarith
        exact lt_trans h18 ht.1
      · have h14 : t₀ + eps_t₀ < 1 / 4 := by
          dsimp [eps_t₀]
          linarith
        exact lt_trans ht.2 h14
    rcases positiveAxisInnerArcChartSideOfAnnulus hε hεR htinner with ⟨η, hη, hside⟩
    let eps_t : ℝ := min eps_t₀ η
    have hεt_pos : 0 < eps_t := lt_min hεt₀_pos hη
    have hstrip_param_branch :
        Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ) := by
      intro t ht
      have ht' : t ∈ Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) := by
        constructor <;> linarith [ht.1, ht.2, min_le_left eps_t₀ η]
      exact hstrip₀ ht'
    have hstrip_param :
        Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro t ht
      have ht' := hstrip_param_branch ht
      exact ⟨lt_trans (by norm_num) ht'.1, lt_trans ht'.2 (by norm_num)⟩
    let upper : ℝ := positiveAxisKeyholeUpperAngle R ε
    let lower : ℝ := positiveAxisKeyholeLowerAngle R ε
    let θ : ℝ → ℝ := fun t ↦ AffineMap.lineMap upper lower (8 * t - 1)
    let γ : ℝ → ℂ := fun t ↦ circleMap 0 ε (θ t)
    let n : ℝ → ℂ := fun t ↦ Complex.exp (θ t * Complex.I)
    let c : ℝ := 8 * (upper - lower) * ε
    let tangent : ℂ :=
      (8 * (lower - upper)) • (circleMap 0 ε (θ t₀) * Complex.I)
    have hθCont : ContDiffAt ℝ 1 θ t₀ := by
      -- The inner-arc angle is affine in the contour parameter.
      have hθ :
          ContDiff ℝ 1
            (fun t : ℝ ↦ upper + (8 * t - 1) * (lower - upper)) := by
        fun_prop
      simpa [θ, upper, lower, AffineMap.lineMap_apply_module, sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
        hθ.contDiffAt
    have hγCont : ContDiffAt ℝ 1 γ t₀ := by
      -- The inner circular branch is smooth after composing `circleMap` with that affine angle.
      simpa [γ] using (contDiff_circleMap 0 ε).contDiffAt.comp t₀ hθCont
    have hnCont : ContDiffAt ℝ 1 n t₀ := by
      -- The outward radial unit field varies smoothly along the inner major arc.
      have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
        simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
      have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
        simpa [one_mul] using hθComplex.mul contDiffAt_const
      simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner)
    have hθDeriv :
        HasDerivAt θ (8 * (lower - upper)) t₀ := by
      -- Differentiate the affine angle before differentiating the circle branch.
      have hθFormula :
          θ = fun t : ℝ ↦ upper + (8 * t - 1) * (lower - upper) := by
        ext t
        rw [show θ t = AffineMap.lineMap upper lower (8 * t - 1) by rfl]
        rw [AffineMap.lineMap_apply_module]
        change (1 - (8 * t - 1)) * upper + (8 * t - 1) * lower =
            upper + (8 * t - 1) * (lower - upper)
        nlinarith
      have hθDerivRaw :
          HasDerivAt
            (fun t : ℝ ↦ upper + (8 * t - 1) * (lower - upper))
            (8 * (lower - upper)) t₀ := by
        convert
          (AffineMap.hasDerivAt_lineMap
            (a := upper) (b := lower) (x := (8 : ℝ) * t₀ - 1)).comp t₀
            (((hasDerivAt_id t₀).const_mul 8).sub_const 1) using 1
        · ext t
          simp [AffineMap.lineMap_apply_module]
          ring
        · ring
      simpa [hθFormula] using hθDerivRaw
    have hγDeriv : HasDerivAt γ tangent t₀ := by
      -- The inner arc differentiates to the explicit tangent used by the frame normalization.
      convert (hasDerivAt_circleMap 0 ε (θ t₀)).scomp t₀ hθDeriv using 1
    have htangent_formula :
        tangent = ((((-c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
      -- Rewrite the tangent in the normalized exponential form expected by the frame lemma.
      calc
        tangent = ((((8 * (lower - upper) * ε : ℝ) : ℂ) * Complex.I) *
            Complex.exp (θ t₀ * Complex.I)) := by
              simp [tangent, θ, circleMap, zero_add, smul_eq_mul]
              ring
        _ = ((((-c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
              simp [c]
              ring
    have hc : c ≠ 0 := by
      have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      dsimp [c, upper, lower]
      nlinarith [hε, horder.1]
    have hv : Complex.equivRealProd tangent ≠ 0 := by
      -- The inner circular tangent is nonzero because both its scalar and exponential factors are
      -- nonzero.
      intro hv0
      have htangent : tangent = 0 := Complex.equivRealProd.injective hv0
      rw [htangent_formula] at htangent
      have hscale : ((((-c : ℝ) : ℂ) * Complex.I) : ℂ) ≠ 0 := by
        exact mul_ne_zero (by simpa using hc) Complex.I_ne_zero
      have hmul :
          (((-c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) = 0 := by
        simpa using htangent
      exact Complex.exp_ne_zero (θ t₀ * Complex.I) ((mul_eq_zero.mp hmul).resolve_left hscale)
    have hrot :
        rot90 (Complex.equivRealProd tangent) = c • Complex.equivRealProd (n t₀) := by
      -- Quarter-turning the tangent points in the outward radial direction on the inner circle.
      rw [htangent_formula]
      simpa [n, c] using
        (positiveAxis_circleMap_rot90_tangent_eq_scaled_radial (c := -c) (θ := θ t₀))
    refine positiveAxisRadialBoundaryStripChartExists
      (K := positiveAxisWedgeAnnulus R ε)
      (curve := ((positiveAxisKeyhole R ε).toClosedPath.realCurve))
      (γ := γ) (n := n) (t₀ := t₀) (eps_t := eps_t) (eps_u := η) (c := c)
      (tangent := tangent) ht₀ hεt_pos hη hstrip_param
      hγCont hnCont hγDeriv hv hrot hc ?_ ?_
    · intro t ht
      have htBranch : t ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ) := hstrip_param_branch ht
      have htIcc : t ∈ Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
      -- On the horizontal axis, the radial chart recovers the inner circular branch exactly.
      apply Complex.equivRealProdCLM.symm.injective
      calc
        Complex.equivRealProdCLM.symm (((positiveAxisKeyhole R ε).toClosedPath.realCurve) t) =
            (positiveAxisKeyhole R ε).extend t := by
              rw [positiveAxis_toClosedPath_realCurve_eq, Function.comp_apply,
                Complex.equivRealProdCLM_symm_apply]
              exact Complex.re_add_im ((positiveAxisKeyhole R ε).extend t)
        _ = circleMap 0 ε (θ t) := by
              simpa [γ, θ] using positive_axis_keyhole_eq_on_inner_arc R ε htIcc
        _ = Complex.equivRealProdCLM.symm (Complex.equivRealProd (γ t)) := by
              rw [Complex.equivRealProdCLM_symm_apply]
              simpa [γ] using (Complex.re_add_im (γ t)).symm
    · intro p hp₁ hp₂
      -- The inner-arc side lemma already matches the radial tube after the radius-add rewrite.
      simpa [γ, n, θ, positiveAxisInnerArc_add_real_mul_radial_eq_circleMap_radius_add] using
        (hside (p := p) (lt_of_lt_of_le hp₁ (min_le_right _ _)) hp₂)
  · let eps_t₀ : ℝ := min (t₀ - 1 / 2) (1 - t₀) / 2
    have hεt₀_pos : 0 < eps_t₀ := by
      dsimp [eps_t₀]
      have hleft : 0 < t₀ - 1 / 2 := sub_pos.mpr htouter.1
      have hright : 0 < 1 - t₀ := sub_pos.mpr htouter.2
      have hmin : 0 < min (t₀ - 1 / 2) (1 - t₀) := lt_min hleft hright
      linarith
    have hstrip₀ :
        Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) ⊆ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := by
      intro t ht
      have hleft : 0 < t₀ - 1 / 2 := sub_pos.mpr htouter.1
      have hright : 0 < 1 - t₀ := sub_pos.mpr htouter.2
      have hmin_left : min (t₀ - 1 / 2) (1 - t₀) / 2 < t₀ - 1 / 2 := by
        have hmin_le : min (t₀ - 1 / 2) (1 - t₀) ≤ t₀ - 1 / 2 := min_le_left _ _
        linarith
      have hmin_right : min (t₀ - 1 / 2) (1 - t₀) / 2 < 1 - t₀ := by
        have hmin_le : min (t₀ - 1 / 2) (1 - t₀) ≤ 1 - t₀ := min_le_right _ _
        linarith
      constructor
      · have h12 : 1 / 2 < t₀ - eps_t₀ := by
          dsimp [eps_t₀]
          linarith
        exact lt_trans h12 ht.1
      · have h1 : t₀ + eps_t₀ < 1 := by
          dsimp [eps_t₀]
          linarith
        exact lt_trans ht.2 h1
    rcases positiveAxisOuterArcChartSideOfAnnulus hε hεR htouter with ⟨η, hη, hside⟩
    let eps_t : ℝ := min eps_t₀ η
    have hεt_pos : 0 < eps_t := lt_min hεt₀_pos hη
    have hstrip_param_branch :
        Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := by
      intro t ht
      have ht' : t ∈ Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) := by
        constructor <;> linarith [ht.1, ht.2, min_le_left eps_t₀ η]
      exact hstrip₀ ht'
    have hstrip_param :
        Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro t ht
      have ht' := hstrip_param_branch ht
      exact ⟨lt_trans (by norm_num) ht'.1, ht'.2⟩
    let upper : ℝ := positiveAxisKeyholeUpperAngle R ε
    let lower : ℝ := positiveAxisKeyholeLowerAngle R ε
    let θ : ℝ → ℝ := fun t ↦ AffineMap.lineMap lower upper (2 * t - 1)
    let γ : ℝ → ℂ := fun t ↦ circleMap 0 R (θ t)
    let n : ℝ → ℂ := fun t ↦ -Complex.exp (θ t * Complex.I)
    let c : ℝ := 2 * (upper - lower) * R
    let tangent : ℂ :=
      (2 * (upper - lower)) • (circleMap 0 R (θ t₀) * Complex.I)
    have hR : 0 < R := lt_trans hε hεR
    have hθCont : ContDiffAt ℝ 1 θ t₀ := by
      -- The outer-arc angle is affine in the contour parameter.
      have hθ :
          ContDiff ℝ 1
            (fun t : ℝ ↦ lower + (2 * t - 1) * (upper - lower)) := by
        fun_prop
      simpa [θ, upper, lower, AffineMap.lineMap_apply_module, sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
        hθ.contDiffAt
    have hγCont : ContDiffAt ℝ 1 γ t₀ := by
      -- The outer circular branch is smooth after composing `circleMap` with that affine angle.
      simpa [γ] using (contDiff_circleMap 0 R).contDiffAt.comp t₀ hθCont
    have hnCont : ContDiffAt ℝ 1 n t₀ := by
      -- The inward radial unit field varies smoothly along the outer major arc.
      have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
        simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
      have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
        simpa [one_mul] using hθComplex.mul contDiffAt_const
      simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner).neg
    have hθDeriv :
        HasDerivAt θ (2 * (upper - lower)) t₀ := by
      -- Differentiate the affine angle interpolation before differentiating the outer circle.
      have hθFormula :
          θ = fun t : ℝ ↦ lower + (2 * t - 1) * (upper - lower) := by
        ext t
        rw [show θ t = AffineMap.lineMap lower upper (2 * t - 1) by rfl]
        rw [AffineMap.lineMap_apply_module]
        change (1 - (2 * t - 1)) * lower + (2 * t - 1) * upper =
            lower + (2 * t - 1) * (upper - lower)
        nlinarith
      have hθDerivRaw :
          HasDerivAt
            (fun t : ℝ ↦ lower + (2 * t - 1) * (upper - lower))
            (2 * (upper - lower)) t₀ := by
        convert
          (AffineMap.hasDerivAt_lineMap
            (a := lower) (b := upper) (x := (2 : ℝ) * t₀ - 1)).comp t₀
            (((hasDerivAt_id t₀).const_mul 2).sub_const 1) using 1
        · ext t
          simp [AffineMap.lineMap_apply_module]
          ring
        · ring
      simpa [hθFormula] using hθDerivRaw
    have hγDeriv : HasDerivAt γ tangent t₀ := by
      -- The outer arc differentiates to the explicit tangent used by the frame normalization.
      convert (hasDerivAt_circleMap 0 R (θ t₀)).scomp t₀ hθDeriv using 1
    have htangent_formula :
        tangent = ((((c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
      -- Rewrite the tangent in the exponential form used by the frame normalization.
      calc
        tangent = ((((2 * (upper - lower) * R : ℝ) : ℂ) * Complex.I) *
            Complex.exp (θ t₀ * Complex.I)) := by
              simp [tangent, θ, circleMap, zero_add, smul_eq_mul]
              ring
        _ = ((((c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
              simp [c]
    have hc : c ≠ 0 := by
      have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      dsimp [c, upper, lower]
      nlinarith [hR, horder.1]
    have hv : Complex.equivRealProd tangent ≠ 0 := by
      -- The outer circular tangent is nonzero for the same reason as the inner one.
      intro hv0
      have htangent : tangent = 0 := Complex.equivRealProd.injective hv0
      rw [htangent_formula] at htangent
      have hscale : ((((c : ℝ) : ℂ) * Complex.I) : ℂ) ≠ 0 := by
        exact mul_ne_zero (by simpa using hc) Complex.I_ne_zero
      have hmul :
          (((c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) = 0 := by
        simpa using htangent
      exact Complex.exp_ne_zero (θ t₀ * Complex.I) ((mul_eq_zero.mp hmul).resolve_left hscale)
    have hrot :
        rot90 (Complex.equivRealProd tangent) = c • Complex.equivRealProd (n t₀) := by
      -- Quarter-turning the tangent points in the inward radial direction on the outer circle.
      rw [htangent_formula]
      calc
        rot90
            (Complex.equivRealProd
              ((((c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I))) =
            (-c) • Complex.equivRealProd (Complex.exp (θ t₀ * Complex.I)) := by
              simpa using
                (positiveAxis_circleMap_rot90_tangent_eq_scaled_radial (c := c) (θ := θ t₀))
        _ = c • Complex.equivRealProd (n t₀) := by
              let w : Plane := Complex.equivRealProd (Complex.exp (θ t₀ * Complex.I))
              have hw : (-c) • w = c • (-w) := by
                simp [w]
              simpa [w, n] using hw
    refine positiveAxisRadialBoundaryStripChartExists
      (K := positiveAxisWedgeAnnulus R ε)
      (curve := ((positiveAxisKeyhole R ε).toClosedPath.realCurve))
      (γ := γ) (n := n) (t₀ := t₀) (eps_t := eps_t) (eps_u := η) (c := c)
      (tangent := tangent) ht₀ hεt_pos hη hstrip_param
      hγCont hnCont hγDeriv hv hrot hc ?_ ?_
    · intro t ht
      have htBranch : t ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := hstrip_param_branch ht
      have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) (1 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
      -- On the horizontal axis, the radial chart recovers the outer circular branch exactly.
      apply Complex.equivRealProdCLM.symm.injective
      calc
        Complex.equivRealProdCLM.symm (((positiveAxisKeyhole R ε).toClosedPath.realCurve) t) =
            (positiveAxisKeyhole R ε).extend t := by
              rw [positiveAxis_toClosedPath_realCurve_eq, Function.comp_apply,
                Complex.equivRealProdCLM_symm_apply]
              exact Complex.re_add_im ((positiveAxisKeyhole R ε).extend t)
        _ = circleMap 0 R (θ t) := by
              simpa [γ, θ] using positive_axis_keyhole_eq_on_outer_arc R ε htIcc
        _ = Complex.equivRealProdCLM.symm (Complex.equivRealProd (γ t)) := by
              rw [Complex.equivRealProdCLM_symm_apply]
              simpa [γ] using (Complex.re_add_im (γ t)).symm
    · intro p hp₁ hp₂
      -- The outer-arc side lemma already matches the radial tube after the radius-sub rewrite.
      let α : ℝ := AffineMap.lineMap
        lower
        upper
        (2 * p.1 - 1)
      have hside' :
          (p.2 < 0 →
            circleMap 0 (R - p.2) α ∉ positiveAxisWedgeAnnulus R ε) ∧
          (0 < p.2 →
            circleMap 0 (R - p.2) α ∈ interior (positiveAxisWedgeAnnulus R ε)) := by
        simpa [α] using hside (p := p) (lt_of_lt_of_le hp₁ (min_le_right _ _)) hp₂
      have hrewrite :
          circleMap 0 R α + (p.2 : ℂ) * (-Complex.exp (α * Complex.I)) =
            circleMap 0 (R - p.2) α := by
        simpa [α] using
          positiveAxisOuterArc_add_real_mul_inward_eq_circleMap_radius_sub R α p.2
      dsimp [γ, n, θ]
      simpa only [α, smul_eq_mul, hrewrite] using hside'
