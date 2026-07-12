import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisWedgeAnnulus

open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: strict annulus bounds together with a negative real part put
a point in the interior of the positive-axis wedge-annulus, because the removed wedge lies
entirely in the positive half-plane. -/
lemma positiveAxisWedgeAnnulus_mem_interior_of_neg_re
    {R ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzR : ‖z‖ < R) (hzre : z.re < 0) :
    z ∈ interior (positiveAxisWedgeAnnulus R ε) := by
  let U : Set ℂ := {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R ∧ w.re < 0}
  have hU_open : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_norm).inter <|
      (isOpen_lt continuous_norm continuous_const).inter ?_
    simpa using isOpen_lt Complex.continuous_re continuous_const
  have hzU : z ∈ U := ⟨hεz, hzR, hzre⟩
  refine mem_interior.mpr ⟨U, ?_, hU_open, hzU⟩
  intro w hw
  refine ⟨⟨le_of_lt hw.1, le_of_lt hw.2.1⟩, ?_⟩
  intro hwedge
  exact not_lt_of_ge hw.2.2.le hwedge.1

/-- Helper for Remark III.6-extra-7: on the upper slit-lip side, membership in the wedge-annulus
is exactly the nonnegativity of the signed vertical gap above the upper wedge boundary line. -/
private lemma positiveAxisWedgeAnnulus_mem_iff_upper_signed_height_nonneg
    {R ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzR : ‖z‖ < R) (hzre : 0 < z.re) (hzim : 0 < z.im) :
    z ∈ positiveAxisWedgeAnnulus R ε ↔ 0 ≤ z.im - (ε / R) * z.re := by
  constructor
  · intro hz
    have hnot_gap : ¬ z.im < (ε / R) * z.re := by
      -- On the upper side, a strict inequality would put `z` back inside the removed wedge.
      intro hlt
      exact hz.2 ⟨hzre, by simpa [abs_of_pos hzim] using hlt⟩
    exact sub_nonneg.mpr (le_of_not_gt hnot_gap)
  · intro hgap
    refine ⟨⟨le_of_lt hεz, le_of_lt hzR⟩, ?_⟩
    intro hzWedge
    -- The signed-height hypothesis rules out the strict wedge inequality.
    have hlt : z.im < (ε / R) * z.re := by
      simpa [abs_of_pos hzim] using hzWedge.2
    linarith

/-- Helper for Remark III.6-extra-7: on the lower slit-lip side, membership in the wedge-annulus
is exactly the nonnegativity of the reflected gap below the lower wedge boundary line. -/
private lemma positiveAxisWedgeAnnulus_mem_iff_lower_signed_height_nonneg
    {R ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzR : ‖z‖ < R) (hzre : 0 < z.re) (hzim : z.im < 0) :
    z ∈ positiveAxisWedgeAnnulus R ε ↔ 0 ≤ -z.im - (ε / R) * z.re := by
  constructor
  · intro hz
    have hnot_gap : ¬ -z.im < (ε / R) * z.re := by
      -- On the lower side, the reflected signed height must stay nonnegative on the boundary
      -- owner.
      intro hlt
      exact hz.2 ⟨hzre, by simpa [abs_of_neg hzim] using hlt⟩
    linarith
  · intro hgap
    refine ⟨⟨le_of_lt hεz, le_of_lt hzR⟩, ?_⟩
    intro hzWedge
    have hlt : -z.im < (ε / R) * z.re := by
      simpa [abs_of_neg hzim] using hzWedge.2
    linarith

/-- Helper for Remark III.6-extra-7: strict annulus bounds together with a strictly positive upper
signed height put a point in the interior of the wedge-annulus. -/
lemma positiveAxisWedgeAnnulus_mem_interior_of_upper_gap
    {R ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzR : ‖z‖ < R) (hzim : 0 < z.im)
    (hgap : 0 < z.im - (ε / R) * z.re) :
    z ∈ interior (positiveAxisWedgeAnnulus R ε) := by
  let U : Set ℂ := {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R ∧ 0 < w.im ∧ 0 < w.im - (ε / R) * w.re}
  have hU_open : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_norm).inter <|
      (isOpen_lt continuous_norm continuous_const).inter <|
        (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    simpa using
      isOpen_lt continuous_const (Complex.continuous_im.sub (continuous_const.mul Complex.continuous_re))
  have hzU : z ∈ U := ⟨hεz, hzR, hzim, hgap⟩
  refine mem_interior.mpr ⟨U, ?_, hU_open, hzU⟩
  intro w hw
  refine ⟨⟨le_of_lt hw.1, le_of_lt hw.2.1⟩, ?_⟩
  intro hwedge
  have hw_im_lt : w.im < (ε / R) * w.re := by
    simpa [abs_of_pos hw.2.2.1] using hwedge.2
  have hw_gap_pos : 0 < w.im - (ε / R) * w.re := hw.2.2.2
  linarith

/-- Helper for Remark III.6-extra-7: strict annulus bounds together with a strictly positive lower
signed height put a point in the interior of the wedge-annulus. -/
lemma positiveAxisWedgeAnnulus_mem_interior_of_lower_gap
    {R ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzR : ‖z‖ < R) (hzim : z.im < 0)
    (hgap : 0 < -z.im - (ε / R) * z.re) :
    z ∈ interior (positiveAxisWedgeAnnulus R ε) := by
  let U : Set ℂ := {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R ∧ w.im < 0 ∧ 0 < -w.im - (ε / R) * w.re}
  have hU_open : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_norm).inter <|
      (isOpen_lt continuous_norm continuous_const).inter <|
        (isOpen_lt Complex.continuous_im continuous_const).inter ?_
    simpa using
      isOpen_lt continuous_const (Complex.continuous_im.neg.sub (continuous_const.mul Complex.continuous_re))
  have hzU : z ∈ U := ⟨hεz, hzR, hzim, hgap⟩
  refine mem_interior.mpr ⟨U, ?_, hU_open, hzU⟩
  intro w hw
  refine ⟨⟨le_of_lt hw.1, le_of_lt hw.2.1⟩, ?_⟩
  intro hwedge
  have hw_im_lt : -w.im < (ε / R) * w.re := by
    simpa [abs_of_neg hw.2.2.1] using hwedge.2
  have hw_gap_pos : 0 < -w.im - (ε / R) * w.re := hw.2.2.2
  linarith

/-- Helper for Remark III.6-extra-7: the transverse coefficient relating strip height to signed
distance from either slit lip is positive. -/
private lemma positiveAxis_lip_transverse_coefficient_pos
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    0 <
      Real.cos (positiveAxisKeyholeAngle R ε) +
        (ε / R) * Real.sin (positiveAxisKeyholeAngle R ε) := by
  have hR : 0 < R := lt_trans hε hεR
  rw [positiveAxisKeyholeAngle, Real.sin_arctan, Real.cos_arctan]
  have hden : 0 < Real.sqrt (1 + (ε / R) ^ 2) := by positivity
  field_simp [hden.ne']
  nlinarith

/-- Helper for Remark III.6-extra-7: unpacking a loop through `toClosedPath.realCurve` only
rewrites the original loop extension into real coordinates. -/
lemma positiveAxis_toClosedPath_realCurve_eq {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.realCurve = Complex.equivRealProd ∘ γ.extend := by
  -- The closed-path wrapper adds no new geometry for a genuine loop.
  cases γ
  rfl

/-- Helper for Remark III.6-extra-7: a `C¹` radial tube has the expected tangent and transverse
derivative columns at the base point. -/
lemma positiveAxis_radialTube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
    (hγCont : ContDiffAt ℝ 1 γ t₀) (hγDeriv : HasDerivAt γ v t₀)
    (hnCont : ContDiffAt ℝ 1 n t₀) :
    ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1 + p.2 • n p.1) (t₀, 0) ∧
      HasFDerivAt (fun p : Plane ↦ γ p.1 + p.2 • n p.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))
        (t₀, 0) := by
  constructor
  · -- The tube map is the sum of the branch and the varying transverse direction.
    have hγfst : ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1) (t₀, 0) := by
      simpa using hγCont.comp (x := (t₀, 0)) contDiffAt_fst
    have hnfst : ContDiffAt ℝ 1 (fun p : Plane ↦ n p.1) (t₀, 0) := by
      simpa using hnCont.comp (x := (t₀, 0)) contDiffAt_fst
    simpa using hγfst.add (contDiffAt_snd.smul hnfst)
  · -- At `p.2 = 0`, the transverse derivative contributes only the actual normal vector.
    have hγfst :
        HasFDerivAt (fun p : Plane ↦ γ p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        hγDeriv.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hnfst :
        HasFDerivAt (fun p : Plane ↦ n p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv n t₀)) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        (hnCont.differentiableAt one_ne_zero).hasDerivAt.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hsnd :
        HasFDerivAt (fun p : Plane ↦ p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, (0 : ℝ)) := by
      simpa using
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    simpa [ContinuousLinearMap.smulRight_apply] using hγfst.add (hsnd.smul hnfst)

/-- Helper for Remark III.6-extra-7: rescaling the second plane coordinate by a nonzero real
factor is a continuous linear automorphism. -/
noncomputable def positiveAxis_planeSecondRescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
  { toLinearEquiv :=
      { toFun := fun p ↦ (p.1, p.2 / c)
        invFun := fun p ↦ (p.1, c * p.2)
        left_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        right_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        map_add' := by
          intro p q
          ext <;> simp [div_eq_mul_inv, add_mul]
        map_smul' := by
          intro s p
          ext <;> simp [div_eq_mul_inv, mul_assoc] }
    continuous_toFun := by
      fun_prop
    continuous_invFun := by
      fun_prop }

/-- Helper for Remark III.6-extra-7: once an explicit affine strip chart already has the
horizontal-axis branch formula and the signed side test, restricting that affine equivalence to a
small strip packages the data into an `IsBoundaryStraighteningAt` chart. -/
private lemma positiveAxisAffineBoundaryStripChartExists
    {K : Set ℂ} {γ : ℝ → Plane} {t₀ eps_t eps_u : ℝ}
    (e : Plane ≃ᴬ[ℝ] Plane)
    (hεt_pos : 0 < eps_t) (hεu_pos : 0 < eps_u)
    (hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1)
    (hmap_axis :
      ∀ {t : ℝ}, t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) → e (t, 0) = γ t)
    (hstrip_side :
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 → Complex.equivRealProdCLM.symm (e (t, u)) ∉ K) ∧
          (0 < u → Complex.equivRealProdCLM.symm (e (t, u)) ∈ interior K)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt K γ t₀ δ := by
  let δ₀ : OpenPartialHomeomorph Plane Plane := e.toHomeomorph.toOpenPartialHomeomorph
  let strip : Set Plane := Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ×ˢ Set.Ioo (-eps_u) eps_u
  let δ : OpenPartialHomeomorph Plane Plane := δ₀.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
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
  · -- The centered strip contains the base parameter and the horizontal axis point.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, δ₀, strip] using hstrip
  · intro p hp
    -- Any source point keeps its first coordinate inside the ambient contour interval.
    have hpStrip : p ∈ strip := by
      simpa [δ, δ₀, strip] using hp
    exact ⟨hstrip_param hpStrip.1, Set.mem_univ _⟩
  · -- Restricting an affine equivalence preserves the `C¹` regularity on the source.
    simpa [δ, δ₀, strip] using e.toContinuousAffineMap.contDiff.contDiffOn
  · -- The inverse affine map stays `C¹` on the restricted target for the same reason.
    simpa [δ, δ₀, strip] using e.symm.toContinuousAffineMap.contDiff.contDiffOn
  · intro t ht
    -- Along the horizontal axis, the restricted chart recovers the prescribed boundary branch.
    have htStrip : (t, 0) ∈ strip := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, δ, δ₀, strip] using ht
    simpa [δ, δ₀] using hmap_axis htStrip.1
  · -- The curve image is exactly the horizontal axis in the restricted source strip.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htStrip : (t, 0) ∈ strip := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, δ, δ₀, strip] using ht
    simpa [δ, δ₀] using hmap_axis htStrip.1
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      simpa [δ, δ₀, strip] using hp.1
    exact (hstrip_side hpStrip.1 hpStrip.2).1 hp.2 hx.2
  · intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      simpa [δ, δ₀, strip] using hp.1
    exact (hstrip_side hpStrip.1 hpStrip.2).2 hp.2

/-- Helper for Remark III.6-extra-7: rotating plane coordinates by `θ` is multiplication by
`exp (θ i)` after identifying `Plane` with `ℂ`. -/
private noncomputable def positiveAxisPlaneRotation (θ : ℝ) : Plane ≃ᴬ[ℝ] Plane :=
  let c : ℂˣ := Units.mk0 (Complex.exp (θ * Complex.I)) (Complex.exp_ne_zero _)
  (((Complex.equivRealProdCLM.symm.trans (ContinuousLinearEquiv.smulLeft c)).trans
      Complex.equivRealProdCLM)).toContinuousAffineEquiv

/-- Helper for Remark III.6-extra-7: reflecting the second plane coordinate flips the transverse
direction while keeping the tangential coordinate fixed. -/
private noncomputable def positiveAxisPlaneFlipSecond : Plane ≃ᴬ[ℝ] Plane :=
  let m : ℝˣ := ⟨-1, -1, by ring, by ring⟩
  (ContinuousAffineEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv)

/-- Helper for Remark III.6-extra-7: the upper-lip affine chart uses the radial parameter on the
first coordinate and the inward `+π/2` normal on the second coordinate. -/
private noncomputable def positiveAxisUpperLipChart (R ε : ℝ) (hεR : ε < R) :
    Plane ≃ᴬ[ℝ] Plane :=
  let m : ℝˣ := ⟨8 * (ε - R), (8 * (ε - R))⁻¹, by
      have hne : ε - R ≠ 0 := by linarith
      field_simp [hne], by
      have hne : ε - R ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ R)
  (ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)).trans
    (positiveAxisPlaneRotation (positiveAxisKeyholeAngle R ε))

/-- Helper for Remark III.6-extra-7: the lower-lip affine chart uses the reflected second
coordinate so positive strip height points into the owner interior. -/
private noncomputable def positiveAxisLowerLipChart (R ε : ℝ) (hεR : ε < R) :
    Plane ≃ᴬ[ℝ] Plane :=
  let m : ℝˣ := ⟨4 * (R - ε), (4 * (R - ε))⁻¹, by
      have hne : R - ε ≠ 0 := by linarith
      field_simp [hne], by
      have hne : R - ε ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (ε - (R - ε)))
  ((ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)).trans positiveAxisPlaneFlipSecond).trans
    (positiveAxisPlaneRotation (-positiveAxisKeyholeAngle R ε))

/-- Helper for Remark III.6-extra-7: after converting back to `ℂ`, the planar rotation chart is
the simple multiplication by `exp (θ i)`. -/
private lemma positiveAxisPlaneRotation_apply
    (θ : ℝ) (p : Plane) :
    Complex.equivRealProdCLM.symm (positiveAxisPlaneRotation θ p) =
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * Complex.exp (θ * Complex.I) := by
  -- Compute the rotated real and imaginary parts coordinatewise in the complex model.
  apply Complex.equivRealProdCLM.injective
  ext <;> simp [positiveAxisPlaneRotation] <;> ring

/-- Helper for Remark III.6-extra-7: the upper-lip affine chart evaluates to the fixed-angle
radial point plus the inward `+π/2` normal displacement. -/
private lemma positiveAxisUpperLipChart_apply
    (R ε : ℝ) (hεR : ε < R) (p : Plane) :
    Complex.equivRealProdCLM.symm (positiveAxisUpperLipChart R ε hεR p) =
      circleMap 0 (AffineMap.lineMap R ε (8 * p.1)) (positiveAxisKeyholeAngle R ε) +
      (p.2 : ℂ) * circleMap 0 1 (positiveAxisKeyholeAngle R ε + Real.pi / 2) := by
  let m : ℝˣ := ⟨8 * (ε - R), (8 * (ε - R))⁻¹, by
      have hne : ε - R ≠ 0 := by linarith
      field_simp [hne], by
      have hne : ε - R ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ R)
  have hex_apply (x : ℝ) : ex x = 8 * (ε - R) * x + R := by
    change (ContinuousAffineEquiv.constVAdd ℝ ℝ R) ((ContinuousLinearEquiv.unitsEquivAut ℝ m) x) =
      8 * (ε - R) * x + R
    rw [ContinuousLinearEquiv.unitsEquivAut_apply]
    change R + x * (8 * (ε - R)) = 8 * (ε - R) * x + R
    ring
  have hbase :
      Complex.equivRealProdCLM.symm (positiveAxisUpperLipChart R ε hεR p) =
        ((((AffineMap.lineMap R ε (8 * p.1)) : ℂ) + (p.2 : ℂ) * Complex.I) *
          Complex.exp (positiveAxisKeyholeAngle R ε * Complex.I)) := by
    change Complex.equivRealProdCLM.symm
        (positiveAxisPlaneRotation (positiveAxisKeyholeAngle R ε)
          ((ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)) p)) = _
    rw [positiveAxisPlaneRotation_apply]
    simp [ex, hex_apply, AffineMap.lineMap_apply_module]
    ring
  rw [hbase, circleMap, zero_add, circleMap, zero_add]
  rw [show ((((positiveAxisKeyholeAngle R ε + Real.pi / 2 : ℝ) : ℂ) * Complex.I)) =
      positiveAxisKeyholeAngle R ε * Complex.I + (Real.pi / 2 : ℂ) * Complex.I by
        simp [add_mul]]
  rw [Complex.exp_add]
  simp
  ring

/-- Helper for Remark III.6-extra-7: the lower-lip affine chart evaluates to the reflected radial
point plus the inward `-π/2` normal displacement. -/
private lemma positiveAxisLowerLipChart_apply
    (R ε : ℝ) (hεR : ε < R) (p : Plane) :
    Complex.equivRealProdCLM.symm (positiveAxisLowerLipChart R ε hεR p) =
      circleMap 0 (AffineMap.lineMap ε R (4 * p.1 - 1)) (-positiveAxisKeyholeAngle R ε) +
      (p.2 : ℂ) * circleMap 0 1 (-positiveAxisKeyholeAngle R ε - Real.pi / 2) := by
  let m : ℝˣ := ⟨4 * (R - ε), (4 * (R - ε))⁻¹, by
      have hne : R - ε ≠ 0 := by linarith
      field_simp [hne], by
      have hne : R - ε ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (ε - (R - ε)))
  have hex_apply (x : ℝ) : ex x = 4 * (R - ε) * x + (ε - (R - ε)) := by
    change
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (ε - (R - ε)))
          ((ContinuousLinearEquiv.unitsEquivAut ℝ m) x) =
        4 * (R - ε) * x + (ε - (R - ε))
    rw [ContinuousLinearEquiv.unitsEquivAut_apply]
    change (ε - (R - ε)) + x * (4 * (R - ε)) = 4 * (R - ε) * x + (ε - (R - ε))
    ring
  have hbase :
      Complex.equivRealProdCLM.symm (positiveAxisLowerLipChart R ε hεR p) =
        ((((AffineMap.lineMap ε R (4 * p.1 - 1)) : ℂ) - (p.2 : ℂ) * Complex.I) *
          Complex.exp ((-positiveAxisKeyholeAngle R ε) * Complex.I)) := by
    change Complex.equivRealProdCLM.symm
        (positiveAxisPlaneRotation (-positiveAxisKeyholeAngle R ε)
          (positiveAxisPlaneFlipSecond ((ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)) p))) = _
    rw [positiveAxisPlaneRotation_apply]
    simp [positiveAxisPlaneFlipSecond, ex, hex_apply, AffineMap.lineMap_apply_module]
    ring
  rw [hbase, circleMap, zero_add, circleMap, zero_add]
  rw [show ((((-positiveAxisKeyholeAngle R ε - Real.pi / 2 : ℝ) : ℂ) * Complex.I)) =
      (-positiveAxisKeyholeAngle R ε) * Complex.I - (Real.pi / 2 : ℂ) * Complex.I by
        simp [sub_eq_add_neg, add_mul]]
  rw [Complex.exp_sub]
  simp
  ring

/-- Helper for Remark III.6-extra-7: near an interior upper-lip point, the explicit affine normal
tube stays in the strict annulus and on the upper half-plane side of the slit, so the sign of the
transverse coordinate is exactly the side-of-boundary test for the owner. -/
private lemma positiveAxisUpperLipPlaneSideOfAnnulus
    {R ε ρ₀ : ℝ} (hε : 0 < ε) (hεR : ε < R) (hρ₀ : ρ₀ ∈ Set.Ioo ε R) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - ρ₀| < η → |p.2| < η →
      let z := circleMap 0 p.1 (positiveAxisKeyholeAngle R ε) +
        (p.2 : ℂ) * circleMap 0 1 (positiveAxisKeyholeAngle R ε + Real.pi / 2)
      (p.2 < 0 → z ∉ positiveAxisWedgeAnnulus R ε) ∧
        (0 < p.2 → z ∈ interior (positiveAxisWedgeAnnulus R ε)) := by
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  have hR : 0 < R := lt_trans hε hεR
  have hsin_pos : 0 < Real.sin θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
  have hcos_pos : 0 < Real.cos θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
  have hsin_nonneg : 0 ≤ Real.sin θ := hsin_pos.le
  have hcos_nonneg : 0 ≤ Real.cos θ := hcos_pos.le
  have hsin_le_one : Real.sin θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have hcos_le_one : Real.cos θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  let η : ℝ :=
    min ((ρ₀ - ε) / 4)
      (min ((R - ρ₀) / 4)
        (min (ρ₀ * Real.cos θ / 4) (ρ₀ * Real.sin θ / 4)))
  have hη_pos : 0 < η := by
    have hρ₀ε : 0 < (ρ₀ - ε) / 4 := by
      nlinarith [hρ₀.1]
    have hRρ₀ : 0 < (R - ρ₀) / 4 := by
      nlinarith [hρ₀.2]
    have hcosq : 0 < ρ₀ * Real.cos θ / 4 := by
      nlinarith [hρ₀.1, hcos_pos]
    have hsinq : 0 < ρ₀ * Real.sin θ / 4 := by
      nlinarith [hρ₀.1, hsin_pos]
    dsimp [η]
    exact lt_min hρ₀ε (lt_min hRρ₀ (lt_min hcosq hsinq))
  refine ⟨η, hη_pos, ?_⟩
  intro p hp₁ hp₂
  let z : ℂ := circleMap 0 p.1 θ + (p.2 : ℂ) * circleMap 0 1 (θ + Real.pi / 2)
  have hη_ρ₀ε : η ≤ (ρ₀ - ε) / 4 := by
    dsimp [η]
    exact min_le_left _ _
  have hη_Rρ₀ : η ≤ (R - ρ₀) / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_cos : η ≤ ρ₀ * Real.cos θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_sin : η ≤ ρ₀ * Real.sin θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hp₁_lower : ρ₀ - η < p.1 := by
    have hp₁' := abs_lt.mp hp₁
    linarith
  have hp₁_upper : p.1 < ρ₀ + η := by
    have hp₁' := abs_lt.mp hp₁
    linarith
  have hp₁_pos : 0 < p.1 := by
    linarith [hρ₀.1, hη_ρ₀ε]
  have hnorm_upper : ‖z‖ < R := by
    have hupper : ‖z‖ ≤ p.1 + |p.2| := by
      calc
        ‖z‖ = ‖circleMap 0 p.1 θ + (p.2 : ℂ) * circleMap 0 1 (θ + Real.pi / 2)‖ := by rfl
        _ ≤ ‖circleMap 0 p.1 θ‖ + ‖(p.2 : ℂ) * circleMap 0 1 (θ + Real.pi / 2)‖ := norm_add_le _ _
        _ = p.1 + |p.2| := by
            rw [norm_circleMap_zero, abs_of_nonneg hp₁_pos.le, norm_mul, norm_circleMap_zero]
            simp
    have hp₂_small : |p.2| < (R - ρ₀) / 4 := lt_of_lt_of_le hp₂ hη_Rρ₀
    have hsum : p.1 + |p.2| < R := by
      linarith
    exact lt_of_le_of_lt hupper hsum
  have hnorm_lower : ε < ‖z‖ := by
    have hcircle : ‖circleMap 0 p.1 θ‖ = p.1 := by
      rw [norm_circleMap_zero, abs_of_nonneg hp₁_pos.le]
    have hnormal : ‖-(p.2 : ℂ) * circleMap 0 1 (θ + Real.pi / 2)‖ = |p.2| := by
      simp [norm_mul]
    have hlower :
        p.1 - |p.2| ≤ ‖z‖ := by
      calc
        p.1 - |p.2| =
            ‖circleMap 0 p.1 θ‖ - ‖-(p.2 : ℂ) * circleMap 0 1 (θ + Real.pi / 2)‖ := by
              rw [hcircle, hnormal]
        _ ≤ ‖circleMap 0 p.1 θ - (-(p.2 : ℂ) * circleMap 0 1 (θ + Real.pi / 2))‖ := by
              exact norm_sub_norm_le _ _
        _ = ‖z‖ := by simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hp₂_small : |p.2| < (ρ₀ - ε) / 4 := lt_of_lt_of_le hp₂ hη_ρ₀ε
    have hdiff : ε < p.1 - |p.2| := by
      linarith
    exact lt_of_lt_of_le hdiff hlower
  have hz_re :
      z.re = p.1 * Real.cos θ - p.2 * Real.sin θ := by
    dsimp [z]
    simp [circleMap_zero_re, circleMap_zero_im, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    ring
  have hz_im :
      z.im = p.1 * Real.sin θ + p.2 * Real.cos θ := by
    dsimp [z]
    simp [circleMap_zero_re, circleMap_zero_im, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  have hz_re_pos : 0 < z.re := by
    have hp₁_big : 3 * ρ₀ / 4 < p.1 := by
      linarith
    have hρcos_big : 3 * (ρ₀ * Real.cos θ) / 4 < p.1 * Real.cos θ := by
      nlinarith
    have hp₂_small : |p.2| < ρ₀ * Real.cos θ / 4 := lt_of_lt_of_le hp₂ hη_cos
    have hp₂sin_lt : p.2 * Real.sin θ < ρ₀ * Real.cos θ / 4 := by
      nlinarith [hp₂_small, le_abs_self p.2, hsin_nonneg, hsin_le_one]
    rw [hz_re]
    linarith
  have hz_im_pos : 0 < z.im := by
    have hp₁_big : 3 * ρ₀ / 4 < p.1 := by
      linarith
    have hρsin_big : 3 * (ρ₀ * Real.sin θ) / 4 < p.1 * Real.sin θ := by
      nlinarith
    have hp₂_small : |p.2| < ρ₀ * Real.sin θ / 4 := lt_of_lt_of_le hp₂ hη_sin
    have hp₂cos_gt : -(ρ₀ * Real.sin θ / 4) < p.2 * Real.cos θ := by
      nlinarith [hp₂_small, neg_le_abs p.2, hcos_nonneg, hcos_le_one]
    rw [hz_im]
    linarith
  have hsigned :
      z.im - (ε / R) * z.re = p.2 * (Real.cos θ + (ε / R) * Real.sin θ) := by
    have hline :
        p.1 * Real.sin θ = (ε / R) * (p.1 * Real.cos θ) := by
      simpa [θ, circleMap_zero_im, circleMap_zero_re] using positiveAxisKeyhole_upper_lip_line R ε p.1
    rw [hz_im, hz_re]
    nlinarith
  have hcoeff :
      0 < Real.cos θ + (ε / R) * Real.sin θ :=
    positiveAxis_lip_transverse_coefficient_pos R ε hε hεR
  constructor
  · intro hp₂_neg hzmem
    -- Negative transverse height crosses into the removed wedge side, so the owner membership
    -- test contradicts the signed-height formula.
    have hheight :
        0 ≤ z.im - (ε / R) * z.re :=
      (positiveAxisWedgeAnnulus_mem_iff_upper_signed_height_nonneg
        hnorm_lower hnorm_upper hz_re_pos hz_im_pos).1 hzmem
    rw [hsigned] at hheight
    nlinarith
  · intro hp₂_pos
    -- Positive transverse height stays on the owner side and the signed-height formula upgrades
    -- that strict inequality to interior membership.
    have hheight :
        0 < z.im - (ε / R) * z.re := by
      rw [hsigned]
      nlinarith
    exact positiveAxisWedgeAnnulus_mem_interior_of_upper_gap
      hnorm_lower hnorm_upper hz_im_pos hheight

/-- Helper for Remark III.6-extra-7: composing the upper-lip side test with the affine branch
parameter `t ↦ lineMap R ε (8 t)` packages the owner-side information directly in the strip-chart
coordinates. -/
private lemma positiveAxisUpperLipChartSideOfAnnulus
    {R ε t₀ : ℝ} (hε : 0 < ε) (hεR : ε < R) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let z := circleMap 0 (AffineMap.lineMap R ε (8 * p.1)) (positiveAxisKeyholeAngle R ε) +
        (p.2 : ℂ) * circleMap 0 1 (positiveAxisKeyholeAngle R ε + Real.pi / 2)
      (p.2 < 0 → z ∉ positiveAxisWedgeAnnulus R ε) ∧
        (0 < p.2 → z ∈ interior (positiveAxisWedgeAnnulus R ε)) := by
  let ρ₀ : ℝ := AffineMap.lineMap R ε (8 * t₀)
  have hparam₀ : 8 * t₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht₀.1, ht₀.2]
  have hρ₀ : ρ₀ ∈ Set.Ioo ε R := by
    have hseg : ρ₀ ∈ openSegment ℝ R ε := by
      simpa [ρ₀] using lineMap_mem_openSegment (𝕜 := ℝ) R ε hparam₀
    have hne : (R : ℝ) ≠ ε := by
      linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hne] at hseg
    simpa [ρ₀, min_eq_right (le_of_lt hεR), max_eq_left (le_of_lt hεR)] using hseg
  rcases positiveAxisUpperLipPlaneSideOfAnnulus hε hεR hρ₀ with ⟨η₀, hη₀, hside⟩
  let η : ℝ := min η₀ (η₀ / (8 * (R - ε)))
  have hscale : 0 < 8 * (R - ε) := by
    nlinarith
  refine ⟨η, lt_min hη₀ (div_pos hη₀ hscale), ?_⟩
  intro p hp₁ hp₂
  have hp₂' : |p.2| < η₀ := by
    exact lt_of_lt_of_le hp₂ (min_le_left _ _)
  have hp₁' : |AffineMap.lineMap R ε (8 * p.1) - ρ₀| < η₀ := by
    have hp₁'' : |p.1 - t₀| < η₀ / (8 * (R - ε)) := by
      exact lt_of_lt_of_le hp₁ (min_le_right _ _)
    have hlin :
        AffineMap.lineMap R ε (8 * p.1) - ρ₀ = (8 * (p.1 - t₀)) * (ε - R) := by
      dsimp [ρ₀]
      simp [AffineMap.lineMap_apply_module]
      ring
    calc
      |AffineMap.lineMap R ε (8 * p.1) - ρ₀|
          = |8 * (p.1 - t₀)| * |ε - R| := by
              rw [hlin, abs_mul]
      _ = (8 * |p.1 - t₀|) * (R - ε) := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ (8 : ℝ) by norm_num),
              abs_of_neg (by linarith : ε - R < 0)]
            ring
      _ = (8 * (R - ε)) * |p.1 - t₀| := by
            ring
      _ < (8 * (R - ε)) * (η₀ / (8 * (R - ε))) := by
            gcongr
      _ = η₀ := by
            have hne : R - ε ≠ 0 := by linarith
            field_simp [hscale.ne', hne]
  simpa [ρ₀] using
    (hside (p := (AffineMap.lineMap R ε (8 * p.1), p.2)) hp₁' hp₂')

/-- Helper for Remark III.6-extra-7: near an interior lower-lip point, the reflected affine
normal tube stays in the strict annulus and on the lower half-plane side of the slit, so the sign
of the transverse coordinate is again the exact side-of-boundary test. -/
private lemma positiveAxisLowerLipPlaneSideOfAnnulus
    {R ε ρ₀ : ℝ} (hε : 0 < ε) (hεR : ε < R) (hρ₀ : ρ₀ ∈ Set.Ioo ε R) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - ρ₀| < η → |p.2| < η →
      let z := circleMap 0 p.1 (-positiveAxisKeyholeAngle R ε) +
        (p.2 : ℂ) * circleMap 0 1 (-positiveAxisKeyholeAngle R ε - Real.pi / 2)
      (p.2 < 0 → z ∉ positiveAxisWedgeAnnulus R ε) ∧
        (0 < p.2 → z ∈ interior (positiveAxisWedgeAnnulus R ε)) := by
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  have hR : 0 < R := lt_trans hε hεR
  have hsin_pos : 0 < Real.sin θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
  have hcos_pos : 0 < Real.cos θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
  have hsin_nonneg : 0 ≤ Real.sin θ := hsin_pos.le
  have hcos_nonneg : 0 ≤ Real.cos θ := hcos_pos.le
  have hsin_le_one : Real.sin θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have hcos_le_one : Real.cos θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  let η : ℝ :=
    min ((ρ₀ - ε) / 4)
      (min ((R - ρ₀) / 4)
        (min (ρ₀ * Real.cos θ / 4) (ρ₀ * Real.sin θ / 4)))
  have hη_pos : 0 < η := by
    have hρ₀ε : 0 < (ρ₀ - ε) / 4 := by
      nlinarith [hρ₀.1]
    have hRρ₀ : 0 < (R - ρ₀) / 4 := by
      nlinarith [hρ₀.2]
    have hcosq : 0 < ρ₀ * Real.cos θ / 4 := by
      nlinarith [hρ₀.1, hcos_pos]
    have hsinq : 0 < ρ₀ * Real.sin θ / 4 := by
      nlinarith [hρ₀.1, hsin_pos]
    dsimp [η]
    exact lt_min hρ₀ε (lt_min hRρ₀ (lt_min hcosq hsinq))
  refine ⟨η, hη_pos, ?_⟩
  intro p hp₁ hp₂
  let z : ℂ := circleMap 0 p.1 (-θ) + (p.2 : ℂ) * circleMap 0 1 (-θ - Real.pi / 2)
  have hη_ρ₀ε : η ≤ (ρ₀ - ε) / 4 := by
    dsimp [η]
    exact min_le_left _ _
  have hη_Rρ₀ : η ≤ (R - ρ₀) / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_cos : η ≤ ρ₀ * Real.cos θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_sin : η ≤ ρ₀ * Real.sin θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hp₁_lower : ρ₀ - η < p.1 := by
    have hp₁' := abs_lt.mp hp₁
    linarith
  have hp₁_upper : p.1 < ρ₀ + η := by
    have hp₁' := abs_lt.mp hp₁
    linarith
  have hp₁_pos : 0 < p.1 := by
    linarith [hρ₀.1, hη_ρ₀ε]
  have hnorm_upper : ‖z‖ < R := by
    have hupper : ‖z‖ ≤ p.1 + |p.2| := by
      calc
        ‖z‖ = ‖circleMap 0 p.1 (-θ) + (p.2 : ℂ) * circleMap 0 1 (-θ - Real.pi / 2)‖ := by rfl
        _ ≤ ‖circleMap 0 p.1 (-θ)‖ + ‖(p.2 : ℂ) * circleMap 0 1 (-θ - Real.pi / 2)‖ := norm_add_le _ _
        _ = p.1 + |p.2| := by
            rw [norm_circleMap_zero, abs_of_nonneg hp₁_pos.le, norm_mul, norm_circleMap_zero]
            simp
    have hp₂_small : |p.2| < (R - ρ₀) / 4 := lt_of_lt_of_le hp₂ hη_Rρ₀
    have hsum : p.1 + |p.2| < R := by
      linarith
    exact lt_of_le_of_lt hupper hsum
  have hnorm_lower : ε < ‖z‖ := by
    have hcircle : ‖circleMap 0 p.1 (-θ)‖ = p.1 := by
      rw [norm_circleMap_zero, abs_of_nonneg hp₁_pos.le]
    have hnormal : ‖-(p.2 : ℂ) * circleMap 0 1 (-θ - Real.pi / 2)‖ = |p.2| := by
      simp [norm_mul]
    have hlower :
        p.1 - |p.2| ≤ ‖z‖ := by
      calc
        p.1 - |p.2| =
            ‖circleMap 0 p.1 (-θ)‖ - ‖-(p.2 : ℂ) * circleMap 0 1 (-θ - Real.pi / 2)‖ := by
              rw [hcircle, hnormal]
        _ ≤ ‖circleMap 0 p.1 (-θ) - (-(p.2 : ℂ) * circleMap 0 1 (-θ - Real.pi / 2))‖ := by
              exact norm_sub_norm_le _ _
        _ = ‖z‖ := by simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hp₂_small : |p.2| < (ρ₀ - ε) / 4 := lt_of_lt_of_le hp₂ hη_ρ₀ε
    have hdiff : ε < p.1 - |p.2| := by
      linarith
    exact lt_of_lt_of_le hdiff hlower
  have hz_re :
      z.re = p.1 * Real.cos θ - p.2 * Real.sin θ := by
    dsimp [z]
    simp [circleMap_zero_re, circleMap_zero_im, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    ring
  have hz_im :
      z.im = -(p.1 * Real.sin θ + p.2 * Real.cos θ) := by
    dsimp [z]
    simp [circleMap_zero_re, circleMap_zero_im, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    ring
  have hz_re_pos : 0 < z.re := by
    have hp₁_big : 3 * ρ₀ / 4 < p.1 := by
      linarith
    have hρcos_big : 3 * (ρ₀ * Real.cos θ) / 4 < p.1 * Real.cos θ := by
      nlinarith
    have hp₂_small : |p.2| < ρ₀ * Real.cos θ / 4 := lt_of_lt_of_le hp₂ hη_cos
    have hp₂sin_lt : p.2 * Real.sin θ < ρ₀ * Real.cos θ / 4 := by
      nlinarith [hp₂_small, le_abs_self p.2, hsin_nonneg, hsin_le_one]
    rw [hz_re]
    linarith
  have hz_im_neg : z.im < 0 := by
    have hp₁_big : 3 * ρ₀ / 4 < p.1 := by
      linarith
    have hρsin_big : 3 * (ρ₀ * Real.sin θ) / 4 < p.1 * Real.sin θ := by
      nlinarith
    have hp₂_small : |p.2| < ρ₀ * Real.sin θ / 4 := lt_of_lt_of_le hp₂ hη_sin
    have hp₂cos_gt : -(ρ₀ * Real.sin θ / 4) < p.2 * Real.cos θ := by
      nlinarith [hp₂_small, neg_le_abs p.2, hcos_nonneg, hcos_le_one]
    rw [hz_im]
    linarith
  have hsigned :
      -z.im - (ε / R) * z.re = p.2 * (Real.cos θ + (ε / R) * Real.sin θ) := by
    have hline :
        -(p.1 * Real.sin θ) = -((ε / R) * (p.1 * Real.cos θ)) := by
      simpa [θ, circleMap_zero_im, circleMap_zero_re] using positiveAxisKeyhole_lower_lip_line R ε p.1
    rw [hz_im, hz_re]
    nlinarith
  have hcoeff :
      0 < Real.cos θ + (ε / R) * Real.sin θ :=
    positiveAxis_lip_transverse_coefficient_pos R ε hε hεR
  constructor
  · intro hp₂_neg hzmem
    -- Negative transverse height crosses into the removed wedge side, so owner membership again
    -- contradicts the reflected signed-height formula.
    have hheight :
        0 ≤ -z.im - (ε / R) * z.re :=
      (positiveAxisWedgeAnnulus_mem_iff_lower_signed_height_nonneg
        hnorm_lower hnorm_upper hz_re_pos hz_im_neg).1 hzmem
    rw [hsigned] at hheight
    nlinarith
  · intro hp₂_pos
    -- Positive transverse height stays on the owner side and the reflected signed-height formula
    -- promotes it to interior membership.
    have hheight :
        0 < -z.im - (ε / R) * z.re := by
      rw [hsigned]
      nlinarith
    exact positiveAxisWedgeAnnulus_mem_interior_of_lower_gap
      hnorm_lower hnorm_upper hz_im_neg hheight

/-- Helper for Remark III.6-extra-7: composing the reflected lower-lip side test with the affine
branch parameter `t ↦ lineMap ε R (4 t - 1)` packages the owner-side information in the actual
lower strip-chart coordinates. -/
private lemma positiveAxisLowerLipChartSideOfAnnulus
    {R ε t₀ : ℝ} (hε : 0 < ε) (hεR : ε < R) (ht₀ : t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let z := circleMap 0 (AffineMap.lineMap ε R (4 * p.1 - 1)) (-positiveAxisKeyholeAngle R ε) +
        (p.2 : ℂ) * circleMap 0 1 (-positiveAxisKeyholeAngle R ε - Real.pi / 2)
      (p.2 < 0 → z ∉ positiveAxisWedgeAnnulus R ε) ∧
        (0 < p.2 → z ∈ interior (positiveAxisWedgeAnnulus R ε)) := by
  let ρ₀ : ℝ := AffineMap.lineMap ε R (4 * t₀ - 1)
  have hparam₀ : 4 * t₀ - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht₀.1, ht₀.2]
  have hρ₀ : ρ₀ ∈ Set.Ioo ε R := by
    have hseg : ρ₀ ∈ openSegment ℝ ε R := by
      simpa [ρ₀] using lineMap_mem_openSegment (𝕜 := ℝ) ε R hparam₀
    have hne : (ε : ℝ) ≠ R := by
      linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hne] at hseg
    simpa [ρ₀, min_eq_left (le_of_lt hεR), max_eq_right (le_of_lt hεR)] using hseg
  rcases positiveAxisLowerLipPlaneSideOfAnnulus hε hεR hρ₀ with ⟨η₀, hη₀, hside⟩
  let η : ℝ := min η₀ (η₀ / (4 * (R - ε)))
  have hscale : 0 < 4 * (R - ε) := by
    nlinarith
  refine ⟨η, lt_min hη₀ (div_pos hη₀ hscale), ?_⟩
  intro p hp₁ hp₂
  have hp₂' : |p.2| < η₀ := by
    exact lt_of_lt_of_le hp₂ (min_le_left _ _)
  have hp₁' : |AffineMap.lineMap ε R (4 * p.1 - 1) - ρ₀| < η₀ := by
    have hp₁'' : |p.1 - t₀| < η₀ / (4 * (R - ε)) := by
      exact lt_of_lt_of_le hp₁ (min_le_right _ _)
    have hlin :
        AffineMap.lineMap ε R (4 * p.1 - 1) - ρ₀ = (4 * (p.1 - t₀)) * (R - ε) := by
      dsimp [ρ₀]
      simp [AffineMap.lineMap_apply_module]
      ring
    calc
      |AffineMap.lineMap ε R (4 * p.1 - 1) - ρ₀|
          = |4 * (p.1 - t₀)| * |R - ε| := by
              rw [hlin, abs_mul]
      _ = (4 * |p.1 - t₀|) * (R - ε) := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num),
              abs_of_nonneg (show 0 ≤ R - ε by linarith)]
      _ = (4 * (R - ε)) * |p.1 - t₀| := by
            ring
      _ < (4 * (R - ε)) * (η₀ / (4 * (R - ε))) := by
            gcongr
      _ = η₀ := by
            have hne : R - ε ≠ 0 := by linarith
            field_simp [hscale.ne', hne]
  simpa [ρ₀] using
    (hside (p := (AffineMap.lineMap ε R (4 * p.1 - 1), p.2)) hp₁' hp₂')

/-- Helper for Remark III.6-extra-7: points on the upper slit-lip branch admit a local
boundary-straightening chart for the positive-axis wedge-annulus. -/
theorem positiveAxisKeyhole_upper_lip_exists_boundary_chart
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (positiveAxisWedgeAnnulus R ε)
        ((positiveAxisKeyhole R ε).toClosedPath.realCurve) t₀ δ :=
by
  let e : Plane ≃ᴬ[ℝ] Plane := positiveAxisUpperLipChart R ε hεR
  let eps_t₀ : ℝ := min t₀ (1 / 8 - t₀) / 2
  have hεt₀_pos : 0 < eps_t₀ := by
    dsimp [eps_t₀]
    have hleft : 0 < t₀ := ht₀.1
    have hright : 0 < 1 / 8 - t₀ := sub_pos.mpr ht₀.2
    have hmin : 0 < min t₀ (1 / 8 - t₀) := lt_min hleft hright
    linarith
  have hstrip₀ :
      Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) ⊆ Set.Ioo (0 : ℝ) (1 / 8 : ℝ) := by
    intro t ht
    have hleft : 0 < t₀ := ht₀.1
    have hright : 0 < 1 / 8 - t₀ := sub_pos.mpr ht₀.2
    constructor
    · have h0 : 0 < t₀ - eps_t₀ := by
        have hmin_le : min t₀ (1 / 8 - t₀) ≤ t₀ := min_le_left _ _
        dsimp [eps_t₀]
        linarith
      exact lt_trans h0 ht.1
    · have h18 : t₀ + eps_t₀ < 1 / 8 := by
        have hmin_le : min t₀ (1 / 8 - t₀) ≤ 1 / 8 - t₀ := min_le_right _ _
        dsimp [eps_t₀]
        linarith
      exact lt_trans ht.2 h18
  rcases positiveAxisUpperLipChartSideOfAnnulus hε hεR ht₀ with ⟨η, hη, hside⟩
  let eps_t : ℝ := min eps_t₀ η
  have hεt_pos : 0 < eps_t := lt_min hεt₀_pos hη
  have hstrip_param_branch :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) (1 / 8 : ℝ) := by
    intro t ht
    have ht' : t ∈ Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) := by
      constructor <;> linarith [ht.1, ht.2, min_le_left eps_t₀ η]
    exact hstrip₀ ht'
  have hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    have ht' := hstrip_param_branch ht
    exact ⟨ht'.1, lt_trans ht'.2 (by norm_num)⟩
  refine positiveAxisAffineBoundaryStripChartExists e hεt_pos hη hstrip_param ?_ ?_
  · intro t ht
    have htBranch : t ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ) := hstrip_param_branch ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
    have hbranch :
        (AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * t)) =
          circleMap 0 (AffineMap.lineMap R ε (8 * t)) (positiveAxisKeyholeAngle R ε) := by
      simp [AffineMap.lineMap_apply_module, circleMap]
      ring
    -- On the horizontal axis, the affine chart recovers the upper slit-lip branch exactly.
    apply Complex.equivRealProdCLM.symm.injective
    calc
      Complex.equivRealProdCLM.symm (e (t, 0)) =
          circleMap 0 (AffineMap.lineMap R ε (8 * t)) (positiveAxisKeyholeAngle R ε) +
            ((0 : ℝ) : ℂ) * circleMap 0 1 (positiveAxisKeyholeAngle R ε + Real.pi / 2) := by
              simpa [e] using positiveAxisUpperLipChart_apply R ε hεR (t, 0)
      _ = circleMap 0 (AffineMap.lineMap R ε (8 * t)) (positiveAxisKeyholeAngle R ε) := by simp
      _ =
          (positiveAxisKeyhole R ε).extend t := by
              rw [← hbranch]
              symm
              exact positive_axis_keyhole_eq_on_upper_lip R ε htIcc
      _ = (ClosedPath.toPath ((positiveAxisKeyhole R ε).toClosedPath)).extend t := by
              rfl
      _ =
          Complex.equivRealProdCLM.symm
            (((positiveAxisKeyhole R ε).toClosedPath.realCurve) t) := by
              rw [Complex.equivRealProdCLM_symm_apply]
              simp [ClosedPath.realCurve, Function.comp, Path.toClosedPath]
  · intro t u ht hu
    -- The theorem-local chart-side lemma already expresses the upper-lip owner test in the strip
    -- coordinates used by the affine packager.
    rw [show Complex.equivRealProdCLM.symm (e (t, u)) =
        circleMap 0 (AffineMap.lineMap R ε (8 * t)) (positiveAxisKeyholeAngle R ε) +
          ((u : ℝ) : ℂ) * circleMap 0 1 (positiveAxisKeyholeAngle R ε + Real.pi / 2) by
            simpa [e] using positiveAxisUpperLipChart_apply R ε hεR (t, u)]
    exact hside (p := (t, u)) (by
      have hleft : -eps_t < t - t₀ := by linarith [ht.1]
      have hright : t - t₀ < eps_t := by linarith [ht.2]
      exact lt_of_lt_of_le (abs_lt.mpr ⟨hleft, hright⟩) (min_le_right eps_t₀ η)) (by
      have hleft : -η < u := by linarith [hu.1]
      have hright : u < η := by linarith [hu.2]
      exact abs_lt.mpr ⟨hleft, hright⟩)

/-- Helper for Remark III.6-extra-7: points on the lower slit-lip branch admit a local
boundary-straightening chart for the positive-axis wedge-annulus. -/
theorem positiveAxisKeyhole_lower_lip_exists_boundary_chart
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (positiveAxisWedgeAnnulus R ε)
        ((positiveAxisKeyhole R ε).toClosedPath.realCurve) t₀ δ :=
by
  let e : Plane ≃ᴬ[ℝ] Plane := positiveAxisLowerLipChart R ε hεR
  let eps_t₀ : ℝ := min (t₀ - 1 / 4) (1 / 2 - t₀) / 2
  have hεt₀_pos : 0 < eps_t₀ := by
    dsimp [eps_t₀]
    have hleft : 0 < t₀ - 1 / 4 := sub_pos.mpr ht₀.1
    have hright : 0 < 1 / 2 - t₀ := sub_pos.mpr ht₀.2
    have hmin : 0 < min (t₀ - 1 / 4) (1 / 2 - t₀) := lt_min hleft hright
    linarith
  have hstrip₀ :
      Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) ⊆ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) := by
    intro t ht
    constructor
    · have h14 : 1 / 4 < t₀ - eps_t₀ := by
        have hsmall : eps_t₀ < t₀ - 1 / 4 := by
          dsimp [eps_t₀]
          have hmin_le : min (t₀ - 1 / 4) (1 / 2 - t₀) ≤ t₀ - 1 / 4 := min_le_left _ _
          nlinarith [ht₀.1, hmin_le]
        linarith
      exact lt_trans h14 ht.1
    · have h12 : t₀ + eps_t₀ < 1 / 2 := by
        have hsmall : eps_t₀ < 1 / 2 - t₀ := by
          dsimp [eps_t₀]
          have hmin_le : min (t₀ - 1 / 4) (1 / 2 - t₀) ≤ 1 / 2 - t₀ := min_le_right _ _
          nlinarith [ht₀.2, hmin_le]
        linarith
      exact lt_trans ht.2 h12
  rcases positiveAxisLowerLipChartSideOfAnnulus hε hεR ht₀ with ⟨η, hη, hside⟩
  let eps_t : ℝ := min eps_t₀ η
  have hεt_pos : 0 < eps_t := lt_min hεt₀_pos hη
  have hstrip_param_branch :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) := by
    intro t ht
    have ht' : t ∈ Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) := by
      constructor <;> linarith [ht.1, ht.2, min_le_left eps_t₀ η]
    exact hstrip₀ ht'
  have hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    have ht' := hstrip_param_branch ht
    exact ⟨lt_trans (by norm_num) ht'.1, lt_trans ht'.2 (by norm_num)⟩
  refine positiveAxisAffineBoundaryStripChartExists e hεt_pos hη hstrip_param ?_ ?_
  · intro t ht
    have htBranch : t ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) := hstrip_param_branch ht
    have htIcc : t ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
    have hbranch :
        (AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * t - 1)) =
          circleMap 0 (AffineMap.lineMap ε R (4 * t - 1)) (-positiveAxisKeyholeAngle R ε) := by
      simp [AffineMap.lineMap_apply_module, circleMap]
      ring
    -- On the horizontal axis, the reflected affine chart recovers the lower slit-lip branch.
    apply Complex.equivRealProdCLM.symm.injective
    calc
      Complex.equivRealProdCLM.symm (e (t, 0)) =
          circleMap 0 (AffineMap.lineMap ε R (4 * t - 1)) (-positiveAxisKeyholeAngle R ε) +
            ((0 : ℝ) : ℂ) * circleMap 0 1 (-positiveAxisKeyholeAngle R ε - Real.pi / 2) := by
              simpa [e] using positiveAxisLowerLipChart_apply R ε hεR (t, 0)
      _ = circleMap 0 (AffineMap.lineMap ε R (4 * t - 1)) (-positiveAxisKeyholeAngle R ε) := by simp
      _ =
          (positiveAxisKeyhole R ε).extend t := by
              rw [← hbranch]
              symm
              exact positive_axis_keyhole_eq_on_lower_lip R ε htIcc
      _ = (ClosedPath.toPath ((positiveAxisKeyhole R ε).toClosedPath)).extend t := by
              rfl
      _ =
          Complex.equivRealProdCLM.symm
            (((positiveAxisKeyhole R ε).toClosedPath.realCurve) t) := by
              rw [Complex.equivRealProdCLM_symm_apply]
              simp [ClosedPath.realCurve, Function.comp, Path.toClosedPath]
  · intro t u ht hu
    -- The reflected chart-side lemma gives the owner test in the strip coordinates consumed by
    -- the affine packager.
    rw [show Complex.equivRealProdCLM.symm (e (t, u)) =
        circleMap 0 (AffineMap.lineMap ε R (4 * t - 1)) (-positiveAxisKeyholeAngle R ε) +
          ((u : ℝ) : ℂ) * circleMap 0 1 (-positiveAxisKeyholeAngle R ε - Real.pi / 2) by
            simpa [e] using positiveAxisLowerLipChart_apply R ε hεR (t, u)]
    exact hside (p := (t, u)) (by
      have hleft : -eps_t < t - t₀ := by linarith [ht.1]
      have hright : t - t₀ < eps_t := by linarith [ht.2]
      exact lt_of_lt_of_le (abs_lt.mpr ⟨hleft, hright⟩) (min_le_right eps_t₀ η)) (by
      have hleft : -η < u := by linarith [hu.1]
      have hright : u < η := by linarith [hu.2]
      exact abs_lt.mpr ⟨hleft, hright⟩)

/-- Helper for Remark III.6-extra-7: every regular point on one of the two radial keyhole lips
admits a local boundary-straightening chart. -/
theorem positiveAxisKeyhole_ray_branch_exists_boundary_chart
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hbranch : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨ t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (positiveAxisWedgeAnnulus R ε)
        ((positiveAxisKeyhole R ε).toClosedPath.realCurve) t₀ δ :=
by
  let _ := ht₀
  -- Once the regular point is known to lie on a ray branch, only the upper/lower lip packager
  -- remains to be chosen.
  rcases hbranch with htupper | htlower
  · exact positiveAxisKeyhole_upper_lip_exists_boundary_chart R ε hε hεR htupper
  · exact positiveAxisKeyhole_lower_lip_exists_boundary_chart R ε hε hεR htlower
