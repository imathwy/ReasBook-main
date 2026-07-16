import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».SquareBoundaryIntegrability

noncomputable section

open scoped Topology unitInterval

/-- Helper for Cartan section12 0038_Exercise_25: the cotangent kernel is odd, so negating the
argument flips its sign. -/
lemma exercise25_piCot_neg (z : ℂ) :
    exercise25PiCot (-z) = -exercise25PiCot z := by
  -- Rewrite the cotangent kernel through `cos / sin` and use the parity of `cos` and `sin`.
  rw [exercise25_piCot_eq_cos_div_sin, exercise25_piCot_eq_cos_div_sin]
  simp [Complex.cos_neg, Complex.sin_neg, div_eq_mul_inv, mul_assoc]

/-- Helper for Cartan section12 0038_Exercise_25: dividing the odd cotangent kernel by `z`
produces an even function. -/
lemma exercise25_piCot_div_z_even (z : ℂ) :
    exercise25PiCot (-z) / (-z) = exercise25PiCot z / z := by
  -- The numerator and denominator both pick up the same sign under `z ↦ -z`.
  simpa [div_eq_mul_inv, exercise25_piCot_neg, mul_assoc]

/-- Helper for Cartan section12 0038_Exercise_25: the correction integral from the degree-gap-one
split vanishes because opposite sides of the square contour contribute opposite values to the even
integrand `π cot (π z) / z`. -/
lemma exercise25_piCotDivZ_squareIntegral_eq_zero (n : ℕ) :
    ∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ exercise25PiCot z / z) dz) z = 0 := by
  let φ : ℂ → ℂ := fun z ↦ exercise25PiCot z / z
  let r : ℝ := exercise25SquareRadius n
  let z₀ : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  let D : Set ℂ := Set.range (exercise25SquareBoundary n)
  have hcoeff : ContinuousOn φ D := by
    intro z hz
    have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
      exercise25_sin_pi_ne_zero_on_square_boundary n hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      subst hz0
      simpa using hsin
    have hz_notint : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)) := by
      intro hzint
      rcases hzint with ⟨p, rfl⟩
      exact hsin <| by simpa [mul_comm] using Complex.sin_int_mul_pi p
    -- On the boundary, the cotangent factor and the extra divisor `z` are both regular.
    have hcont : ContinuousAt φ z := by
      simpa [φ] using
        (exercise25_piCot_continuousAt_of_not_integer hz_notint).div continuousAt_id hz_ne
    exact hcont.continuousWithinAt
  have hform :
      ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) D := by
    -- Package the scalar coefficient as a continuous complex-linear one-form on the contour.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
  have hsubsets := exercise25_square_boundary_side_ranges_subset n
  dsimp [z₀, w, zw, wz] at hsubsets
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
      (fun t ↦ hbottom_subset ⟨t, rfl⟩)
  have hright_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
      (fun t ↦ hright_subset ⟨t, rfl⟩)
  have htop_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
      (fun t ↦ htop_subset ⟨t, rfl⟩)
  have hleft_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
      (fun t ↦ hleft_subset ⟨t, rfl⟩)
  have htop_line :
      ∀ t : ℝ, AffineMap.lineMap w wz t = -AffineMap.lineMap z₀ zw t := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, w, zw, wz, r] <;> ring
  have hleft_line :
      ∀ t : ℝ, AffineMap.lineMap wz z₀ t = -AffineMap.lineMap zw w t := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, w, zw, wz, r] <;> ring
  have htop_diff : wz - w = -(zw - z₀) := by
    apply Complex.ext <;> simp [z₀, w, zw, wz, r]
  have hleft_diff : z₀ - wz = -(w - zw) := by
    apply Complex.ext <;> simp [z₀, w, zw, wz, r]
  have htop_eq :
      ∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z =
        -∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z := by
    rw [curveIntegral_segment, curveIntegral_segment]
    calc
      ∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap w wz t)) (wz - w) =
          ∫ t in (0 : ℝ)..1, -((((fun z ↦ φ z) dz) (AffineMap.lineMap z₀ zw t)) (zw - z₀)) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            simp only [Complex.scalarOneForm_apply, φ]
            rw [htop_line t, htop_diff, exercise25_piCot_div_z_even]
            ring
      _ = -∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap z₀ zw t)) (zw - z₀) := by
            rw [intervalIntegral.integral_neg]
  have hleft_eq :
      ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z =
        -∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z := by
    rw [curveIntegral_segment, curveIntegral_segment]
    calc
      ∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap wz z₀ t)) (z₀ - wz) =
          ∫ t in (0 : ℝ)..1, -((((fun z ↦ φ z) dz) (AffineMap.lineMap zw w t)) (w - zw)) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            simp only [Complex.scalarOneForm_apply, φ]
            rw [hleft_line t, hleft_diff, exercise25_piCot_div_z_even]
            ring
      _ = -∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap zw w t)) (w - zw) := by
            rw [intervalIntegral.integral_neg]
  have hboundary_eq :
      exercise25SquareBoundary n =
        (Path.segment z₀ zw).trans
          ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
    rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
  -- Expand the contour into its four affine sides and cancel the opposite pairs using evenness.
  rw [hboundary_eq]
  rw [curveIntegral_trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))]
  rw [curveIntegral_trans hright_int (CurveIntegrable.trans htop_int hleft_int)]
  rw [curveIntegral_trans htop_int hleft_int]
  rw [htop_eq, hleft_eq]
  ring
