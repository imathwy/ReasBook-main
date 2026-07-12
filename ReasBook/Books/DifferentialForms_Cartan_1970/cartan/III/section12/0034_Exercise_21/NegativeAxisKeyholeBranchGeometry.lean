import DifferentialForms_Cartan_1970.III.section12.«0034_Exercise_21».NegativeAxisKeyholeSegments

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

/-- Helper for Exercise 21: points on the upper lip of the negative-axis keyhole lie on the line
`im z = (ε / r) * (-re z)`. This is the first branch invariant used to separate the slit lips from
the circular arcs. -/
lemma exercise21Delta_upper_lip_line (r ε ρ : ℝ) :
    (circleMap 0 ρ (Real.pi - Real.arctan (ε / r))).im =
      -((ε / r) * (circleMap 0 ρ (Real.pi - Real.arctan (ε / r))).re) := by
  -- Unfold the circle coordinates at the upper-lip angle and use the standard arctangent formulas.
  rw [circleMap_zero_im, circleMap_zero_re]
  rw [Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_arctan, Real.cos_arctan]
  ring

/-- Helper for Exercise 21: points on the lower lip of the negative-axis keyhole lie on the line
`im z = (ε / r) * re z`. This is the companion line equation for the lower slit edge. -/
lemma exercise21Delta_lower_lip_line (r ε ρ : ℝ) :
    (circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))).im =
      (ε / r) * (circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))).re := by
  -- Normalize the lower-lip angle to `arctan (ε / r) - π`, then reduce again to the
  -- arctangent identities.
  have hsin :
      Real.sin (-Real.pi + Real.arctan (ε / r)) = -Real.sin (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.sin_sub]
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) = -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  rw [circleMap_zero_im, circleMap_zero_re, hsin, hcos, Real.sin_arctan, Real.cos_arctan]
  ring

/-- Helper for Exercise 21: every nonzero point on the upper lip has negative real part, so it
lies on the negative-real side of the slit model. -/
lemma exercise21Delta_upper_lip_re_neg
    {r ε ρ : ℝ} (hρ : 0 < ρ) :
    (circleMap 0 ρ (Real.pi - Real.arctan (ε / r))).re < 0 := by
  -- The upper-lip angle differs from `arctan (ε / r)` by `π`, so the cosine changes sign.
  rw [circleMap_zero_re, Real.cos_pi_sub]
  have hpos : 0 < ρ * Real.cos (Real.arctan (ε / r)) := by
    exact mul_pos hρ (Real.cos_arctan_pos (ε / r))
  linarith

/-- Helper for Exercise 21: every nonzero point on the lower lip also has negative real part,
which is the remaining sign condition in the negative-wedge geometry. -/
lemma exercise21Delta_lower_lip_re_neg
    {r ε ρ : ℝ} (hρ : 0 < ρ) :
    (circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))).re < 0 := by
  -- The lower-lip angle is `arctan (ε / r) - π`, so the cosine is the negative of
  -- `cos (arctan (ε / r))`.
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) = -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  rw [circleMap_zero_re, hcos]
  have hpos : 0 < ρ * Real.cos (Real.arctan (ε / r)) := by
    exact mul_pos hρ (Real.cos_arctan_pos (ε / r))
  linarith

/-- Helper for Exercise 21: the transverse coefficient in the slit-lip normal coordinates is
strictly positive, so the sign of the transverse parameter agrees with the side of the slit. -/
lemma exercise21_lip_transverse_coefficient_pos
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    0 <
      Real.cos (Real.arctan (ε / r)) +
        (ε / r) * Real.sin (Real.arctan (ε / r)) := by
  have hr : 0 < r := lt_trans hε hεr
  have hcos : 0 < Real.cos (Real.arctan (ε / r)) :=
    Real.cos_arctan_pos (ε / r)
  have hratio_nonneg : 0 ≤ ε / r := by
    exact le_of_lt (div_pos hε hr)
  have hsin_nonneg : 0 ≤ Real.sin (Real.arctan (ε / r)) := by
    rw [Real.sin_arctan]
    positivity
  -- The coefficient is the sum of a positive cosine term and a nonnegative slope correction.
  exact add_pos_of_pos_of_nonneg hcos (mul_nonneg hratio_nonneg hsin_nonneg)

/-- Helper for Exercise 21: in the explicit upper-lip normal coordinates, the signed height above
the slit line is a positive multiple of the transverse parameter. This is the core sign identity
for the upper branch chart. -/
lemma exercise21_upper_lip_normal_signed_height
    (r ε ρ s : ℝ) :
    let φ := Real.pi - Real.arctan (ε / r)
    let z := circleMap 0 ρ φ + (s : ℂ) * circleMap 0 1 (φ - Real.pi / 2)
    z.im + (ε / r) * z.re =
      s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
  let φ := Real.pi - Real.arctan (ε / r)
  let w : ℂ := circleMap 0 ρ φ
  let n : ℂ := circleMap 0 1 (φ - Real.pi / 2)
  have hw :
      w.im + (ε / r) * w.re = 0 := by
    -- The upper lip itself lies on the boundary line `im z = -(ε / r) re z`.
    have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρ)
    simpa [w, φ] using eq_neg_iff_add_eq_zero.mp hline
  have hn :
      n.im + (ε / r) * n.re =
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) := by
    -- The chosen upper-lip normal is the `-π/2` rotation of the lip direction.
    dsimp [n, φ]
    rw [circleMap_zero_im, circleMap_zero_re, Real.sin_sub_pi_div_two,
      Real.cos_sub_pi_div_two, Real.sin_pi_sub, Real.cos_pi_sub]
    ring
  -- Split the signed height into the lip contribution, which vanishes, and the normal
  -- contribution, which is exactly the positive transverse coefficient.
  calc
    (w + (s : ℂ) * n).im + (ε / r) * (w + (s : ℂ) * n).re
        = (w.im + (ε / r) * w.re) + s * (n.im + (ε / r) * n.re) := by
            simp [Complex.add_re, Complex.add_im, mul_re, mul_im, Complex.ofReal_re,
              Complex.ofReal_im]
            ring
    _ = s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
          rw [hw, hn]
          ring

/-- Helper for Exercise 21: in the explicit lower-lip normal coordinates, the signed height below
the slit line is again a positive multiple of the transverse parameter. This is the matching sign
identity for the lower branch chart. -/
lemma exercise21_lower_lip_normal_signed_height
    (r ε ρ s : ℝ) :
    -(circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) +
        (s : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)).im +
      (ε / r) *
        (circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) +
          (s : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)).re =
      s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
  let φ := -Real.pi + Real.arctan (ε / r)
  let w : ℂ := circleMap 0 ρ φ
  let n : ℂ := circleMap 0 1 (φ + Real.pi / 2)
  have hw :
      -w.im + (ε / r) * w.re = 0 := by
    -- The lower lip lies on the companion boundary line `im z = (ε / r) re z`.
    have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρ)
    linarith
  have hsin :
      Real.sin (-Real.pi + Real.arctan (ε / r)) =
        -Real.sin (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.sin_sub]
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) =
        -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  have hn :
      -n.im + (ε / r) * n.re =
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) := by
    -- The lower-lip inward normal is the `+π/2` rotation of the lower radial direction.
    dsimp [n, φ]
    rw [circleMap_zero_im, circleMap_zero_re, Real.sin_add_pi_div_two,
      Real.cos_add_pi_div_two, hsin, hcos]
    ring
  -- As on the upper lip, the line contribution vanishes and only the normal coefficient remains.
  calc
    -(w + (s : ℂ) * n).im + (ε / r) * (w + (s : ℂ) * n).re
        = (-w.im + (ε / r) * w.re) + s * (-n.im + (ε / r) * n.re) := by
            simp [Complex.add_re, Complex.add_im, mul_re, mul_im, Complex.ofReal_re,
              Complex.ofReal_im]
            ring
    _ = s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
          rw [hw, hn]
          ring

/-- Helper for Exercise 21: affine interpolation between two points on the same ray only changes
the radius, so the angular coordinate stays fixed. This is the transport-stable normalization used
when a branch proof should reason by radius and angle rather than by raw complex affine formulas. -/
lemma exercise21_lineMap_circleMap_same_angle (ρ₀ ρ₁ φ c : ℝ) :
    AffineMap.lineMap (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ) c =
      circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ c) φ := by
  -- Compare real and imaginary parts separately; on a fixed ray, affine interpolation is purely
  -- radial.
  rw [Complex.ext_iff]
  constructor <;>
    simp [circleMap_zero_re, circleMap_zero_im, AffineMap.lineMap_apply_module, smul_eq_mul,
      add_mul] <;>
    ring

/-- Helper for Exercise 21: the opening angle `θ = arctan (ε / r)` of the keyhole contour lies in
`(0, π / 2)` whenever `0 < ε < r`. -/
lemma exercise21_keyhole_angle_bounds {r ε : ℝ}
    (hε : 0 < ε) (hεr : ε < r) :
    0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 := by
  -- The keyhole opening is acute because the slope `ε / r` is positive.
  have hr : 0 < r := lt_trans hε hεr
  constructor
  · exact Real.arctan_pos.mpr (div_pos hε hr)
  · exact Real.arctan_lt_pi_div_two (ε / r)

/-- Helper for Exercise 21: an interior point of the upper slit lip is a point on the upper
boundary ray with radius strictly between `ε` and `r`. -/
lemma exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) :
    ∃ ρ ∈ Set.Ioo ε r,
      exercise21Delta r ε t =
        circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) := by
  let ρ : ℝ := AffineMap.lineMap r ε (8 * (t : ℝ))
  have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε r := by
    have hseg : ρ ∈ openSegment ℝ r ε := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) r ε hparam
    have hre : (r : ℝ) ≠ ε := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ, min_eq_right (le_of_lt hεr), max_eq_left (le_of_lt hεr)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open upper branch using the radial parameter supplied by `lineMap`.
  calc
    exercise21Delta r ε t =
        AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * (t : ℝ)) := by
            exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
              exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) := by
          rw [exercise21_lineMap_circleMap_same_angle]

/-- Helper for Exercise 21: an interior point of the inner arc stays on the circle of radius `ε`
with angle strictly between the two slit-boundary angles. -/
lemma exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) :
    ∃ α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)),
      exercise21Delta r ε t = circleMap 0 ε α := by
  let α : ℝ :=
    AffineMap.lineMap
      (Real.pi - Real.arctan (ε / r))
      (-Real.pi + Real.arctan (ε / r))
      (8 * (t : ℝ) - 1)
  have hr : 0 < r := lt_trans hε hεr
  have hθ : 0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 :=
    exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
    have hseg :
        α ∈ openSegment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          hparam
    have hneq :
        Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    have horder :
        -Real.pi + Real.arctan (ε / r) ≤ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    simpa [α, min_eq_right horder, max_eq_left horder] using hseg
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open inner branch to its explicit angular parameter.
  exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
    exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self ht)

/-- Helper for Exercise 21: an interior point of the lower slit lip is a point on the lower
boundary ray with radius strictly between `ε` and `r`. -/
lemma exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) :
    ∃ ρ ∈ Set.Ioo ε r,
      exercise21Delta r ε t =
        circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) := by
  let ρ : ℝ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1)
  have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε r := by
    have hseg : ρ ∈ openSegment ℝ ε r := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) ε r hparam
    have hre : (ε : ℝ) ≠ r := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ, min_eq_left (le_of_lt hεr), max_eq_right (le_of_lt hεr)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open lower branch using the corresponding radial parameter.
  calc
    exercise21Delta r ε t =
        AffineMap.lineMap
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
          (4 * (t : ℝ) - 1) := by
            exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
              exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) := by
          rw [exercise21_lineMap_circleMap_same_angle]

/-- Helper for Exercise 21: an interior point of the outer arc stays on the circle of radius `r`
with angle strictly between the two slit-boundary angles. -/
lemma exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)) :
    ∃ α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)),
      exercise21Delta r ε t = circleMap 0 r α := by
  let α : ℝ :=
    AffineMap.lineMap
      (-Real.pi + Real.arctan (ε / r))
      (Real.pi - Real.arctan (ε / r))
      (2 * (t : ℝ) - 1)
  have hr : 0 < r := lt_trans hε hεr
  have hθ : 0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 :=
    exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
    have hseg :
        α ∈ openSegment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          hparam
    have hneq :
        -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    have horder :
        -Real.pi + Real.arctan (ε / r) ≤ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    simpa [α, min_eq_left horder, max_eq_right horder] using hseg
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open outer branch to its explicit angular parameter.
  exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
    exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self ht)
