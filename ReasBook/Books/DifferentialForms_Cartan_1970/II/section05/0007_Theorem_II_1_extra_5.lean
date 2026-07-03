import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»

open scoped unitInterval

noncomputable section

open MeasureTheory

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Theorem II.1-extra-5: the boundary path of the axis-parallel rectangle with
opposite corners `z` and `w`, traversed side-by-side in the source-proof order. -/
def axisParallelRectangleBoundaryPath (z w : ℂ) : Path z z :=
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  (Path.segment z zw).trans
    ((Path.segment zw w).trans
      ((Path.segment w wz).trans
        (Path.segment wz z)))

section

variable (P Q dPdy dQdx : ℂ → ℝ) {z w : ℂ}

local notation "Rect" => Complex.Rectangle z w

/-- Helper for Theorem II.1-extra-5: the extension of a straight segment is `C¹` on the unit
interval. -/
lemma segment_contDiffOn (a b : ℂ) : ContDiffOn ℝ 1 (Path.segment a b).extend I := by
  -- A segment extension agrees with the affine line map on the unit interval.
  have hline : ContDiffOn ℝ 1 (ContinuousAffineMap.lineMap (R := ℝ) a b) I :=
    (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) a b)).contDiffOn
  refine hline.congr ?_
  intro t ht
  simpa using Path.eqOn_extend_segment a b ht

/-- Helper for Theorem II.1-extra-5: a continuous `1`-form is curve integrable on any affine side
of the rectangle. -/
lemma rectangle_side_curveIntegrable {ω : ℂ → ℂ →L[ℝ] ℝ} {a b : ℂ}
    (hω : ContinuousOn ω Rect) (hab : ∀ t : I, Path.segment a b t ∈ Rect) :
    CurveIntegrable ω (Path.segment a b) := by
  -- Continuity on the rectangle and the affine parametrization of a side give curve integrability.
  exact hω.curveIntegrable_of_contDiffOn (segment_contDiffOn a b) hab

/-- Helper for Theorem II.1-extra-5: along a vertical segment, only the `Q dy` term contributes. -/
lemma vertical_segment_qdy_eq_intervalIntegral (P0 Q0 : ℂ → ℝ) (a y₁ y₂ : ℝ) :
    (∫ᶜ ζ in Path.segment (Complex.mk a y₁) (Complex.mk a y₂), (P0 dx + Q0 dy) ζ) =
      ∫ y in y₁..y₂, Q0 (Complex.mk a y) := by
  -- Rewrite the curve integral using the affine parametrization of the segment.
  rw [curveIntegral_segment]
  have hline : ∀ t : ℝ,
      AffineMap.lineMap (Complex.mk a y₁) (Complex.mk a y₂) t =
        Complex.mk a ((y₂ - y₁) * t + y₁) := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, sub_eq_add_neg]
    ring
  simp [hline]
  -- The remaining change of variables is the standard affine interval-integral identity.
  simpa [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
    (intervalIntegral.smul_integral_comp_mul_add
      (f := fun y ↦ Q0 (Complex.mk a y)) (a := (0 : ℝ)) (b := 1)
      (c := y₂ - y₁) (d := y₁))

/-- Helper for Theorem II.1-extra-5: along a horizontal segment, only the `P dx` term
contributes. -/
lemma horizontal_segment_pdx_eq_intervalIntegral (P0 Q0 : ℂ → ℝ) (x₁ x₂ b : ℝ) :
    (∫ᶜ ζ in Path.segment (Complex.mk x₁ b) (Complex.mk x₂ b), (P0 dx + Q0 dy) ζ) =
      ∫ x in x₁..x₂, P0 (Complex.mk x b) := by
  -- Rewrite the curve integral using the affine parametrization of the segment.
  rw [curveIntegral_segment]
  have hline : ∀ t : ℝ,
      AffineMap.lineMap (Complex.mk x₁ b) (Complex.mk x₂ b) t =
        Complex.mk ((x₂ - x₁) * t + x₁) b := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, sub_eq_add_neg]
    ring
  simp [hline]
  -- The remaining change of variables is the standard affine interval-integral identity.
  simpa [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
    (intervalIntegral.smul_integral_comp_mul_add
      (f := fun x ↦ P0 (Complex.mk x b)) (a := (0 : ℝ)) (b := 1)
      (c := x₂ - x₁) (d := x₁))

/-- Helper for Theorem II.1-extra-5: fixing the real part gives a continuous vertical coordinate
embedding into `ℂ`. -/
lemma continuousOn_complex_mk_left (a : ℝ) {s : Set ℝ} :
    ContinuousOn (fun y : ℝ ↦ Complex.mk a y) s := by
  have hcont : Continuous (fun y : ℝ ↦ (a : ℂ) + y * Complex.I) := by
    exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  refine hcont.continuousOn.congr ?_
  intro y hy
  apply Complex.ext <;> simp

/-- Helper for Theorem II.1-extra-5: fixing the imaginary part gives a continuous horizontal
coordinate embedding into `ℂ`. -/
lemma continuousOn_complex_mk_right (b : ℝ) {s : Set ℝ} :
    ContinuousOn (fun x : ℝ ↦ Complex.mk x b) s := by
  have hcont : Continuous (fun x : ℝ ↦ (x : ℂ) + b * Complex.I) := by
    exact (Complex.continuous_ofReal.comp continuous_id).add (continuous_const.mul continuous_const)
  refine hcont.continuousOn.congr ?_
  intro x hx
  apply Complex.ext <;> simp

/-- Helper for Theorem II.1-extra-5: pairing the two real coordinates gives a continuous map into
`ℂ`. -/
lemma continuousOn_complex_mk_prod {s : Set (ℝ × ℝ)} :
    ContinuousOn (fun p : ℝ × ℝ ↦ Complex.mk p.1 p.2) s := by
  have hcont : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * Complex.I) := by
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  refine hcont.continuousOn.congr ?_
  intro p hp
  apply Complex.ext <;> simp

/-- Helper for Theorem II.1-extra-5: every complex tangent vector splits in the real basis
`1, I`. -/
lemma complex_eq_re_smul_one_add_im_smul_I (v : ℂ) :
    v = v.re • (1 : ℂ) + v.im • Complex.I := by
  apply Complex.ext <;> simp

/-- Helper for Theorem II.1-extra-5: every real-valued real-linear `1`-form on `ℂ` is the planar
form with coefficients given by its values on `1` and `I`. -/
lemma one_form_eq_planarDifferentialForm (ω : ℂ → ℂ →L[ℝ] ℝ) :
    ω = Complex.planarDifferentialForm (fun z ↦ ω z 1) (fun z ↦ ω z Complex.I) := by
  ext z v
  -- Decompose the tangent vector into the real basis `1` and the imaginary basis `I`.
  rw [Complex.planarDifferentialForm_apply]
  calc
    ω z v = ω z (v.re • (1 : ℂ) + v.im • Complex.I) := by
      exact congrArg (ω z) (complex_eq_re_smul_one_add_im_smul_I v)
    _ = v.re • ω z 1 + v.im • ω z Complex.I := by
      rw [map_add, map_smul, map_smul]

/-- Helper for Theorem II.1-extra-5: the reversed affine interpolation between `a` and `b`
still lies in the unordered interval spanned by the endpoints. -/
lemma lineMap_mem_uIcc_swap (a b : ℝ) (t : I) :
    AffineMap.lineMap b a (t : ℝ) ∈ Set.uIcc a b := by
  simpa [segment_eq_uIcc, Set.uIcc_comm] using
    (lineMap_mem_segment ℝ b a t.2 :
      AffineMap.lineMap b a (t : ℝ) ∈ segment ℝ b a)

/-- Helper for Theorem II.1-extra-5: a continuous planar form is curve integrable along the full
axis-parallel rectangle boundary. -/
lemma rectangle_boundary_curveIntegrable {ω : ℂ → ℂ →L[ℝ] ℝ}
    (hω : ContinuousOn ω Rect) :
    CurveIntegrable ω (axisParallelRectangleBoundaryPath z w) := by
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  have hbottom_mem : ∀ t : I, Path.segment z zw t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.re w.re t.2)
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hright_mem : ∀ t : I, Path.segment zw w t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.im w.im t.2)
  have htop_mem : ∀ t : I, Path.segment w wz t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.re) (b := w.re) t
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hleft_mem : ∀ t : I, Path.segment wz z t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.im) (b := w.im) t
  have hbottom_int : CurveIntegrable ω (Path.segment z zw) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω hbottom_mem
  have hright_int : CurveIntegrable ω (Path.segment zw w) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω hright_mem
  have htop_int : CurveIntegrable ω (Path.segment w wz) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω htop_mem
  have hleft_int : CurveIntegrable ω (Path.segment wz z) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω hleft_mem
  -- The boundary path is the concatenation of the four affine sides.
  simpa [axisParallelRectangleBoundaryPath, zw, wz] using
    (CurveIntegrable.trans hbottom_int
      (CurveIntegrable.trans hright_int
        (CurveIntegrable.trans htop_int hleft_int)))

/-- Helper for Theorem II.1-extra-5: the boundary integral of a continuous real-valued `1`-form
splits into the four oriented side integrals of the rectangle. -/
lemma rectangle_boundary_integral_eq {ω : ℂ → ℂ →L[ℝ] ℝ}
    (hω : ContinuousOn ω Rect) :
    ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, ω ζ =
      (∫ x in z.re..w.re, ω (Complex.mk x z.im) 1) +
        (∫ y in z.im..w.im, ω (Complex.mk w.re y) Complex.I) +
          (∫ x in w.re..z.re, ω (Complex.mk x w.im) 1) +
            ∫ y in w.im..z.im, ω (Complex.mk z.re y) Complex.I := by
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  have hbottom_mem : ∀ t : I, Path.segment z zw t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.re w.re t.2)
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hright_mem : ∀ t : I, Path.segment zw w t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.im w.im t.2)
  have htop_mem : ∀ t : I, Path.segment w wz t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.re) (b := w.re) t
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hleft_mem : ∀ t : I, Path.segment wz z t ∈ Rect := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.im) (b := w.im) t
  have hbottom_int : CurveIntegrable ω (Path.segment z zw) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω hbottom_mem
  have hright_int : CurveIntegrable ω (Path.segment zw w) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω hright_mem
  have htop_int : CurveIntegrable ω (Path.segment w wz) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω htop_mem
  have hleft_int : CurveIntegrable ω (Path.segment wz z) :=
    rectangle_side_curveIntegrable (z := z) (w := w) hω hleft_mem
  -- Expand the concatenated boundary path into its four affine sides.
  rw [axisParallelRectangleBoundaryPath]
  rw [curveIntegral_trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))]
  rw [curveIntegral_trans hright_int (CurveIntegrable.trans htop_int hleft_int)]
  rw [curveIntegral_trans htop_int hleft_int]
  -- Rewrite the form in planar coordinates and evaluate each side separately.
  rw [one_form_eq_planarDifferentialForm ω]
  rw [horizontal_segment_pdx_eq_intervalIntegral (P0 := fun ζ ↦ ω ζ 1)
    (Q0 := fun ζ ↦ ω ζ Complex.I) (x₁ := z.re)
    (x₂ := w.re) (b := z.im)]
  rw [vertical_segment_qdy_eq_intervalIntegral (P0 := fun ζ ↦ ω ζ 1)
    (Q0 := fun ζ ↦ ω ζ Complex.I) (a := w.re)
    (y₁ := z.im) (y₂ := w.im)]
  rw [horizontal_segment_pdx_eq_intervalIntegral (P0 := fun ζ ↦ ω ζ 1)
    (Q0 := fun ζ ↦ ω ζ Complex.I) (x₁ := w.re)
    (x₂ := z.re) (b := w.im)]
  rw [vertical_segment_qdy_eq_intervalIntegral (P0 := fun ζ ↦ ω ζ 1)
    (Q0 := fun ζ ↦ ω ζ Complex.I) (a := z.re)
    (y₁ := w.im) (y₂ := z.im)]
  simp [add_assoc]

/-- Helper for Theorem II.1-extra-5: the `Q dy` contribution along the rectangle boundary equals
the iterated integral of `∂Q/∂x` in the source-proof order. -/
lemma rectangle_boundary_qdy_eq_integral_partial_x
    (hQ_cont : ContinuousOn Q Rect)
    (hdQdx_cont : ContinuousOn dQdx Rect)
    (hQ_dx : ∀ ζ ∈ interior Rect,
      HasDerivAt (fun x ↦ Q (Complex.mk x ζ.im)) (dQdx ζ) ζ.re) :
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, ((0 : ℂ → ℝ) dx + Q dy) ζ) =
      ∫ y in z.im..w.im, ∫ x in z.re..w.re, dQdx (Complex.mk x y) := by
  have hω_cont : ContinuousOn (((0 : ℂ → ℝ) dx + Q dy)) Rect := by
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := Rect) (P := (0 : ℂ → ℝ)) (Q := Q)
        continuousOn_const hQ_cont)
  have hright_slice_cont :
      ContinuousOn (fun y ↦ Q (Complex.mk w.re y)) (Set.uIcc z.im w.im) := by
    refine hQ_cont.comp (continuousOn_complex_mk_left (a := w.re) (s := Set.uIcc z.im w.im)) ?_
    intro y hy
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨by simp [Set.uIcc], hy⟩
  have hleft_slice_cont :
      ContinuousOn (fun y ↦ Q (Complex.mk z.re y)) (Set.uIcc z.im w.im) := by
    refine hQ_cont.comp (continuousOn_complex_mk_left (a := z.re) (s := Set.uIcc z.im w.im)) ?_
    intro y hy
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨by simp [Set.uIcc], hy⟩
  have hftc :
      ∀ y ∈ Set.uIoo z.im w.im,
        ∫ x in z.re..w.re, dQdx (Complex.mk x y) =
          Q (Complex.mk w.re y) - Q (Complex.mk z.re y) := by
    intro y hy
    have hy_mem : y ∈ Set.uIcc z.im w.im := by
      simpa [Set.uIcc] using (Set.Ioo_subset_Icc_self hy)
    have hcont_slice : ContinuousOn (fun x ↦ Q (Complex.mk x y)) (Set.uIcc z.re w.re) := by
      refine hQ_cont.comp (continuousOn_complex_mk_right (b := y) (s := Set.uIcc z.re w.re)) ?_
      intro x hx
      simpa [Complex.Rectangle, Complex.mem_reProdIm] using ⟨hx, hy_mem⟩
    have hdQdx_slice : ContinuousOn (fun x ↦ dQdx (Complex.mk x y)) (Set.uIcc z.re w.re) := by
      refine hdQdx_cont.comp (continuousOn_complex_mk_right (b := y) (s := Set.uIcc z.re w.re)) ?_
      intro x hx
      simpa [Complex.Rectangle, Complex.mem_reProdIm] using ⟨hx, hy_mem⟩
    have hderiv_slice :
        ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re),
          HasDerivWithinAt (fun x ↦ Q (Complex.mk x y)) (dQdx (Complex.mk x y)) (Set.Ioi x) x := by
      intro x hx
      have hxy : Complex.mk x y ∈ interior Rect := by
        rw [Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
        constructor
        · simpa [Set.uIcc, interior_Icc] using hx
        · simpa [Set.uIcc, interior_Icc, Set.uIoo] using hy
      exact (hQ_dx (Complex.mk x y) hxy).hasDerivWithinAt
    have hint_slice : IntervalIntegrable (fun x ↦ dQdx (Complex.mk x y)) volume z.re w.re :=
      hdQdx_slice.intervalIntegrable
    -- Apply the one-variable FTC in the `x`-direction for this fixed interior `y`.
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont_slice hderiv_slice hint_slice)
  -- Expand the boundary path into side integrals, then discard the horizontal contributions.
  rw [rectangle_boundary_integral_eq (z := z) (w := w) (ω := ((0 : ℂ → ℝ) dx + Q dy)) hω_cont]
  simp only [Complex.planarDifferentialForm_apply, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, Pi.zero_apply, zero_smul, one_smul, zero_add, add_zero,
    intervalIntegral.integral_zero]
  rw [show (∫ y in w.im..z.im, Q (Complex.mk z.re y)) = -∫ y in z.im..w.im, Q (Complex.mk z.re y) by
    exact intervalIntegral.integral_symm _ _]
  rw [show (∫ y in z.im..w.im, Q (Complex.mk w.re y)) + -∫ y in z.im..w.im, Q (Complex.mk z.re y) =
      ∫ y in z.im..w.im, (Q (Complex.mk w.re y) - Q (Complex.mk z.re y)) by
      simpa [sub_eq_add_neg] using
        (intervalIntegral.integral_sub hright_slice_cont.intervalIntegrable
          hleft_slice_cont.intervalIntegrable).symm]
  -- Replace the boundary difference by the inner integral using the FTC almost everywhere in `y`.
  refine (intervalIntegral.integral_congr_ae_restrict ?_).symm
  rcases le_total z.im w.im with hy | hy
  · rw [Set.uIoc_of_le hy]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with y hyIoo
    simpa [Set.uIoo, hy] using hftc y (by simpa [Set.uIoo, hy] using hyIoo)
  · rw [Set.uIoc_of_ge hy]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with y hyIoo
    simpa [Set.uIoo, hy] using hftc y (by simpa [Set.uIoo, hy] using hyIoo)

/-- Helper for Theorem II.1-extra-5: the `P dx` contribution along the rectangle boundary equals
minus the iterated integral of `∂P/∂y`. -/
lemma rectangle_boundary_pdx_eq_neg_integral_partial_y
    (hP_cont : ContinuousOn P Rect)
    (hdPdy_cont : ContinuousOn dPdy Rect)
    (hP_dy : ∀ ζ ∈ interior Rect,
      HasDerivAt (fun y ↦ P (Complex.mk ζ.re y)) (dPdy ζ) ζ.im) :
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + (0 : ℂ → ℝ) dy) ζ) =
      -∫ x in z.re..w.re, ∫ y in z.im..w.im, dPdy (Complex.mk x y) := by
  have hω_cont : ContinuousOn ((P dx + (0 : ℂ → ℝ) dy)) Rect := by
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := Rect) (P := P) (Q := (0 : ℂ → ℝ))
        hP_cont continuousOn_const)
  have hbottom_slice_cont :
      ContinuousOn (fun x ↦ P (Complex.mk x z.im)) (Set.uIcc z.re w.re) := by
    refine hP_cont.comp (continuousOn_complex_mk_right (b := z.im) (s := Set.uIcc z.re w.re)) ?_
    intro x hx
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨hx, by simp [Set.uIcc]⟩
  have htop_slice_cont :
      ContinuousOn (fun x ↦ P (Complex.mk x w.im)) (Set.uIcc z.re w.re) := by
    refine hP_cont.comp (continuousOn_complex_mk_right (b := w.im) (s := Set.uIcc z.re w.re)) ?_
    intro x hx
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨hx, by simp [Set.uIcc]⟩
  have hftc :
      ∀ x ∈ Set.uIoo z.re w.re,
        ∫ y in z.im..w.im, dPdy (Complex.mk x y) =
          P (Complex.mk x w.im) - P (Complex.mk x z.im) := by
    intro x hx
    have hx_mem : x ∈ Set.uIcc z.re w.re := by
      simpa [Set.uIcc] using (Set.Ioo_subset_Icc_self hx)
    have hcont_slice : ContinuousOn (fun y ↦ P (Complex.mk x y)) (Set.uIcc z.im w.im) := by
      refine hP_cont.comp (continuousOn_complex_mk_left (a := x) (s := Set.uIcc z.im w.im)) ?_
      intro y hy
      simpa [Complex.Rectangle, Complex.mem_reProdIm] using ⟨hx_mem, hy⟩
    have hdPdy_slice : ContinuousOn (fun y ↦ dPdy (Complex.mk x y)) (Set.uIcc z.im w.im) := by
      refine hdPdy_cont.comp (continuousOn_complex_mk_left (a := x) (s := Set.uIcc z.im w.im)) ?_
      intro y hy
      simpa [Complex.Rectangle, Complex.mem_reProdIm] using ⟨hx_mem, hy⟩
    have hderiv_slice :
        ∀ y ∈ Set.Ioo (min z.im w.im) (max z.im w.im),
          HasDerivWithinAt (fun y ↦ P (Complex.mk x y)) (dPdy (Complex.mk x y)) (Set.Ioi y) y := by
      intro y hy
      have hxy : Complex.mk x y ∈ interior Rect := by
        rw [Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
        constructor
        · simpa [Set.uIcc, interior_Icc, Set.uIoo] using hx
        · simpa [Set.uIcc, interior_Icc] using hy
      exact (hP_dy (Complex.mk x y) hxy).hasDerivWithinAt
    have hint_slice : IntervalIntegrable (fun y ↦ dPdy (Complex.mk x y)) volume z.im w.im :=
      hdPdy_slice.intervalIntegrable
    -- Apply the one-variable FTC in the `y`-direction for this fixed interior `x`.
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont_slice hderiv_slice hint_slice)
  -- Expand the boundary path into side integrals, then discard the vertical contributions.
  rw [rectangle_boundary_integral_eq (z := z) (w := w) (ω := (P dx + (0 : ℂ → ℝ) dy)) hω_cont]
  simp only [Complex.planarDifferentialForm_apply, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, Pi.zero_apply, zero_smul, one_smul, add_zero,
    intervalIntegral.integral_zero]
  rw [show (∫ x in w.re..z.re, P (Complex.mk x w.im)) = -∫ x in z.re..w.re, P (Complex.mk x w.im) by
    exact intervalIntegral.integral_symm _ _]
  rw [show (∫ x in z.re..w.re, P (Complex.mk x z.im)) + -∫ x in z.re..w.re, P (Complex.mk x w.im) =
      ∫ x in z.re..w.re, (P (Complex.mk x z.im) - P (Complex.mk x w.im)) by
      simpa [sub_eq_add_neg] using
        (intervalIntegral.integral_sub hbottom_slice_cont.intervalIntegrable
          htop_slice_cont.intervalIntegrable).symm]
  -- Replace the boundary difference by the inner integral using the FTC almost everywhere in `x`.
  have hrewrite :
      (fun x ↦ P (Complex.mk x z.im) - P (Complex.mk x w.im))
        =ᵐ[volume.restrict (Set.uIoc z.re w.re)]
          fun x ↦ -∫ y in z.im..w.im, dPdy (Complex.mk x y) := by
    rcases le_total z.re w.re with hx | hx
    · rw [Set.uIoc_of_le hx]
      refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with x hxIoo
      have h := hftc x (by simpa [Set.uIoo, hx] using hxIoo)
      linarith
    · rw [Set.uIoc_of_ge hx]
      refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with x hxIoo
      have h := hftc x (by simpa [Set.uIoo, hx] using hxIoo)
      linarith
  rw [intervalIntegral.integral_congr_ae_restrict hrewrite, intervalIntegral.integral_neg]

/-- Helper for Theorem II.1-extra-5: continuity on the closed rectangle makes the corresponding
coordinate function integrable on the product of the interval-restricted volume measures. -/
lemma rectangle_uncurry_integrable {f : ℂ → ℝ} (hf : ContinuousOn f Rect) :
    Integrable (fun p : ℝ × ℝ ↦ f (Complex.mk p.1 p.2))
      ((volume.restrict (Set.uIoc z.re w.re)).prod (volume.restrict (Set.uIoc z.im w.im))) := by
  have hIcc :
      IntegrableOn (fun p : ℝ × ℝ ↦ f (Complex.mk p.1 p.2))
        (Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im) volume := by
    refine ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) ?_
    refine hf.comp (continuousOn_complex_mk_prod (s := Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im))
      ?_
    intro p hp
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact hp
  have hIoc :
      IntegrableOn (fun p : ℝ × ℝ ↦ f (Complex.mk p.1 p.2))
        (Set.uIoc z.re w.re ×ˢ Set.uIoc z.im w.im) volume := by
    refine hIcc.mono_set ?_
    intro p hp
    exact ⟨Set.uIoc_subset_uIcc hp.1, Set.uIoc_subset_uIcc hp.2⟩
  simpa [IntegrableOn, Measure.prod_restrict] using hIoc

/-- Helper for Theorem II.1-extra-5: Fubini swaps the two interval integrals of `∂Q/∂x` over the
rectangle. -/
lemma rectangle_partial_x_integral_swap_aux (hdQdx_cont : ContinuousOn dQdx Rect) :
    (∫ y in z.im..w.im, ∫ x in z.re..w.re, dQdx (Complex.mk x y)) =
      ∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y) := by
  let μy : Measure ℝ := volume.restrict (Set.uIoc z.im w.im)
  have hInt :
      Integrable (Function.uncurry fun x y ↦ dQdx (Complex.mk x y))
        ((volume.restrict (Set.uIoc z.re w.re)).prod μy) := by
    simpa [μy] using
      (rectangle_uncurry_integrable (z := z) (w := w) (f := dQdx) hdQdx_cont)
  have hswap :
      ∫ y, ∫ x in z.re..w.re, dQdx (Complex.mk x y) ∂volume ∂μy =
        ∫ x in z.re..w.re, ∫ y, dQdx (Complex.mk x y) ∂μy := by
    simpa [μy] using
      (intervalIntegral_integral_swap (μ := μy) (a := z.re) (b := w.re)
        (f := fun x y ↦ dQdx (Complex.mk x y)) hInt).symm
  rcases le_total z.im w.im with hy | hy
  · -- When the vertical orientation is standard, the restricted `y`-measure is the interval.
    simpa [μy, intervalIntegral.integral_of_le hy, Set.uIoc_of_le hy] using hswap
  · -- Reversing the vertical orientation introduces the same minus sign on both sides.
    have hswap_neg := congrArg (fun t : ℝ => -t) hswap
    simpa [μy, intervalIntegral.integral_of_ge hy, Set.uIoc_of_ge hy,
      intervalIntegral.integral_neg] using hswap_neg

/-- Helper for Theorem II.1-extra-5: when the rectangle bounds are ordered, the iterated
integrals of `∂Q/∂x` can be swapped. -/
lemma rectangle_partial_x_integral_swap_of_le (hx : z.re ≤ w.re) (hy : z.im ≤ w.im)
    (hdQdx_cont : ContinuousOn dQdx Rect) :
    (∫ y in z.im..w.im, ∫ x in z.re..w.re, dQdx (Complex.mk x y)) =
      ∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y) := by
  let _ := hx
  let _ := hy
  exact rectangle_partial_x_integral_swap_aux (z := z) (w := w) (dQdx := dQdx) hdQdx_cont

/-- Helper for Theorem II.1-extra-5: the iterated integrals of `∂Q/∂x` over the rectangle can be
swapped without assuming an ordering of the corners. -/
lemma rectangle_partial_x_integral_swap (hdQdx_cont : ContinuousOn dQdx Rect) :
    (∫ y in z.im..w.im, ∫ x in z.re..w.re, dQdx (Complex.mk x y)) =
      ∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y) := by
  exact rectangle_partial_x_integral_swap_aux (z := z) (w := w) (dQdx := dQdx) hdQdx_cont

/-- Helper for Theorem II.1-extra-5: linearity of the product integral pulls subtraction inside the
iterated integral over the rectangle. -/
lemma rectangle_iterated_integral_sub_aux
    (hdQdx_cont : ContinuousOn dQdx Rect) (hdPdy_cont : ContinuousOn dPdy Rect) :
    (∫ x in z.re..w.re, ∫ y in z.im..w.im,
        (dQdx (Complex.mk x y) - dPdy (Complex.mk x y))) =
      (∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y)) -
        ∫ x in z.re..w.re, ∫ y in z.im..w.im, dPdy (Complex.mk x y) := by
  let μx : Measure ℝ := volume.restrict (Set.uIoc z.re w.re)
  let μy : Measure ℝ := volume.restrict (Set.uIoc z.im w.im)
  have hIntQ :
      Integrable (fun p : ℝ × ℝ ↦ dQdx (Complex.mk p.1 p.2)) (μx.prod μy) := by
    simpa [μx, μy] using
      (rectangle_uncurry_integrable (z := z) (w := w) (f := dQdx) hdQdx_cont)
  have hIntP :
      Integrable (fun p : ℝ × ℝ ↦ dPdy (Complex.mk p.1 p.2)) (μx.prod μy) := by
    simpa [μx, μy] using
      (rectangle_uncurry_integrable (z := z) (w := w) (f := dPdy) hdPdy_cont)
  have hsub :
      (∫ x, ∫ y, (dQdx (Complex.mk x y) - dPdy (Complex.mk x y)) ∂μy ∂μx) =
        (∫ x, ∫ y, dQdx (Complex.mk x y) ∂μy ∂μx) -
          ∫ x, ∫ y, dPdy (Complex.mk x y) ∂μy ∂μx := by
    simpa [μx, μy] using
      (integral_integral_sub' (μ := μx) (ν := μy)
        (f := fun p : ℝ × ℝ ↦ dQdx (Complex.mk p.1 p.2))
        (g := fun p : ℝ × ℝ ↦ dPdy (Complex.mk p.1 p.2)) hIntQ hIntP)
  have hsub_neg := congrArg (fun t : ℝ => -t) hsub
  have hsub_y :
      (∫ x, ∫ y in z.im..w.im, (dQdx (Complex.mk x y) - dPdy (Complex.mk x y)) ∂volume ∂μx) =
        (∫ x, ∫ y in z.im..w.im, dQdx (Complex.mk x y) ∂volume ∂μx) -
          ∫ x, ∫ y in z.im..w.im, dPdy (Complex.mk x y) ∂volume ∂μx := by
    rcases le_total z.im w.im with hy | hy
    · -- First convert the inner restricted `y`-integrals to interval integrals.
      simpa [μy, intervalIntegral.integral_of_le hy, Set.uIoc_of_le hy] using hsub
    · -- If the vertical orientation is reversed, convert the negated equality instead.
      simpa [μy, intervalIntegral.integral_of_ge hy, Set.uIoc_of_ge hy,
        intervalIntegral.integral_neg, integral_neg, neg_sub, sub_eq_add_neg, add_comm] using
        hsub_neg
  rcases le_total z.re w.re with hx | hx
  · -- Then convert the outer restricted `x`-integral to the interval notation used by the theorem.
    simpa [μx, intervalIntegral.integral_of_le hx, Set.uIoc_of_le hx] using hsub_y
  · -- A reversed horizontal orientation again contributes one global minus sign.
    have hsub_y_neg := congrArg (fun t : ℝ => -t) hsub_y
    simpa [μx, intervalIntegral.integral_of_ge hx, Set.uIoc_of_ge hx,
      intervalIntegral.integral_neg, neg_sub, sub_eq_add_neg, add_comm] using hsub_y_neg

/-- Helper for Theorem II.1-extra-5: when the rectangle bounds are ordered, subtraction may be
pulled inside the iterated integral. -/
lemma rectangle_iterated_integral_sub_of_le (hx : z.re ≤ w.re) (hy : z.im ≤ w.im)
    (hdQdx_cont : ContinuousOn dQdx Rect) (hdPdy_cont : ContinuousOn dPdy Rect) :
    (∫ x in z.re..w.re, ∫ y in z.im..w.im,
        (dQdx (Complex.mk x y) - dPdy (Complex.mk x y))) =
      (∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y)) -
        ∫ x in z.re..w.re, ∫ y in z.im..w.im, dPdy (Complex.mk x y) := by
  let _ := hx
  let _ := hy
  exact rectangle_iterated_integral_sub_aux (z := z) (w := w) (dQdx := dQdx) (dPdy := dPdy)
    hdQdx_cont hdPdy_cont

/-- Helper for Theorem II.1-extra-5: subtraction may be pulled inside the iterated integral on an
arbitrarily oriented rectangle. -/
lemma rectangle_iterated_integral_sub
    (hdQdx_cont : ContinuousOn dQdx Rect) (hdPdy_cont : ContinuousOn dPdy Rect) :
    (∫ x in z.re..w.re, ∫ y in z.im..w.im,
        (dQdx (Complex.mk x y) - dPdy (Complex.mk x y))) =
      (∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y)) -
        ∫ x in z.re..w.re, ∫ y in z.im..w.im, dPdy (Complex.mk x y) := by
  exact rectangle_iterated_integral_sub_aux (z := z) (w := w) (dQdx := dQdx) (dPdy := dPdy)
    hdQdx_cont hdPdy_cont

/-- Theorem II.1-extra-5: for the axis-parallel rectangle with corners `z` and `w`, the
positively oriented boundary integral of `P dx + Q dy` equals the double integral of
`∂Q/∂x - ∂P/∂y` over `Complex.Rectangle z w`. -/
-- Proof sketch: this is the source-facing rectangle formula built on the canonical rectangle owner
-- `Complex.Rectangle z w`; one can derive it from the rectangle divergence theorem for the vector
-- field `(Q, -P)`, or by applying the one-variable fundamental theorem of calculus on each side and
-- then matching the resulting iterated integrals.
theorem green_riemann_formula
    (hP_cont : ContinuousOn P Rect)
    (hQ_cont : ContinuousOn Q Rect)
    (hdPdy_cont : ContinuousOn dPdy Rect)
    (hdQdx_cont : ContinuousOn dQdx Rect)
    (hP_dy : ∀ ζ ∈ interior Rect,
      HasDerivAt (fun y ↦ P (Complex.mk ζ.re y)) (dPdy ζ) ζ.im)
    (hQ_dx : ∀ ζ ∈ interior Rect,
      HasDerivAt (fun x ↦ Q (Complex.mk x ζ.im)) (dQdx ζ) ζ.re) :
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + Q dy) ζ) =
      ∫ x in z.re..w.re, ∫ y in z.im..w.im,
        (dQdx (Complex.mk x y) - dPdy (Complex.mk x y)) := by
  have hP_component_cont : ContinuousOn ((P dx + (0 : ℂ → ℝ) dy)) Rect := by
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := Rect) (P := P) (Q := (0 : ℂ → ℝ))
        hP_cont continuousOn_const)
  have hQ_component_cont : ContinuousOn (((0 : ℂ → ℝ) dx + Q dy)) Rect := by
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := Rect) (P := (0 : ℂ → ℝ)) (Q := Q)
        continuousOn_const hQ_cont)
  have hP_component_int :
      CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) (axisParallelRectangleBoundaryPath z w) :=
    rectangle_boundary_curveIntegrable (z := z) (w := w) hP_component_cont
  have hQ_component_int :
      CurveIntegrable ((0 : ℂ → ℝ) dx + Q dy) (axisParallelRectangleBoundaryPath z w) :=
    rectangle_boundary_curveIntegrable (z := z) (w := w) hQ_component_cont
  have hform_split :
      (P dx + Q dy) = (P dx + (0 : ℂ → ℝ) dy) + ((0 : ℂ → ℝ) dx + Q dy) := by
    ext ζ v
    simp [Complex.planarDifferentialForm, add_comm]
  have hsplit :
      (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + Q dy) ζ) =
        ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + (0 : ℂ → ℝ) dy) ζ +
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, ((0 : ℂ → ℝ) dx + Q dy) ζ := by
    -- Split the form into its horizontal and vertical parts before evaluating the boundary pieces.
    rw [hform_split]
    simpa using
      (curveIntegral_add hP_component_int hQ_component_int :
        curveIntegral ((P dx + (0 : ℂ → ℝ) dy) + ((0 : ℂ → ℝ) dx + Q dy))
          (axisParallelRectangleBoundaryPath z w) =
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + (0 : ℂ → ℝ) dy) ζ +
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, ((0 : ℂ → ℝ) dx + Q dy) ζ)
  -- Route correction: execute the source proof via side integrals and one-variable FTC, then use a
  -- separate swap lemma to match the target iterated-integral order.
  calc
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + Q dy) ζ) =
        (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + (0 : ℂ → ℝ) dy) ζ) +
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, ((0 : ℂ → ℝ) dx + Q dy) ζ := hsplit
    _ = (-∫ x in z.re..w.re, ∫ y in z.im..w.im, dPdy (Complex.mk x y)) +
          ∫ y in z.im..w.im, ∫ x in z.re..w.re, dQdx (Complex.mk x y) := by
      rw [rectangle_boundary_pdx_eq_neg_integral_partial_y (z := z) (w := w) (P := P)
        (dPdy := dPdy) hP_cont hdPdy_cont hP_dy]
      rw [rectangle_boundary_qdy_eq_integral_partial_x (z := z) (w := w) (Q := Q)
        (dQdx := dQdx) hQ_cont hdQdx_cont hQ_dx]
    _ = (-∫ x in z.re..w.re, ∫ y in z.im..w.im, dPdy (Complex.mk x y)) +
          ∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y) := by
      rw [rectangle_partial_x_integral_swap (z := z) (w := w) (dQdx := dQdx) hdQdx_cont]
    _ = (∫ x in z.re..w.re, ∫ y in z.im..w.im, dQdx (Complex.mk x y)) -
          ∫ x in z.re..w.re, ∫ y in z.im..w.im, dPdy (Complex.mk x y) := by
      ring
    _ = ∫ x in z.re..w.re, ∫ y in z.im..w.im,
          (dQdx (Complex.mk x y) - dPdy (Complex.mk x y)) := by
      symm
      exact rectangle_iterated_integral_sub (z := z) (w := w) (dQdx := dQdx) (dPdy := dPdy)
        hdQdx_cont hdPdy_cont

end
