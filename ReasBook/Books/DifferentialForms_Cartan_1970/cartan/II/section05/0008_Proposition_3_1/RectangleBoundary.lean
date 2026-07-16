import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0004_Definition_II_1_extra_4»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0014_Remark_II_1_extra_8»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0008_Proposition_3_1».PrimitiveSegments

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped unitInterval
open scoped Interval

/-- Helper for Cartan section05 0008_Proposition_3_1: taking the real part of a complex-valued
curve integral commutes with integration. -/
theorem curveIntegral_re_comp_eq
    {z w : ℂ} {γ : Path z w} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hInt : CurveIntegrable ω γ) :
    ∫ᶜ ζ in γ, Complex.reCLM.comp (ω ζ) = Complex.re (∫ᶜ ζ in γ, ω ζ) := by
  -- Rewrite both curve integrals as interval integrals and move `Complex.reCLM` across the
  -- Bochner integral in one step.
  rw [curveIntegral_def, curveIntegral_def]
  simpa [CurveIntegrable, curveIntegralFun, Function.comp] using
    Complex.reCLM.intervalIntegral_comp_comm (f := curveIntegralFun ω γ) hInt

/-- Helper for Cartan section05 0008_Proposition_3_1: taking the imaginary part of a
complex-valued curve integral commutes with integration. -/
theorem curveIntegral_im_comp_eq
    {z w : ℂ} {γ : Path z w} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hInt : CurveIntegrable ω γ) :
    ∫ᶜ ζ in γ, Complex.imCLM.comp (ω ζ) = Complex.im (∫ᶜ ζ in γ, ω ζ) := by
  -- Rewrite both curve integrals as interval integrals and move `Complex.imCLM` across the
  -- Bochner integral in one step.
  rw [curveIntegral_def, curveIntegral_def]
  simpa [CurveIntegrable, curveIntegralFun, Function.comp] using
    Complex.imCLM.intervalIntegral_comp_comm (f := curveIntegralFun ω γ) hInt

/-- Helper for Cartan section05 0008_Proposition_3_1: composing the planar form with the real-part
functional extracts the real parts of the coefficients. -/
lemma reCLM_comp_planarDifferentialForm (P Q : ℂ → ℂ) (z : ℂ) :
    Complex.reCLM.comp (Complex.planarDifferentialForm P Q z) =
      Complex.planarDifferentialForm (fun w ↦ (P w).re) (fun w ↦ (Q w).re) z := by
  -- Evaluate both real-valued forms on an arbitrary tangent vector and compare coordinates.
  ext v
  simp [Complex.planarDifferentialForm_apply]

/-- Helper for Cartan section05 0008_Proposition_3_1: composing the planar form with the
imaginary-part functional extracts the imaginary parts of the coefficients. -/
lemma imCLM_comp_planarDifferentialForm (P Q : ℂ → ℂ) (z : ℂ) :
    Complex.imCLM.comp (Complex.planarDifferentialForm P Q z) =
      Complex.planarDifferentialForm (fun w ↦ (P w).im) (fun w ↦ (Q w).im) z := by
  -- Evaluate both real-valued forms on an arbitrary tangent vector and compare coordinates.
  ext v
  simp [Complex.planarDifferentialForm_apply]

/-- Helper for Cartan section05 0008_Proposition_3_1: a complex one-variable derivative projects
to the corresponding real and imaginary scalar derivatives. -/
lemma hasDerivAtReIm
    {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).re) f'.re x ∧ HasDerivAt (fun t ↦ (f t).im) f'.im x := by
  constructor
  · -- Compose the complex derivative with the real-part linear functional.
    simpa [Function.comp] using (Complex.reCLM.hasFDerivAt.comp x h.hasFDerivAt).hasDerivAt
  · -- Compose the complex derivative with the imaginary-part linear functional.
    simpa [Function.comp] using (Complex.imCLM.hasFDerivAt.comp x h.hasFDerivAt).hasDerivAt

/-- Helper for Cartan section05 0008_Proposition_3_1: replacing the imaginary part of `z` by the
center's imaginary part cannot leave the surrounding ball. -/
lemma reAddImMul_mem_ball {c z : ℂ} {r : ℝ} (hz : z ∈ Metric.ball c r) :
    z.re + c.im * Complex.I ∈ Metric.ball c r := by
  -- Compare the two distance formulas after dropping the nonnegative imaginary contribution.
  suffices dist (z.re + c.im * Complex.I) c ≤ dist z c from lt_of_le_of_lt this hz
  rw [dist_eq_re_im, dist_eq_re_im, Real.le_sqrt (by positivity) (by positivity),
    Real.sq_sqrt (by positivity)]
  simp [sq_nonneg _]

/-- Helper for Cartan section05 0008_Proposition_3_1: nearby horizontal points through `z` stay
inside the ambient ball around `c`. -/
lemma mem_ball_horizontalSlice {c z : ℂ} {r x : ℝ}
    (hx : x ∈ Set.Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) :
    Complex.mk x z.im ∈ Metric.ball c r := by
  -- First place the horizontal slice in the smaller ball centered at `z`.
  set r₁ := r - dist z c
  set s := Set.Ioo (z.re - r₁) (z.re + r₁)
  have hs_ball : s ×ℂ ({z.im} : Set ℝ) ⊆ Metric.ball z r₁ := by
    rintro y ⟨hyRe, hyIm⟩
    rw [Metric.mem_ball, dist_eq_re_im, hyIm, sub_self, zero_pow two_ne_zero, add_zero,
      Real.sqrt_sq_eq_abs]
    grind [abs_lt]
  -- Then enlarge from the smaller ball to the ambient ball around `c`.
  suffices s ×ℂ ({z.im} : Set ℝ) ⊆ Metric.ball c r from this <| by
    simp [Complex.mem_reProdIm, s, r₁, hx]
  exact hs_ball.trans <| ball_subset_ball' <| by simp [r₁]

/-- Helper for Cartan section05 0008_Proposition_3_1: vertical interpolation inside a closed ball
stays inside that closed ball. -/
lemma mem_closedBall_verticalSlice {c z : ℂ} {r y : ℝ}
    (hz : z ∈ Metric.closedBall c r) (hy : y ∈ Ι c.im z.im) :
    Complex.mk z.re y ∈ Metric.closedBall c r := by
  -- Only the imaginary displacement changes, and the interval condition bounds its square.
  refine le_trans ?_ (Metric.mem_closedBall.mp hz)
  rw [dist_eq_re_im, dist_eq_re_im, Real.le_sqrt (by positivity) (by positivity),
    Real.sq_sqrt (by positivity)]
  suffices (y - c.im) ^ 2 ≤ (z.im - c.im) ^ 2 by simpa
  cases mem_uIoc.mp hy <;> nlinarith

/-- Helper for Cartan section05 0008_Proposition_3_1: a vertical segment whose endpoints lie in a
ball stays in that ball. -/
lemma image_verticalSegment_subset_ball {c : ℂ} {r a b₁ b₂ : ℝ}
    (hb₁ : Complex.mk a b₁ ∈ Metric.ball c r)
    (hb₂ : Complex.mk a b₂ ∈ Metric.ball c r) :
    (fun y : ℝ ↦ Complex.mk a y) '' [[b₁, b₂]] ⊆ Metric.ball c r := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  have hySeg : y ∈ segment ℝ b₁ b₂ := by
    simpa [segment_eq_uIcc] using hy
  rw [segment_eq_image_lineMap] at hySeg
  rcases hySeg with ⟨t, ht, rfl⟩
  -- Repackage the vertical slice point as a point on the complex segment between the endpoints.
  exact (convex_ball c r).segment_subset hb₁ hb₂ <| by
    have hEq :
        Complex.mk a (AffineMap.lineMap b₁ b₂ t) =
          AffineMap.lineMap (Complex.mk a b₁) (Complex.mk a b₂) t := by
      apply Complex.ext <;> simp [AffineMap.lineMap_apply]
    simpa [hEq] using
      (lineMap_mem_segment ℝ (Complex.mk a b₁) (Complex.mk a b₂) ht)

/-- Helper for Cartan section05 0008_Proposition_3_1: a horizontal segment whose endpoints lie in a
ball stays in that ball. -/
lemma image_horizontalSegment_subset_ball {c : ℂ} {r a₁ a₂ b : ℝ}
    (ha₁ : Complex.mk a₁ b ∈ Metric.ball c r)
    (ha₂ : Complex.mk a₂ b ∈ Metric.ball c r) :
    (fun x : ℝ ↦ Complex.mk x b) '' [[a₁, a₂]] ⊆ Metric.ball c r := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxSeg : x ∈ segment ℝ a₁ a₂ := by
    simpa [segment_eq_uIcc] using hx
  rw [segment_eq_image_lineMap] at hxSeg
  rcases hxSeg with ⟨t, ht, rfl⟩
  -- Repackage the horizontal slice point as a point on the complex segment between the endpoints.
  exact (convex_ball c r).segment_subset ha₁ ha₂ <| by
    have hEq :
        Complex.mk (AffineMap.lineMap a₁ a₂ t) b =
          AffineMap.lineMap (Complex.mk a₁ b) (Complex.mk a₂ b) t := by
      apply Complex.ext <;> simp [AffineMap.lineMap_apply]
    simpa [hEq] using
      (lineMap_mem_segment ℝ (Complex.mk a₁ b) (Complex.mk a₂ b) ht)

/-- Helper for Cartan section05 0008_Proposition_3_1: a nearby vertical slice through `w` stays
inside the ambient ball around `c`. -/
lemma image_verticalSlice_subset_ball_of_mem {c z w : ℂ} {r : ℝ}
    (hw : w ∈ Metric.ball z (r - dist z c)) :
    (fun y : ℝ ↦ Complex.mk w.re y) '' [[z.im, w.im]] ⊆ Metric.ball c r := by
  have hwCorner : w ∈ Metric.ball c r := by
    exact Metric.ball_subset_ball' (by linarith) hw
  have hzCorner : Complex.mk w.re z.im ∈ Metric.ball c r := by
    have hwre_le : |w.re - z.re| ≤ dist w z := by
      simpa [Complex.sub_re, dist_eq_norm] using (Complex.abs_re_le_norm (w - z))
    have hwre :
        |w.re - z.re| < r - dist z c := by
      exact lt_of_le_of_lt hwre_le (by simpa [dist_comm] using hw)
    have hwre_mem :
        w.re ∈ Set.Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c)) := by
      rcases abs_lt.mp hwre with ⟨hleft, hright⟩
      constructor <;> linarith
    -- Keep the horizontal corner inside the ambient ball by first staying in the smaller ball
    -- centered at `z`.
    exact mem_ball_horizontalSlice (c := c) (z := z) (r := r) hwre_mem
  -- Both endpoints of the vertical slice lie in the ambient ball, so convexity keeps the full
  -- slice in the ball.
  exact image_verticalSegment_subset_ball hzCorner hwCorner

/-- Helper for Cartan section05 0008_Proposition_3_1: if `w` stays in the smaller ball around
`z`, then the whole axis-parallel rectangle with corners `z` and `w` stays in the ambient ball
around `c`. -/
lemma rectangle_subset_ball_of_mem {c z w : ℂ} {r : ℝ}
    (hz : z ∈ Metric.ball c r) (hw : w ∈ Metric.ball z (r - dist z c)) :
    Complex.Rectangle z w ⊆ Metric.ball c r := by
  have hwBall : w ∈ Metric.ball c r := by
    exact Metric.ball_subset_ball' (by linarith) hw
  have hrightCorner : Complex.mk w.re z.im ∈ Metric.ball c r := by
    have hwre_le : |w.re - z.re| ≤ dist w z := by
      simpa [Complex.sub_re, dist_eq_norm] using (Complex.abs_re_le_norm (w - z))
    have hwre :
        |w.re - z.re| < r - dist z c := by
      exact lt_of_le_of_lt hwre_le (by simpa [dist_comm] using hw)
    have hwre_mem :
        w.re ∈ Set.Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c)) := by
      rcases abs_lt.mp hwre with ⟨hleft, hright⟩
      constructor <;> linarith
    exact mem_ball_horizontalSlice (c := c) (z := z) (r := r) hwre_mem
  have htopCorner : Complex.mk z.re w.im ∈ Metric.ball c r := by
    have hwim_le : dist (Complex.mk z.re w.im) z ≤ dist w z := by
      have habs : |w.im - z.im| ≤ dist w z := by
        simpa [Complex.sub_im, dist_eq_norm] using (Complex.abs_im_le_norm (w - z))
      rw [Complex.dist_of_re_eq (by simp)]
      simpa [Real.dist_eq, abs_sub_comm] using habs
    have hsmall : Complex.mk z.re w.im ∈ Metric.ball z (r - dist z c) := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hwim_le (by simpa [Metric.mem_ball, dist_comm] using hw)
    exact Metric.ball_subset_ball' (by linarith) hsmall
  have hrightCorner' : w.re + z.im * Complex.I ∈ Metric.ball c r := by
    have hEq : (w.re + z.im * Complex.I : ℂ) = Complex.mk w.re z.im := by
      apply Complex.ext <;> simp
    simpa [hEq] using hrightCorner
  have htopCorner' : z.re + w.im * Complex.I ∈ Metric.ball c r := by
    have hEq : (z.re + w.im * Complex.I : ℂ) = Complex.mk z.re w.im := by
      apply Complex.ext <;> simp
    simpa [hEq] using htopCorner
  -- An open ball is convex, so once the four rectangle corners lie in it, the whole rectangle
  -- does as well.
  exact Complex.Convex.rectangle_subset (convex_ball c r) hz hwBall htopCorner' hrightCorner'

/-- Helper for Cartan section05 0008_Proposition_3_1: a continuous complex planar form is curve
integrable along the full boundary of an axis-parallel rectangle. -/
lemma rectangleBoundary_curveIntegrable_complex {z w : ℂ} {P Q : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Complex.Rectangle z w))
    (hQ_cont : ContinuousOn Q (Complex.Rectangle z w)) :
    CurveIntegrable (Complex.planarDifferentialForm P Q) (axisParallelRectangleBoundaryPath z w) := by
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  have hω_cont : ContinuousOn (Complex.planarDifferentialForm P Q) (Complex.Rectangle z w) := by
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := Complex.Rectangle z w) (P := P) (Q := Q)
        hP_cont hQ_cont)
  have hbottom_mem : ∀ t : I, Path.segment z zw t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.re w.re t.2)
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hright_mem : ∀ t : I, Path.segment zw w t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.im w.im t.2)
  have htop_mem : ∀ t : I, Path.segment w wz t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.re) (b := w.re) t
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hleft_mem : ∀ t : I, Path.segment wz z t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.im) (b := w.im) t
  have hbottom_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment z zw) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn z zw) hbottom_mem
  have hright_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment zw w) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn zw w) hright_mem
  have htop_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment w wz) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn w wz) htop_mem
  have hleft_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment wz z) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn wz z) hleft_mem
  -- The complex boundary path is the same four-segment concatenation used in the real Green
  -- formula, so the generic curve-integrability API applies side by side.
  simpa [axisParallelRectangleBoundaryPath, zw, wz] using
    (CurveIntegrable.trans hbottom_int
      (CurveIntegrable.trans hright_int
        (CurveIntegrable.trans htop_int hleft_int)))

/-- Helper for Cartan section05 0008_Proposition_3_1: on a rectangle where `P` and `Q` are
continuous, the complex boundary integral splits into the forward and reverse wedge integrals. -/
lemma rectangleBoundaryIntegral_eq_ballPrimitiveSum {z w : ℂ} {P Q : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Complex.Rectangle z w))
    (hQ_cont : ContinuousOn Q (Complex.Rectangle z w)) :
    ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, Complex.planarDifferentialForm P Q ζ =
      ballPrimitive z P Q w + ballPrimitive w P Q z := by
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  have hω_cont : ContinuousOn (Complex.planarDifferentialForm P Q) (Complex.Rectangle z w) := by
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := Complex.Rectangle z w) (P := P) (Q := Q)
        hP_cont hQ_cont)
  have hbottom_mem : ∀ t : I, Path.segment z zw t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.re w.re t.2)
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hright_mem : ∀ t : I, Path.segment zw w t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.im w.im t.2)
  have htop_mem : ∀ t : I, Path.segment w wz t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.re) (b := w.re) t
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hleft_mem : ∀ t : I, Path.segment wz z t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.im) (b := w.im) t
  have hbottom_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment z zw) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn z zw) hbottom_mem
  have hright_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment zw w) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn zw w) hright_mem
  have htop_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment w wz) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn w wz) htop_mem
  have hleft_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (Path.segment wz z) :=
    hω_cont.curveIntegrable_of_contDiffOn (segment_contDiffOn wz z) hleft_mem
  -- Expand the boundary path into its four sides before rewriting each side by the source-style
  -- horizontal and vertical interval integrals.
  calc
    ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, Complex.planarDifferentialForm P Q ζ =
        ((∫ᶜ ζ in Path.segment z zw, Complex.planarDifferentialForm P Q ζ +
            ∫ᶜ ζ in Path.segment zw w, Complex.planarDifferentialForm P Q ζ) +
          ∫ᶜ ζ in Path.segment w wz, Complex.planarDifferentialForm P Q ζ) +
            ∫ᶜ ζ in Path.segment wz z, Complex.planarDifferentialForm P Q ζ := by
      rw [axisParallelRectangleBoundaryPath]
      rw [curveIntegral_trans hbottom_int (CurveIntegrable.trans hright_int
        (CurveIntegrable.trans htop_int hleft_int))]
      rw [curveIntegral_trans hright_int (CurveIntegrable.trans htop_int hleft_int)]
      rw [curveIntegral_trans htop_int hleft_int]
      simp [add_assoc]
    _ = (((∫ x in z.re..w.re, P (Complex.mk x z.im)) +
            ∫ y in z.im..w.im, Q (Complex.mk w.re y)) +
          ∫ x in w.re..z.re, P (Complex.mk x w.im)) +
            ∫ y in w.im..z.im, Q (Complex.mk z.re y) := by
      rw [horizontal_segment_planarIntegral_eq_intervalIntegral (P := P) (Q := Q)
          (x₀ := z.re) (x₁ := w.re) (b := z.im)]
      rw [vertical_segment_planarIntegral_eq_intervalIntegral (P := P) (Q := Q)
          (a := w.re) (y₀ := z.im) (y₁ := w.im)]
      rw [horizontal_segment_planarIntegral_eq_intervalIntegral (P := P) (Q := Q)
          (x₀ := w.re) (x₁ := z.re) (b := w.im)]
      rw [vertical_segment_planarIntegral_eq_intervalIntegral (P := P) (Q := Q)
          (a := z.re) (y₀ := w.im) (y₁ := z.im)]
    _ = ballPrimitive z P Q w + ballPrimitive w P Q z := by
      simp [ballPrimitive, add_assoc]

/-- Helper for Cartan section05 0008_Proposition_3_1: if the mixed partials agree on a ball, then
every axis-parallel rectangle inside that ball has zero complex boundary integral. -/
lemma rectangleBoundaryIntegral_eq_zero_onBall_of_partialDeriv_eq
    {c : ℂ} {r : ℝ} {P Q dPdy dQdx : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Metric.ball c r))
    (hQ_cont : ContinuousOn Q (Metric.ball c r))
    (hdPdy_cont : ContinuousOn dPdy (Metric.ball c r))
    (hP_dy : ∀ z ∈ Metric.ball c r, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ Metric.ball c r, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hpartial : ∀ z ∈ Metric.ball c r, dPdy z = dQdx z) :
    ∀ w₀ w₁ : ℂ,
      Complex.Rectangle w₀ w₁ ⊆ Metric.ball c r →
        ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁, Complex.planarDifferentialForm P Q ζ = 0 := by
  intro w₀ w₁ hrect
  have hP_rect : ContinuousOn P (Complex.Rectangle w₀ w₁) := hP_cont.mono hrect
  have hQ_rect : ContinuousOn Q (Complex.Rectangle w₀ w₁) := hQ_cont.mono hrect
  have hInt :
      CurveIntegrable (Complex.planarDifferentialForm P Q) (axisParallelRectangleBoundaryPath w₀ w₁) :=
    rectangleBoundary_curveIntegrable_complex hP_rect hQ_rect
  have hdPdy_re_rect : ContinuousOn (fun z ↦ (dPdy z).re) (Complex.Rectangle w₀ w₁) := by
    -- The real-part mixed partial is continuous on the chosen rectangle because it is continuous
    -- on the ambient ball.
    exact Complex.continuous_re.comp_continuousOn (hdPdy_cont.mono hrect)
  have hdPdy_im_rect : ContinuousOn (fun z ↦ (dPdy z).im) (Complex.Rectangle w₀ w₁) := by
    -- The imaginary-part mixed partial is continuous on the chosen rectangle for the same reason.
    exact Complex.continuous_im.comp_continuousOn (hdPdy_cont.mono hrect)
  have hre_zero :
      ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
        Complex.planarDifferentialForm (fun z ↦ (P z).re) (fun z ↦ (Q z).re) ζ = 0 := by
    -- Route correction: call Green's formula on the projected real-valued coefficients, using
    -- `hpartial` only to identify the two projected mixed partials.
    rw [green_riemann_formula
      (P := fun z ↦ (P z).re) (Q := fun z ↦ (Q z).re)
      (dPdy := fun z ↦ (dPdy z).re) (dQdx := fun z ↦ (dPdy z).re)
      (z := w₀) (w := w₁)]
    · simp
    · exact Complex.continuous_re.comp_continuousOn hP_rect
    · exact Complex.continuous_re.comp_continuousOn hQ_rect
    · exact hdPdy_re_rect
    · exact hdPdy_re_rect
    · intro z hz
      -- Project the `y`-derivative of `P` to the real axis.
      exact (hasDerivAtReIm (hP_dy z (hrect <| interior_subset hz))).1
    · intro z hz
      -- Project the `x`-derivative of `Q` to the real axis, then rewrite the derivative value
      -- using the mixed-partial equality on the ball.
      simpa [hpartial z (hrect <| interior_subset hz)] using
        (hasDerivAtReIm (hQ_dx z (hrect <| interior_subset hz))).1
  have him_zero :
      ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
        Complex.planarDifferentialForm (fun z ↦ (P z).im) (fun z ↦ (Q z).im) ζ = 0 := by
    -- Apply the same projected Green argument to the imaginary parts.
    rw [green_riemann_formula
      (P := fun z ↦ (P z).im) (Q := fun z ↦ (Q z).im)
      (dPdy := fun z ↦ (dPdy z).im) (dQdx := fun z ↦ (dPdy z).im)
      (z := w₀) (w := w₁)]
    · simp
    · exact Complex.continuous_im.comp_continuousOn hP_rect
    · exact Complex.continuous_im.comp_continuousOn hQ_rect
    · exact hdPdy_im_rect
    · exact hdPdy_im_rect
    · intro z hz
      -- Project the `y`-derivative of `P` to the imaginary axis.
      exact (hasDerivAtReIm (hP_dy z (hrect <| interior_subset hz))).2
    · intro z hz
      -- Project the `x`-derivative of `Q` to the imaginary axis, then rewrite by `hpartial`.
      simpa [hpartial z (hrect <| interior_subset hz)] using
        (hasDerivAtReIm (hQ_dx z (hrect <| interior_subset hz))).2
  -- Once both scalar projections vanish, the original complex boundary integral vanishes too.
  apply Complex.ext
  · have hre_eq :
        Complex.re (∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
            Complex.planarDifferentialForm P Q ζ) =
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
            Complex.planarDifferentialForm (fun z ↦ (P z).re) (fun z ↦ (Q z).re) ζ := by
      calc
        Complex.re (∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
            Complex.planarDifferentialForm P Q ζ) =
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
              Complex.reCLM.comp (Complex.planarDifferentialForm P Q ζ) := by
          simpa using
            (curveIntegral_re_comp_eq
              (γ := axisParallelRectangleBoundaryPath w₀ w₁)
              (ω := fun z ↦ Complex.planarDifferentialForm P Q z) hInt).symm
        _ = ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
              Complex.planarDifferentialForm (fun z ↦ (P z).re) (fun z ↦ (Q z).re) ζ := by
          rw [show
              (fun ζ ↦ Complex.reCLM.comp (Complex.planarDifferentialForm P Q ζ)) =
                fun ζ ↦
                  Complex.planarDifferentialForm (fun z ↦ (P z).re) (fun z ↦ (Q z).re) ζ by
                funext ζ
                exact reCLM_comp_planarDifferentialForm P Q ζ]
    exact hre_eq.trans hre_zero
  · have him_eq :
        Complex.im (∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
            Complex.planarDifferentialForm P Q ζ) =
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
            Complex.planarDifferentialForm (fun z ↦ (P z).im) (fun z ↦ (Q z).im) ζ := by
      calc
        Complex.im (∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
            Complex.planarDifferentialForm P Q ζ) =
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
              Complex.imCLM.comp (Complex.planarDifferentialForm P Q ζ) := by
          simpa using
            (curveIntegral_im_comp_eq
              (γ := axisParallelRectangleBoundaryPath w₀ w₁)
              (ω := fun z ↦ Complex.planarDifferentialForm P Q z) hInt).symm
        _ = ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
              Complex.planarDifferentialForm (fun z ↦ (P z).im) (fun z ↦ (Q z).im) ζ := by
          rw [show
              (fun ζ ↦ Complex.imCLM.comp (Complex.planarDifferentialForm P Q ζ)) =
                fun ζ ↦
                  Complex.planarDifferentialForm (fun z ↦ (P z).im) (fun z ↦ (Q z).im) ζ by
                funext ζ
                exact imCLM_comp_planarDifferentialForm P Q ζ]
    exact him_eq.trans him_zero
