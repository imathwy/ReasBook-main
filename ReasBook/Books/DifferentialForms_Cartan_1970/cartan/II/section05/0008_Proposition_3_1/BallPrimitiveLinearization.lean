import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0004_Definition_II_1_extra_4»
import DifferentialForms_Cartan_1970.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.II.section05.«0014_Remark_II_1_extra_8»
import DifferentialForms_Cartan_1970.II.section05.«0008_Proposition_3_1».PrimitiveSegments
import DifferentialForms_Cartan_1970.II.section05.«0008_Proposition_3_1».RectangleBoundary

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped unitInterval
open scoped Interval

/-- Helper for Cartan section05 0008_Proposition_3_1: near a point `z` in the ball, the explicit
primitive based at `c` differs from its value at `z` by the local wedge integral from `z` to `w`. -/
lemma eventually_ballPrimitive_sub_eq_localWedge
    {c z : ℂ} {r : ℝ} {P Q : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Metric.ball c r))
    (hQ_cont : ContinuousOn Q (Metric.ball c r))
    (hz : z ∈ Metric.ball c r)
    (hrectangle :
      ∀ w₀ w₁ : ℂ,
        Complex.Rectangle w₀ w₁ ⊆ Metric.ball c r →
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁, Complex.planarDifferentialForm P Q ζ = 0) :
    ∀ᶠ w in 𝓝 z, ballPrimitive c P Q w - ballPrimitive c P Q z = ballPrimitive z P Q w := by
  refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w hw ↦ ?_⟩
  set I₁ := ∫ x in c.re..w.re, P (Complex.mk x c.im)
  set I₂ := ∫ y in c.im..w.im, Q (Complex.mk w.re y)
  set I₃ := ∫ x in c.re..z.re, P (Complex.mk x c.im)
  set I₄ := ∫ y in c.im..z.im, Q (Complex.mk z.re y)
  set I₅ := ∫ x in z.re..w.re, P (Complex.mk x z.im)
  set I₆ := ∫ y in z.im..w.im, Q (Complex.mk w.re y)
  set I₇ := ∫ x in z.re..w.re, P (Complex.mk x c.im)
  set I₈ := ∫ y in c.im..z.im, Q (Complex.mk w.re y)
  have hzBall : Metric.ball z (r - dist z c) ⊆ Metric.ball c r := ball_subset_ball' (by simp)
  have hw_mem : w ∈ Metric.ball c r := mem_of_subset_of_mem hzBall hw
  have integrableHoriz (a₁ a₂ b : ℝ)
      (ha₁ : Complex.mk a₁ b ∈ Metric.ball c r) (ha₂ : Complex.mk a₂ b ∈ Metric.ball c r) :
      IntervalIntegrable (fun x ↦ P (Complex.mk x b)) volume a₁ a₂ := by
    refine ((hP_cont.mono (image_horizontalSegment_subset_ball ha₁ ha₂)).comp
      (continuousOn_complex_mk_right (b := b) (s := Set.uIcc a₁ a₂))
      (mapsTo_image _ _)).intervalIntegrable
  have integrableVert (a b₁ b₂ : ℝ)
      (hb₁ : Complex.mk a b₁ ∈ Metric.ball c r) (hb₂ : Complex.mk a b₂ ∈ Metric.ball c r) :
      IntervalIntegrable (fun y ↦ Q (Complex.mk a y)) volume b₁ b₂ := by
    refine ((hQ_cont.mono (image_verticalSegment_subset_ball hb₁ hb₂)).comp
      (continuousOn_complex_mk_left (a := a) (s := Set.uIcc b₁ b₂))
      (mapsTo_image _ _)).intervalIntegrable
  have hcCorner : Complex.mk c.re c.im ∈ Metric.ball c r := by
    simpa using (Metric.mem_ball_self (pos_of_mem_ball hz) : c ∈ Metric.ball c r)
  have hzCorner : Complex.mk z.re c.im ∈ Metric.ball c r := by
    have hEq : (z.re + c.im * Complex.I : ℂ) = Complex.mk z.re c.im := by
      apply Complex.ext <;> simp
    exact hEq ▸ reAddImMul_mem_ball (c := c) (z := z) hz
  have hwCorner : Complex.mk w.re c.im ∈ Metric.ball c r := by
    have hEq : (w.re + c.im * Complex.I : ℂ) = Complex.mk w.re c.im := by
      apply Complex.ext <;> simp
    exact hEq ▸ reAddImMul_mem_ball (c := c) (z := w) hw_mem
  have hwzCorner : Complex.mk w.re z.im ∈ Metric.ball c r := by
    have hwzSmall : w.re + z.im * Complex.I ∈ Metric.ball z (r - dist z c) :=
      reAddImMul_mem_ball (c := z) (z := w) hw
    have hEq : (w.re + z.im * Complex.I : ℂ) = Complex.mk w.re z.im := by
      apply Complex.ext <;> simp
    exact mem_of_subset_of_mem hzBall (hEq ▸ hwzSmall)
  have hI₁ : I₁ = I₃ + I₇ := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact integrableHoriz _ _ _ hcCorner hzCorner
    · exact integrableHoriz _ _ _ hzCorner hwCorner
  have hI₂ : I₂ = I₈ + I₆ := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact integrableVert _ _ _ hwCorner hwzCorner
    · exact integrableVert _ _ _ hwzCorner (by simpa using hw_mem)
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    have hrect :
        Complex.Rectangle (Complex.mk z.re c.im) (Complex.mk w.re z.im) ⊆ Metric.ball c r := by
      have hwCorner' :
          (Complex.mk w.re z.im).re + (Complex.mk z.re c.im).im * Complex.I ∈ Metric.ball c r := by
        have hEq :
            (((Complex.mk w.re z.im).re + (Complex.mk z.re c.im).im * Complex.I : ℂ)) =
              Complex.mk w.re c.im := by
          apply Complex.ext <;> simp
        exact hEq.symm ▸ hwCorner
      exact Complex.Convex.rectangle_subset (convex_ball c r) hzCorner hwzCorner
        (by simpa using hz) hwCorner'
    have hP_rect : ContinuousOn P (Complex.Rectangle (Complex.mk z.re c.im) (Complex.mk w.re z.im)) :=
      hP_cont.mono hrect
    have hQ_rect : ContinuousOn Q (Complex.Rectangle (Complex.mk z.re c.im) (Complex.mk w.re z.im)) :=
      hQ_cont.mono hrect
    have hrect_zero :
        ∫ᶜ ζ in axisParallelRectangleBoundaryPath (Complex.mk z.re c.im) (Complex.mk w.re z.im),
          Complex.planarDifferentialForm P Q ζ = 0 :=
      hrectangle (Complex.mk z.re c.im) (Complex.mk w.re z.im) hrect
    rw [rectangleBoundaryIntegral_eq_ballPrimitiveSum (z := Complex.mk z.re c.im)
      (w := Complex.mk w.re z.im) hP_rect hQ_rect] at hrect_zero
    have hrect_zero' :
        I₇ + I₈ + (∫ x in w.re..z.re, P (Complex.mk x z.im)) +
          ∫ y in z.im..c.im, Q (Complex.mk z.re y) = 0 := by
      simpa [ballPrimitive, I₇, I₈, add_assoc, add_left_comm, add_comm] using hrect_zero
    have hrect_zero'' : I₇ + I₈ - I₅ - I₄ = 0 := by
      have hrevx : (∫ x in w.re..z.re, P (Complex.mk x z.im)) = -I₅ := by
        dsimp [I₅]
        rw [intervalIntegral.integral_symm]
      have hrevy : (∫ y in z.im..c.im, Q (Complex.mk z.re y)) = -I₄ := by
        dsimp [I₄]
        rw [intervalIntegral.integral_symm]
      calc
        I₇ + I₈ - I₅ - I₄ =
            I₇ + I₈ + (∫ x in w.re..z.re, P (Complex.mk x z.im)) +
              ∫ y in z.im..c.im, Q (Complex.mk z.re y) := by
          rw [hrevx, hrevy]
          abel
        _ = 0 := hrect_zero'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrect_zero''
  have hsplit :
      ballPrimitive c P Q w - ballPrimitive c P Q z - ballPrimitive z P Q w =
        I₇ - I₅ + I₈ - I₄ := by
    calc
      ballPrimitive c P Q w - ballPrimitive c P Q z - ballPrimitive z P Q w =
          (I₁ + I₂) - (I₃ + I₄) - (I₅ + I₆) := by
        simp [ballPrimitive, I₁, I₂, I₃, I₄, I₅, I₆]
      _ = (I₃ + I₇ + (I₈ + I₆)) - (I₃ + I₄) - (I₅ + I₆) := by rw [hI₁, hI₂]
      _ = I₇ - I₅ + I₈ - I₄ := by abel
  have hzero :
      ballPrimitive c P Q w - ballPrimitive c P Q z - ballPrimitive z P Q w = 0 := by
    rw [hsplit, hI₀]
  exact sub_eq_zero.mp hzero

/-- Helper for Cartan section05 0008_Proposition_3_1: the horizontal part of the local wedge
primitive has the expected linear approximation at `z`. -/
lemma ballPrimitive_re_isLittleO
    {c z : ℂ} {r : ℝ} {P : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Metric.ball c r)) (hz : z ∈ Metric.ball c r) :
    (fun w ↦ (∫ x in z.re..w.re, P (Complex.mk x z.im)) - (w - z).re • P z)
      =o[𝓝 z] fun w ↦ w - z := by
  suffices
      (fun x ↦ (∫ t in z.re..x, P (Complex.mk t z.im)) - (x - z.re) • P z)
        =o[𝓝 z.re] fun x ↦ x - z.re by
    exact this.comp_tendsto (continuous_re.tendsto z) |>.trans_isBigO isBigO_re_sub_re
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simpa [r₁] using hz
  let s : Set ℝ := Set.Ioo (z.re - r₁) (z.re + r₁)
  have hzRe_mem : z.re ∈ s := by simp [s, r₁_pos]
  have hcont_slice : ContinuousOn (fun x : ℝ ↦ P (Complex.mk x z.im)) s := by
    refine hP_cont.comp (continuousOn_complex_mk_right (b := z.im) (s := s)) ?_
    intro x hx
    exact mem_ball_horizontalSlice (c := c) (z := z) (r := r) hx
  have hInt :
      IntervalIntegrable (fun x : ℝ ↦ P (Complex.mk x z.im)) volume z.re z.re :=
    (hcont_slice.mono <| by simpa [s]).intervalIntegrable
  have hMeas :
      StronglyMeasurableAtFilter (fun x : ℝ ↦ P (Complex.mk x z.im)) (𝓝 z.re) :=
    hcont_slice.stronglyMeasurableAtFilter isOpen_Ioo _ hzRe_mem
  have hCont : ContinuousAt (fun x : ℝ ↦ P (Complex.mk x z.im)) z.re :=
    isOpen_Ioo.continuousOn_iff.mp hcont_slice hzRe_mem
  simpa using intervalIntegral.integral_hasDerivAt_right hInt hMeas hCont |>.isLittleO

/-- Helper for Cartan section05 0008_Proposition_3_1: the vertical part of the local wedge
primitive has the expected linear approximation at `z`. -/
lemma ballPrimitive_im_isLittleO
    {c z : ℂ} {r : ℝ} {Q : ℂ → ℂ}
    (hQ_cont : ContinuousOn Q (Metric.ball c r)) (hz : z ∈ Metric.ball c r) :
    (fun w ↦ (∫ y in z.im..w.im, Q (Complex.mk w.re y)) - (w - z).im • Q z)
      =o[𝓝 z] fun w ↦ w - z := by
  suffices
      (fun w ↦ ∫ y in z.im..w.im, Q (Complex.mk w.re y) - Q z)
        =o[𝓝 z] fun w ↦ w - z by
    calc
      (fun w ↦ (∫ y in z.im..w.im, Q (Complex.mk w.re y)) - (w - z).im • Q z)
          = (fun w ↦ (∫ y in z.im..w.im, Q (Complex.mk w.re y)) - (∫ _ in z.im..w.im, Q z)) := by
            ext w
            simp
      _ =ᶠ[𝓝 z] fun w ↦ ∫ y in z.im..w.im, Q (Complex.mk w.re y) - Q z := by
        refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w hw ↦ ?_⟩
        have hslice : ContinuousOn (fun y ↦ Q (Complex.mk w.re y)) (Set.uIcc z.im w.im) := by
          refine hQ_cont.comp (continuousOn_complex_mk_left (a := w.re) (s := Set.uIcc z.im w.im)) ?_
          intro y hy
          exact image_verticalSlice_subset_ball_of_mem (c := c) (z := z) (w := w) hw ⟨y, hy, rfl⟩
        simpa using
          (intervalIntegral.integral_sub hslice.intervalIntegrable
            (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ Q z) volume z.im w.im)).symm
      _ =o[𝓝 z] fun w ↦ w - z := this
  have hsmall : (fun w ↦ Q w - Q z) =o[𝓝 z] fun _ ↦ (1 : ℝ) := by
    rw [Asymptotics.isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
    exact hQ_cont.continuousAt <| _root_.mem_nhds_iff.mpr
      ⟨Metric.ball c r, subset_rfl, Metric.isOpen_ball, hz⟩
  rw [Asymptotics.IsLittleO] at hsmall ⊢
  intro ε hε
  replace hsmall := hsmall hε
  simp only [Asymptotics.isBigOWith_iff, norm_one, mul_one] at hsmall ⊢
  replace hsmall :
      ∀ᶠ w in 𝓝 z, ∀ y ∈ Ι z.im w.im, ‖Q (Complex.mk w.re y) - Q z‖ ≤ ε := by
    rw [Metric.nhds_basis_closedBall.eventually_iff] at hsmall ⊢
    obtain ⟨i, hi_pos, hi⟩ := hsmall
    refine ⟨i, hi_pos, ?_⟩
    intro w hw y hy
    exact hi (mem_closedBall_verticalSlice (c := z) (z := w) hw hy)
  filter_upwards [hsmall] with w hw
  calc
    ‖∫ y in z.im..w.im, Q (Complex.mk w.re y) - Q z‖ ≤ ε * ‖w.im - z.im‖ :=
      intervalIntegral.norm_integral_le_of_norm_le_const hw
    _ = ε * ‖(w - z).im‖ := by simp
    _ ≤ ε * ‖w - z‖ := (mul_le_mul_iff_of_pos_left hε).mpr (abs_im_le_norm _)

/-- Helper for Cartan section05 0008_Proposition_3_1: the local wedge primitive based at `z`
linearizes to the planar differential form at `z`. -/
lemma ballPrimitive_isLittleO_linearization
    {c z : ℂ} {r : ℝ} {P Q : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Metric.ball c r))
    (hQ_cont : ContinuousOn Q (Metric.ball c r))
    (hz : z ∈ Metric.ball c r) :
    (fun w ↦ ballPrimitive z P Q w - Complex.planarDifferentialForm P Q z (w - z))
      =o[𝓝 z] fun w ↦ w - z := by
  have hre := ballPrimitive_re_isLittleO (c := c) (z := z) (r := r) hP_cont hz
  have him := ballPrimitive_im_isLittleO (c := c) (z := z) (r := r) hQ_cont hz
  have hsplit :
      (fun w ↦ ballPrimitive z P Q w - Complex.planarDifferentialForm P Q z (w - z)) =
        (fun w ↦ (∫ x in z.re..w.re, P (Complex.mk x z.im)) - (w - z).re • P z) +
          fun w ↦ (∫ y in z.im..w.im, Q (Complex.mk w.re y)) - (w - z).im • Q z := by
    funext w
    simp [ballPrimitive, Complex.planarDifferentialForm_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
  rw [hsplit]
  exact hre.add him

/-- Helper for Cartan section05 0008_Proposition_3_1: zero boundary integrals on small rectangles
force the explicit primitive `ballPrimitive c P Q` to have derivative `P dx + Q dy`. -/
lemma hasFDerivAt_ballPrimitive_of_zeroRectangleBoundary
    {c z : ℂ} {r : ℝ} {P Q : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Metric.ball c r))
    (hQ_cont : ContinuousOn Q (Metric.ball c r))
    (hz : z ∈ Metric.ball c r)
    (hrectangle :
      ∀ w₀ w₁ : ℂ,
        Complex.Rectangle w₀ w₁ ⊆ Metric.ball c r →
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁, Complex.planarDifferentialForm P Q ζ = 0) :
    HasFDerivAt (ballPrimitive c P Q) (Complex.planarDifferentialForm P Q z) z := by
  rw [hasFDerivAt_iff_isLittleO]
  calc
    (fun w ↦ ballPrimitive c P Q w - ballPrimitive c P Q z -
        Complex.planarDifferentialForm P Q z (w - z))
        =ᶠ[𝓝 z] fun w ↦ ballPrimitive z P Q w - Complex.planarDifferentialForm P Q z (w - z) := by
          refine (eventually_ballPrimitive_sub_eq_localWedge (c := c) (z := z) (r := r)
            hP_cont hQ_cont hz hrectangle).mono ?_
          intro w hw
          simp [hw]
    _ =o[𝓝 z] fun w ↦ w - z :=
      ballPrimitive_isLittleO_linearization (c := c) (z := z) (r := r) hP_cont hQ_cont hz
