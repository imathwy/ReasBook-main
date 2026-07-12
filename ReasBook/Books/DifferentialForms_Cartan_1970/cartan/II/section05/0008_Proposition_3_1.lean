import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0004_Definition_II_1_extra_4»
import DifferentialForms_Cartan_1970.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.II.section05.«0014_Remark_II_1_extra_8»
import DifferentialForms_Cartan_1970.II.section05.«0008_Proposition_3_1».Index

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped unitInterval
open scoped Interval

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Proposition 3.1: a primitive of `P dx + Q dy` recovers the expected coordinate
derivatives along horizontal and vertical lines in `ℂ`. -/
lemma primitive_planar_coord_derivatives
    {D : Set ℂ} {P Q F : ℂ → ℂ}
    (hF : IsPrimitiveOn D (P dx + Q dy) F) :
    ∀ z ∈ D,
      HasDerivAt (fun x : ℝ ↦ F (Complex.mk x z.im)) (P z) z.re ∧
        HasDerivAt (fun y : ℝ ↦ F (Complex.mk z.re y)) (Q z) z.im := by
  intro z hz
  constructor
  · -- Compose the Fréchet derivative of the primitive with the horizontal coordinate line.
    have hline : HasFDerivAt (fun x : ℝ ↦ Complex.mk x z.im) Complex.ofRealCLM z.re := by
      simpa [Complex.mk_eq_add_mul_I, add_comm, add_left_comm, add_assoc] using
        Complex.ofRealCLM.hasFDerivAt.add_const ((z.im : ℂ) * Complex.I)
    have hcomp := (hF z hz).comp z.re hline
    change HasFDerivAt (fun x : ℝ ↦ F (Complex.mk x z.im))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (P z)) z.re
    have hmap :
        ((P dx + Q dy) z).comp Complex.ofRealCLM =
          ((1 : ℝ →L[ℝ] ℝ).smulRight (P z)) := by
      ext
      simp
    simpa [hmap] using hcomp
  · -- Compose the same derivative with the vertical coordinate line.
    have hline :
        HasFDerivAt (fun y : ℝ ↦ Complex.mk z.re y) (Complex.I • Complex.ofRealCLM) z.im := by
      simpa [Complex.mk_eq_add_mul_I, add_comm, add_left_comm, add_assoc, smul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        (Complex.ofRealCLM.hasFDerivAt.mul_const Complex.I).add_const (z.re : ℂ)
    have hcomp := (hF z hz).comp z.im hline
    change HasFDerivAt (fun y : ℝ ↦ F (Complex.mk z.re y))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Q z)) z.im
    have hmap :
        ((P dx + Q dy) z).comp (Complex.I • Complex.ofRealCLM) =
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Q z)) := by
      ext
      simp [smul_eq_mul]
    simpa [hmap] using hcomp

/-- Helper for Proposition 3.1: after fixing two nearby heights, the vertical difference quotient
of a primitive has horizontal derivative given by the corresponding difference quotient of `P`. -/
lemma primitive_vertical_difference_quotient_hasDerivAt
    {D : Set ℂ} {P Q F : ℂ → ℂ}
    (hF : IsPrimitiveOn D (P dx + Q dy) F)
    {x y k : ℝ}
    (hy : Complex.mk x y ∈ D) (hyk : Complex.mk x (y + k) ∈ D) :
    HasDerivAt
      (fun s : ℝ ↦ (F (Complex.mk s (y + k)) - F (Complex.mk s y)) / k)
      ((P (Complex.mk x (y + k)) - P (Complex.mk x y)) / k) x := by
  rcases primitive_planar_coord_derivatives hF (Complex.mk x y) hy with ⟨hyx, -⟩
  rcases primitive_planar_coord_derivatives hF (Complex.mk x (y + k)) hyk with ⟨hykx, -⟩
  -- Differentiate the numerator termwise, then divide by the fixed nonzero scalar `k`.
  simpa [div_eq_inv_mul, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using
    (HasDerivAt.const_mul ((k : ℂ)⁻¹) (hykx.sub hyx))

/-- Helper for Proposition 3.1: a sufficiently small coordinate box around `z` stays inside the
ambient metric ball. -/
lemma complex_mk_mem_ball_of_coordinate_bounds
    {z : ℂ} {r δ x y : ℝ}
    (hδr : 2 * δ < r)
    (hx : x ∈ Set.Icc (z.re - δ) (z.re + δ))
    (hy : y ∈ Set.Icc (z.im - δ) (z.im + δ)) :
    Complex.mk x y ∈ Metric.ball z r := by
  -- Convert the coordinate bounds into absolute-value bounds on the horizontal and vertical
  -- displacements from `z`.
  have hx' : |x - z.re| ≤ δ := by
    rw [abs_le]
    constructor <;> nlinarith [hx.1, hx.2]
  have hy' : |y - z.im| ≤ δ := by
    rw [abs_le]
    constructor <;> nlinarith [hy.1, hy.2]
  -- Estimate the complex distance by the sum of the horizontal and vertical displacements.
  rw [Metric.mem_ball, Complex.dist_eq]
  have hdecomp :
      Complex.mk x y - z =
        ((x - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc]
  calc
    ‖Complex.mk x y - z‖
        = ‖((x - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I‖ := by
          rw [hdecomp]
    _ ≤ ‖((x - z.re : ℝ) : ℂ)‖ + ‖((y - z.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |x - z.re| + |y - z.im| := by
          have hnormx : ‖((x - z.re : ℝ) : ℂ)‖ = |x - z.re| := by
            simpa using (RCLike.norm_ofReal (K := ℂ) (x - z.re))
          have hnormy : ‖((y - z.im : ℝ) : ℂ) * Complex.I‖ = |y - z.im| := by
            have hnormy' : ‖((y - z.im : ℝ) : ℂ)‖ = |y - z.im| := by
              simpa using (RCLike.norm_ofReal (K := ℂ) (y - z.im))
            calc
              ‖((y - z.im : ℝ) : ℂ) * Complex.I‖
                  = ‖((y - z.im : ℝ) : ℂ)‖ * ‖Complex.I‖ := norm_mul _ _
              _ = |y - z.im| * 1 := by rw [hnormy', Complex.norm_I]
              _ = |y - z.im| := by ring
          rw [hnormx, hnormy]
    _ ≤ δ + δ := add_le_add hx' hy'
    _ = 2 * δ := by ring
    _ < r := hδr

/-- Helper for Proposition 3.1: the vertical difference quotient of `P` is the average of the
continuous partial derivative `dPdy` along the corresponding vertical segment. -/
lemma partial_difference_quotient_eq_average_partial
    {D : Set ℂ} {P dPdy : ℂ → ℂ} {z : ℂ} {δ s k : ℝ}
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ x ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk x y ∈ D)
    (hs : s ∈ Set.Icc (z.re - δ) (z.re + δ))
    (hk : |k| ≤ δ) (hk0 : k ≠ 0) :
    (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k =
      (1 / k) * ∫ t in z.im..z.im + k, dPdy (Complex.mk s t) := by
  -- First show that the whole vertical segment lies in `D`, so the slice derivative data applies.
  have hδ_nonneg : 0 ≤ δ := le_trans (abs_nonneg k) hk
  have hz_mem : z.im ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> linarith
  have hzk_mem : z.im + k ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> nlinarith [abs_le.mp hk |>.1, abs_le.mp hk |>.2]
  have hslice_mem :
      ∀ t ∈ Set.uIcc z.im (z.im + k), Complex.mk s t ∈ D := by
    intro t ht
    have ht_mem : t ∈ Set.Icc (z.im - δ) (z.im + δ) := by
      by_cases hk_nonneg : 0 ≤ k
      · have ht' : t ∈ Set.Icc z.im (z.im + k) := by
          have hk_order : z.im ≤ z.im + k := by linarith
          rw [Set.uIcc_of_le hk_order] at ht
          exact ht
        constructor <;> nlinarith [ht'.1, ht'.2, abs_le.mp hk |>.1, abs_le.mp hk |>.2]
      · have hk_nonpos : z.im + k ≤ z.im := by linarith
        have ht' : t ∈ Set.Icc (z.im + k) z.im := by
          rw [Set.uIcc_of_ge hk_nonpos] at ht
          exact ht
        constructor <;> nlinarith [ht'.1, ht'.2, abs_le.mp hk |>.1, abs_le.mp hk |>.2]
    exact hbox s hs t ht_mem
  -- The derivative along the vertical slice is exactly the prescribed partial derivative.
  have hderiv :
      ∀ t ∈ Set.uIcc z.im (z.im + k),
        HasDerivAt (fun y : ℝ ↦ P (Complex.mk s y)) (dPdy (Complex.mk s t)) t := by
    intro t ht
    exact hP_dy (Complex.mk s t) (hslice_mem t ht)
  -- Continuity of the slice derivative gives the interval-integrability needed for FTC.
  have hmk_cont : Continuous (fun t : ℝ ↦ Complex.mk s t) := by
    have hcont : Continuous (fun t : ℝ ↦ (s : ℂ) + (t : ℂ) * Complex.I) := by
      exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    refine hcont.congr ?_
    intro t
    apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I]
  have hslice_cont : ContinuousOn (fun t : ℝ ↦ dPdy (Complex.mk s t)) (Set.uIcc z.im (z.im + k)) := by
    refine hdPdy_cont.comp hmk_cont.continuousOn ?_
    intro t ht
    exact hslice_mem t ht
  have hslice_int :
      IntervalIntegrable (fun t : ℝ ↦ dPdy (Complex.mk s t)) MeasureTheory.volume z.im (z.im + k) :=
    hslice_cont.intervalIntegrable
  have hFTC :
      ∫ t in z.im..z.im + k, dPdy (Complex.mk s t) =
        P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im) := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hslice_int
  -- Rewrite the difference quotient using the interval formula and pull out the scalar factor.
  calc
    (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k
        = (1 / k) * (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) := by
          simp [div_eq_inv_mul]
    _ = (1 / k) * ∫ t in z.im..z.im + k, dPdy (Complex.mk s t) := by
          rw [hFTC]

/-- Helper for Proposition 3.1: subtracting a constant from a complex-valued interval average can
be rewritten as averaging the pointwise error term, provided the interval length is nonzero. -/
lemma average_interval_sub_const_eq
    {g : ℝ → ℂ} {a k : ℝ} {c : ℂ}
    (hg : IntervalIntegrable g MeasureTheory.volume a (a + k))
    (hk0 : k ≠ 0) :
    ((1 / k : ℂ) * ∫ t in a..a + k, g t) - c =
      ((1 / k : ℂ) * ∫ t in a..a + k, (g t - c)) := by
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ c) MeasureTheory.volume a (a + k) :=
    intervalIntegrable_const
  have hk0C : (k : ℂ) ≠ 0 := by
    exact_mod_cast hk0
  have hc :
      ((1 / k : ℂ) * ∫ t in a..a + k, c) = c := by
    -- The interval integral of a constant is the interval length times that constant.
    rw [intervalIntegral.integral_const]
    have hlen : a + k - a = k := by
      ring
    rw [hlen]
    calc
      ((1 / k : ℂ) * (k • c))
          = ((1 / k : ℂ) * ((k : ℂ) * c)) := by
              simp [Algebra.smul_def]
      _ = (((1 / k : ℂ) * (k : ℂ)) * c) := by ring
      _ = c := by simp [hk0C]
  -- Normalize the average-minus-constant expression before later norm estimates.
  calc
    ((1 / k : ℂ) * ∫ t in a..a + k, g t) - c
        = ((1 / k : ℂ) * ∫ t in a..a + k, g t) -
            ((1 / k : ℂ) * ∫ t in a..a + k, c) := by rw [hc]
    _ = (1 / k : ℂ) * ((∫ t in a..a + k, g t) - ∫ t in a..a + k, c) := by ring
    _ = ((1 / k : ℂ) * ∫ t in a..a + k, (g t - c)) := by
          rw [← intervalIntegral.integral_sub hg hconst]

/-- Helper for Proposition 3.1: after rewriting the vertical difference quotient of `P` as an
average of `dPdy`, subtracting the base value of `dPdy` turns it into the average error term along
the same vertical segment. -/
lemma partial_difference_quotient_sub_partial_eq_average_error
    {D : Set ℂ} {P dPdy : ℂ → ℂ} {z : ℂ} {δ s k : ℝ}
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ x ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk x y ∈ D)
    (hs : s ∈ Set.Icc (z.re - δ) (z.re + δ))
    (hk : |k| ≤ δ) (hk0 : k ≠ 0) :
    ((P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k) - dPdy (Complex.mk s z.im) =
      ((1 / k : ℂ) * ∫ t in z.im..z.im + k,
        (dPdy (Complex.mk s t) - dPdy (Complex.mk s z.im))) := by
  have hslice_mem :
      ∀ t ∈ Set.uIcc z.im (z.im + k), Complex.mk s t ∈ D := by
    intro t ht
    have ht_mem : t ∈ Set.Icc (z.im - δ) (z.im + δ) := by
      rcases Set.mem_uIcc.mp ht with ht' | ht'
      · constructor <;> nlinarith [ht'.1, ht'.2, abs_nonneg k, abs_le.mp hk |>.1, abs_le.mp hk |>.2]
      · constructor <;> nlinarith [ht'.1, ht'.2, abs_nonneg k, abs_le.mp hk |>.1, abs_le.mp hk |>.2]
    exact hbox s hs t ht_mem
  have hmk_cont : Continuous (fun t : ℝ ↦ Complex.mk s t) := by
    have hcont : Continuous (fun t : ℝ ↦ (s : ℂ) + (t : ℂ) * Complex.I) := by
      exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    refine hcont.congr ?_
    intro t
    apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I]
  have hslice_cont : ContinuousOn (fun t : ℝ ↦ dPdy (Complex.mk s t)) (Set.uIcc z.im (z.im + k)) := by
    refine hdPdy_cont.comp hmk_cont.continuousOn ?_
    intro t ht
    exact hslice_mem t ht
  have hslice_int :
      IntervalIntegrable (fun t : ℝ ↦ dPdy (Complex.mk s t)) MeasureTheory.volume z.im (z.im + k) :=
    hslice_cont.intervalIntegrable
  -- First rewrite the quotient as the averaged partial derivative, then subtract the base value
  -- inside the same interval average.
  calc
    ((P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k) - dPdy (Complex.mk s z.im)
        = ((1 / k : ℂ) * ∫ t in z.im..z.im + k, dPdy (Complex.mk s t)) -
            dPdy (Complex.mk s z.im) := by
              rw [partial_difference_quotient_eq_average_partial hdPdy_cont hP_dy hbox hs hk hk0]
    _ = ((1 / k : ℂ) * ∫ t in z.im..z.im + k,
          (dPdy (Complex.mk s t) - dPdy (Complex.mk s z.im))) := by
          simpa using
            average_interval_sub_const_eq
              (g := fun t : ℝ ↦ dPdy (Complex.mk s t))
              (a := z.im) (k := k) (c := dPdy (Complex.mk s z.im)) hslice_int hk0

/-- Helper for Proposition 3.1: every point of the short vertical segment from `z.im` to
`z.im + k` stays inside the vertical side of the coordinate box whenever `|k| ≤ δ`. -/
lemma mem_vertical_box_of_mem_uIcc
    {z : ℂ} {δ k t : ℝ}
    (hk : |k| ≤ δ)
    (ht : t ∈ Set.uIcc z.im (z.im + k)) :
    t ∈ Set.Icc (z.im - δ) (z.im + δ) := by
  -- Split according to the orientation of the short vertical segment.
  rcases Set.mem_uIcc.mp ht with ht | ht
  · constructor <;> nlinarith [ht.1, ht.2, abs_nonneg k, abs_le.mp hk |>.1, abs_le.mp hk |>.2]
  · constructor <;> nlinarith [ht.1, ht.2, abs_nonneg k, abs_le.mp hk |>.1, abs_le.mp hk |>.2]

/-- Helper for Proposition 3.1: every point of the half-open unoriented interval `uIoc` also lies
in the corresponding closed unoriented interval `uIcc`. -/
lemma mem_uIcc_of_mem_uIoc {a b t : ℝ} (ht : t ∈ Set.uIoc a b) : t ∈ Set.uIcc a b := by
  rcases Set.mem_uIoc.mp ht with ht | ht
  · exact Set.mem_uIcc_of_le ht.1.le ht.2
  · exact Set.mem_uIcc_of_ge ht.1.le ht.2

/-- Helper for Proposition 3.1: on a vertical line, complex distance is the absolute difference of
the imaginary coordinates. -/
lemma complex_dist_mk_same_re_eq_abs
    {x y₁ y₂ : ℝ} :
    dist (Complex.mk x y₁) (Complex.mk x y₂) = |y₁ - y₂| := by
  -- Expand the complex difference and use that multiplication by `I` preserves the norm.
  rw [Complex.dist_eq]
  have hdecomp :
      Complex.mk x y₁ - Complex.mk x y₂ = (((y₁ - y₂ : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc]
  rw [hdecomp, norm_mul, Complex.norm_I]
  simpa using (RCLike.norm_ofReal (K := ℂ) (y₁ - y₂))

/-- Helper for Proposition 3.1: the vertical difference quotient of `P` converges uniformly on the
small horizontal interval to `dPdy` as the vertical increment tends to `0`. -/
lemma partial_difference_quotient_uniform_approx
    {D : Set ℂ} {P dPdy : ℂ → ℂ} {z : ℂ} {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ x ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk x y ∈ D) :
    ∀ ε > 0, ∃ η > 0, ∀ ⦃k : ℝ⦄, k ≠ 0 → |k| < η →
      ∀ s ∈ Set.Icc (z.re - δ) (z.re + δ),
        ‖((P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k) -
            dPdy (Complex.mk s z.im)‖ ≤ ε := by
  -- Route correction: the remaining issue is no longer the algebraic normalization. The new
  -- `average_interval_sub_const_eq` reduces the target to a pure uniform-continuity bound on the
  -- average error over the short vertical segment inside the box.
  let R : Set ℂ :=
    Set.Icc (z.re - δ) (z.re + δ) ×ℂ Set.Icc (z.im - δ) (z.im + δ)
  have hR_subset : R ⊆ D := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    exact hbox w.re hw.1 w.im hw.2
  have hR_compact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hR_uc : UniformContinuousOn dPdy R :=
    hR_compact.uniformContinuousOn_of_continuous (hdPdy_cont.mono hR_subset)
  rw [Metric.uniformContinuousOn_iff] at hR_uc
  intro ε hε
  rcases hR_uc ε hε with ⟨η, hη_pos, hη⟩
  refine ⟨min η δ, lt_min hη_pos hδ_pos, ?_⟩
  intro k hk0 hk_eta s hs
  have hk_eta' : |k| < η := lt_of_lt_of_le hk_eta (min_le_left _ _)
  have hkδ : |k| ≤ δ := le_of_lt (lt_of_lt_of_le hk_eta (min_le_right _ _))
  have hzim : z.im ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> linarith
  have hrewrite :=
    partial_difference_quotient_sub_partial_eq_average_error hdPdy_cont hP_dy hbox hs hkδ hk0
  rw [hrewrite]
  have hk0_abs : |k| ≠ 0 := abs_ne_zero.mpr hk0
  have hnorm_inv : ‖(1 / k : ℂ)‖ = |k|⁻¹ := by
    simp [Complex.norm_real, abs_inv]
  -- Uniform continuity on the compact rectangle bounds the integrand by `ε` along the whole
  -- short vertical segment, uniformly in the horizontal parameter `s`.
  have hbound :
      ∀ t ∈ Set.uIcc z.im (z.im + k),
        ‖dPdy (Complex.mk s t) - dPdy (Complex.mk s z.im)‖ ≤ ε := by
    intro t ht
    have ht_box : t ∈ Set.Icc (z.im - δ) (z.im + δ) :=
      mem_vertical_box_of_mem_uIcc hkδ ht
    have hw₁ : Complex.mk s t ∈ R := by
      rw [Complex.mem_reProdIm]
      exact ⟨hs, ht_box⟩
    have hw₀ : Complex.mk s z.im ∈ R := by
      rw [Complex.mem_reProdIm]
      exact ⟨hs, hzim⟩
    have hdist_le : dist (Complex.mk s t) (Complex.mk s z.im) ≤ |k| := by
      rw [complex_dist_mk_same_re_eq_abs]
      rcases Set.mem_uIcc.mp ht with ht' | ht'
      · by_cases hk_nonneg : 0 ≤ k
        · have hk_order : z.im ≤ z.im + k := by linarith
          have ht'' : t ∈ Set.Icc z.im (z.im + k) := by
            simpa [Set.uIcc_of_le hk_order] using ht
          have ht_nonneg : 0 ≤ t - z.im := by linarith
          have ht_le : t - z.im ≤ k := by linarith
          rw [abs_of_nonneg ht_nonneg, abs_of_nonneg hk_nonneg]
          linarith
        · have hk_nonpos : z.im + k ≤ z.im := by linarith
          have ht'' : t ∈ Set.Icc (z.im + k) z.im := by
            simpa [Set.uIcc_of_ge hk_nonpos] using ht
          have ht_nonneg : 0 ≤ z.im - t := by linarith
          have ht_le : z.im - t ≤ -k := by linarith
          have htk_nonpos : t - z.im ≤ 0 := by linarith
          rw [abs_of_nonpos htk_nonpos, abs_of_neg (show k < 0 by linarith)]
          linarith
      · by_cases hk_nonneg : 0 ≤ k
        · have hk_order : z.im ≤ z.im + k := by linarith
          have ht'' : t ∈ Set.Icc z.im (z.im + k) := by
            simpa [Set.uIcc_of_le hk_order] using ht
          have ht_nonneg : 0 ≤ t - z.im := by linarith
          have ht_le : t - z.im ≤ k := by linarith
          rw [abs_of_nonneg ht_nonneg, abs_of_nonneg hk_nonneg]
          linarith
        · have hk_nonpos : z.im + k ≤ z.im := by linarith
          have ht'' : t ∈ Set.Icc (z.im + k) z.im := by
            simpa [Set.uIcc_of_ge hk_nonpos] using ht
          have ht_nonneg : 0 ≤ z.im - t := by linarith
          have ht_le : z.im - t ≤ -k := by linarith
          have htk_nonpos : t - z.im ≤ 0 := by linarith
          rw [abs_of_nonpos htk_nonpos, abs_of_neg (show k < 0 by linarith)]
          linarith
    have hdist_lt : dist (Complex.mk s t) (Complex.mk s z.im) < η :=
      lt_of_le_of_lt hdist_le hk_eta'
    have hdist_image :
        dist (dPdy (Complex.mk s t)) (dPdy (Complex.mk s z.im)) < ε :=
      hη _ hw₁ _ hw₀ hdist_lt
    simpa [dist_eq_norm] using le_of_lt hdist_image
  have hbound_interval :
      ∀ t ∈ Set.uIoc z.im (z.im + k),
        ‖dPdy (Complex.mk s t) - dPdy (Complex.mk s z.im)‖ ≤ ε := by
    intro t ht
    have ht' : t ∈ Set.uIcc z.im (z.im + k) := by
      rcases Set.mem_uIoc.mp ht with h | h
      · exact Set.mem_uIcc_of_le h.1.le h.2
      · exact Set.mem_uIcc_of_ge h.1.le h.2
    exact hbound t ht'
  have hnorm_int :
      ‖∫ t in z.im..z.im + k, (dPdy (Complex.mk s t) - dPdy (Complex.mk s z.im))‖ ≤
        ε * |k| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound_interval
  calc
    ‖(1 / k : ℂ) * ∫ t in z.im..z.im + k,
        (dPdy (Complex.mk s t) - dPdy (Complex.mk s z.im))‖
        = ‖(1 / k : ℂ)‖ *
            ‖∫ t in z.im..z.im + k,
              (dPdy (Complex.mk s t) - dPdy (Complex.mk s z.im))‖ := by
              rw [norm_mul]
    _ ≤ ‖(1 / k : ℂ)‖ * (ε * |k|) := by
          gcongr
    _ = |k|⁻¹ * (ε * |k|) := by rw [hnorm_inv]
    _ = ε := by
          field_simp [hk0_abs]

/-- Helper for Proposition 3.1: for a fixed short vertical increment `k`, the averaged partial
derivative stays continuous in the horizontal parameter along the local box. -/
lemma average_partial_continuous_in_horizontal_parameter
    {D : Set ℂ} {dPdy : ℂ → ℂ} {z : ℂ} {δ x k : ℝ}
    (hdPdy_cont : ContinuousOn dPdy D)
    (hbox :
      ∀ s ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk s y ∈ D)
    (hx : x ∈ Set.Icc (z.re - δ) (z.re + δ))
    (hk : |k| ≤ δ) :
    ContinuousOn
      (fun s : ℝ ↦ ((1 / k : ℂ) * ∫ t in z.im..z.im + k, dPdy (Complex.mk s t)))
      (Set.uIcc z.re x) := by
  have hδ_nonneg : 0 ≤ δ := le_trans (abs_nonneg k) hk
  have hzre_mem : z.re ∈ Set.Icc (z.re - δ) (z.re + δ) := by
    constructor <;> linarith
  have hzre_u : z.re ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hzre_mem
  have hx_u : x ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hx
  have him_mem : z.im ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> linarith
  have him_u : z.im ∈ Set.uIcc (z.im - δ) (z.im + δ) := Set.Icc_subset_uIcc him_mem
  have himk_mem : z.im + k ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> nlinarith [abs_le.mp hk |>.1, abs_le.mp hk |>.2]
  have himk_u : z.im + k ∈ Set.uIcc (z.im - δ) (z.im + δ) := Set.Icc_subset_uIcc himk_mem
  have hI_subset : Set.uIcc z.re x ⊆ Set.Icc (z.re - δ) (z.re + δ) := by
    intro s hs
    have hs' : s ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.uIcc_subset_uIcc hzre_u hx_u hs
    rcases Set.mem_uIcc.mp hs' with hs'' | hs''
    · constructor <;> nlinarith [hs''.1, hs''.2]
    · constructor <;> nlinarith [hs''.1, hs''.2]
  have hJ_subset : Set.uIcc z.im (z.im + k) ⊆ Set.Icc (z.im - δ) (z.im + δ) := by
    intro t ht
    have ht' : t ∈ Set.uIcc (z.im - δ) (z.im + δ) := Set.uIcc_subset_uIcc him_u himk_u ht
    rcases Set.mem_uIcc.mp ht' with ht'' | ht''
    · constructor <;> nlinarith [ht''.1, ht''.2]
    · constructor <;> nlinarith [ht''.1, ht''.2]
  let R : Set ℂ := Set.uIcc z.re x ×ℂ Set.uIcc z.im (z.im + k)
  have hR_subset : R ⊆ D := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    exact hbox w.re (hI_subset hw.1) w.im (hJ_subset hw.2)
  have hR_compact : IsCompact R := isCompact_uIcc.reProdIm isCompact_uIcc
  obtain ⟨C, hC⟩ := hR_compact.exists_bound_of_continuousOn (hdPdy_cont.mono hR_subset)
  have hslice_cont :
      ∀ s : Set.uIcc z.re x,
        ContinuousOn (fun t : ℝ ↦ dPdy (Complex.mk (s : ℝ) t)) (Set.uIcc z.im (z.im + k)) := by
    intro s
    have hmk_cont : Continuous (fun t : ℝ ↦ Complex.mk (s : ℝ) t) := by
      have hcont : Continuous (fun t : ℝ ↦ ((s : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
        exact continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
      refine hcont.congr ?_
      intro t
      apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I]
    refine hdPdy_cont.comp hmk_cont.continuousOn ?_
    intro t ht
    exact hbox (s : ℝ) (hI_subset s.property) t (hJ_subset ht)
  have havg_cont :
      Continuous
        (fun s : Set.uIcc z.re x ↦ ∫ t in z.im..z.im + k, dPdy (Complex.mk (s : ℝ) t)) := by
    -- Compactness of the coordinate rectangle gives a uniform bound, so dominated convergence
    -- upgrades pointwise continuity in `s` to continuity of the averaged slice.
    simpa using
      (intervalIntegral.continuous_of_dominated_interval
        (F := fun s : Set.uIcc z.re x ↦ fun t : ℝ => dPdy (Complex.mk (s : ℝ) t))
        (bound := fun _ : ℝ ↦ C)
        (a := z.im) (b := z.im + k)
        (hF_meas := fun s ↦
          (hslice_cont s).aestronglyMeasurable_of_subset_isCompact
            isCompact_uIcc measurableSet_uIoc (by
              intro t ht
              exact mem_uIcc_of_mem_uIoc ht))
        (h_bound := fun s ↦ Filter.Eventually.of_forall fun t ht ↦
          hC (Complex.mk (s : ℝ) t) (by
            rw [Complex.mem_reProdIm]
            exact ⟨s.property, mem_uIcc_of_mem_uIoc ht⟩))
        (bound_integrable := by
          simpa using
            (intervalIntegrable_const :
              IntervalIntegrable (fun _ : ℝ ↦ C) MeasureTheory.volume z.im (z.im + k)))
        (h_cont := Filter.Eventually.of_forall fun t ht ↦ by
          have hline_cont : ContinuousOn (fun s : ℝ ↦ dPdy (Complex.mk s t)) (Set.uIcc z.re x) := by
            have hmk_cont : Continuous (fun s : ℝ ↦ Complex.mk s t) := by
              have hcont : Continuous (fun s : ℝ ↦ (s : ℂ) + (t : ℂ) * Complex.I) := by
                exact (Complex.continuous_ofReal.comp continuous_id).add continuous_const
              refine hcont.congr ?_
              intro s
              apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I]
            refine hdPdy_cont.comp hmk_cont.continuousOn ?_
            intro s hs
            exact hbox s (hI_subset hs) t (hJ_subset (mem_uIcc_of_mem_uIoc ht))
          simpa using (continuousOn_iff_continuous_restrict.mp hline_cont)))
  have hsmul_cont :
      Continuous
        (fun s : Set.uIcc z.re x ↦
          ((1 / k : ℂ) * ∫ t in z.im..z.im + k, dPdy (Complex.mk (s : ℝ) t))) :=
    continuous_const.mul havg_cont
  -- Convert the continuous subtype statement back to the original `ContinuousOn` formulation.
  exact continuousOn_iff_continuous_restrict.mpr (by simpa using hsmul_cont)

/-- Helper for Proposition 3.1: the horizontal primitive quotient has an integrable derivative once
the vertical `P`-difference quotient is rewritten as the averaged partial derivative. -/
lemma primitive_vertical_difference_quotient_intervalIntegrable
    {D : Set ℂ} {P dPdy : ℂ → ℂ} {z : ℂ} {δ x k : ℝ}
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ s ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk s y ∈ D)
    (hx : x ∈ Set.Icc (z.re - δ) (z.re + δ))
    (hk : |k| ≤ δ) (hk0 : k ≠ 0) :
    IntervalIntegrable
      (fun s : ℝ ↦ (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
      MeasureTheory.volume z.re x := by
  have hδ_nonneg : 0 ≤ δ := le_trans (abs_nonneg k) hk
  have hzre_mem : z.re ∈ Set.Icc (z.re - δ) (z.re + δ) := by
    constructor <;> linarith
  have hzre_u : z.re ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hzre_mem
  have hx_u : x ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hx
  have hI_subset : Set.uIcc z.re x ⊆ Set.Icc (z.re - δ) (z.re + δ) := by
    intro s hs
    have hs' : s ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.uIcc_subset_uIcc hzre_u hx_u hs
    rcases Set.mem_uIcc.mp hs' with hs'' | hs''
    · constructor <;> nlinarith [hs''.1, hs''.2]
    · constructor <;> nlinarith [hs''.1, hs''.2]
  have havg_cont :
      ContinuousOn
        (fun s : ℝ ↦ ((1 / k : ℂ) * ∫ t in z.im..z.im + k, dPdy (Complex.mk s t)))
        (Set.uIcc z.re x) :=
    average_partial_continuous_in_horizontal_parameter hdPdy_cont hbox hx hk
  have hquot_cont :
      ContinuousOn
        (fun s : ℝ ↦ (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
        (Set.uIcc z.re x) := by
    -- Rewrite pointwise on `Set.uIcc z.re x` to expose the continuous averaged formula.
    refine havg_cont.congr ?_
    intro s hs
    exact partial_difference_quotient_eq_average_partial
      hdPdy_cont hP_dy hbox (hI_subset hs) hk hk0
  exact hquot_cont.intervalIntegrable

/-- Helper for Proposition 3.1: the horizontal change of the primitive's vertical difference
quotient is the interval integral of the corresponding difference quotient of `P`. -/
lemma primitive_vertical_difference_quotient_eq_interval_integral
    {D : Set ℂ} {P Q F dPdy : ℂ → ℂ} {z : ℂ} {δ x k : ℝ}
    (hF : IsPrimitiveOn D (P dx + Q dy) F)
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ s ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk s y ∈ D)
    (hx : x ∈ Set.Icc (z.re - δ) (z.re + δ))
    (hk : |k| ≤ δ) (hk0 : k ≠ 0) :
    ((F (Complex.mk x (z.im + k)) - F (Complex.mk x z.im)) / k) -
        ((F (Complex.mk z.re (z.im + k)) - F z) / k) =
      ∫ s in z.re..x, (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k := by
  have hδ_nonneg : 0 ≤ δ := le_trans (abs_nonneg k) hk
  have hzre_mem : z.re ∈ Set.Icc (z.re - δ) (z.re + δ) := by
    constructor <;> linarith
  have hzre_u : z.re ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hzre_mem
  have hx_u : x ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hx
  have him_mem : z.im ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> linarith
  have himk_mem : z.im + k ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> nlinarith [abs_le.mp hk |>.1, abs_le.mp hk |>.2]
  have hI_subset : Set.uIcc z.re x ⊆ Set.Icc (z.re - δ) (z.re + δ) := by
    intro s hs
    have hs' : s ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.uIcc_subset_uIcc hzre_u hx_u hs
    rcases Set.mem_uIcc.mp hs' with hs'' | hs''
    · constructor <;> nlinarith [hs''.1, hs''.2]
    · constructor <;> nlinarith [hs''.1, hs''.2]
  have hderiv :
      ∀ s ∈ Set.uIcc z.re x,
        HasDerivAt
          (fun r : ℝ ↦ (F (Complex.mk r (z.im + k)) - F (Complex.mk r z.im)) / k)
          ((P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k) s := by
    intro s hs
    have hzD : Complex.mk s z.im ∈ D := hbox s (hI_subset hs) z.im him_mem
    have hkD : Complex.mk s (z.im + k) ∈ D := hbox s (hI_subset hs) (z.im + k) himk_mem
    -- Differentiate the fixed-height vertical quotient along the horizontal segment.
    simpa using primitive_vertical_difference_quotient_hasDerivAt hF hzD hkD
  have hint :
      IntervalIntegrable
        (fun s : ℝ ↦ (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
        MeasureTheory.volume z.re x :=
    primitive_vertical_difference_quotient_intervalIntegrable hdPdy_cont hP_dy hbox hx hk hk0
  have hFTC :
      ∫ s in z.re..x, (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k =
        ((F (Complex.mk x (z.im + k)) - F (Complex.mk x z.im)) / k) -
          ((F (Complex.mk z.re (z.im + k)) - F (Complex.mk z.re z.im)) / k) := by
    -- One-variable FTC now applies because the derivative is integrable on `z.re..x`.
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using hFTC.symm

/-- Helper for Proposition 3.1: the pointwise uniform approximation estimate upgrades to a genuine
punctured-neighborhood `TendstoUniformlyOn` statement on the fixed horizontal interval. -/
lemma partial_difference_quotient_tendstoUniformlyOn
    {D : Set ℂ} {P dPdy : ℂ → ℂ} {z : ℂ} {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ x ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk x y ∈ D) :
    TendstoUniformlyOn
      (fun k : ℝ ↦ fun s : ℝ ↦ (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
      (fun s : ℝ ↦ dPdy (Complex.mk s z.im))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (Set.Icc (z.re - δ) (z.re + δ)) := by
  -- Repackage the previously proved epsilon-eta estimate in mathlib's uniform-convergence form.
  refine Metric.tendstoUniformlyOn_iff.mpr ?_
  intro ε hε
  have hε_half : ε / 2 > 0 := by linarith
  rcases partial_difference_quotient_uniform_approx hδ_pos hdPdy_cont hP_dy hbox (ε / 2) hε_half with
    ⟨η, hη_pos, hη⟩
  have hη_mem : {k : ℝ | |k| < η} ∈ nhds (0 : ℝ) := by
    simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using Metric.ball_mem_nhds (0 : ℝ) hη_pos
  have hη_mem_within : {k : ℝ | |k| < η} ∈ nhdsWithin (0 : ℝ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hη_mem
  filter_upwards [self_mem_nhdsWithin, hη_mem_within] with k hk0 hkη s hs
  have hdist :
      dist (dPdy (Complex.mk s z.im))
          ((P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k) ≤ ε / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hη hk0 hkη s hs
  exact lt_of_le_of_lt hdist (by linarith)

/-- Helper for Proposition 3.1: the primitive's vertical difference quotient tends to `Q` along a
punctured real neighborhood of the vertical increment `0`. -/
lemma primitive_vertical_difference_quotient_tendsto_Q
    {D : Set ℂ} {P Q F : ℂ → ℂ}
    (hF : IsPrimitiveOn D (P dx + Q dy) F)
    {w : ℂ} (hw : w ∈ D) :
    Filter.Tendsto
      (fun k : ℝ ↦ (F (Complex.mk w.re (w.im + k)) - F w) / k)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (Q w)) := by
  rcases primitive_planar_coord_derivatives hF w hw with ⟨-, hw_vertical⟩
  -- Rewrite the vertical quotient into the slope-zero normal form of the derivative.
  simpa [div_eq_inv_mul, smul_eq_mul] using hw_vertical.tendsto_slope_zero

/-- Helper for Proposition 3.1: integrating the vertical `P`-difference quotient along the
horizontal segment commutes with the `k → 0` limit because the convergence is uniform there. -/
lemma partial_difference_quotient_interval_integral_tendsto
    {D : Set ℂ} {P dPdy : ℂ → ℂ} {z : ℂ} {δ x : ℝ}
    (hδ_pos : 0 < δ)
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ s ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk s y ∈ D)
    (hx : x ∈ Set.Icc (z.re - δ) (z.re + δ)) :
    Filter.Tendsto
      (fun k : ℝ ↦ ∫ s in z.re..x, (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (∫ s in z.re..x, dPdy (Complex.mk s z.im))) := by
  have hzre_mem : z.re ∈ Set.Icc (z.re - δ) (z.re + δ) := by
    constructor <;> linarith
  have hzre_u : z.re ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hzre_mem
  have hx_u : x ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.Icc_subset_uIcc hx
  have hI_subset : Set.uIcc z.re x ⊆ Set.Icc (z.re - δ) (z.re + δ) := by
    intro s hs
    have hs' : s ∈ Set.uIcc (z.re - δ) (z.re + δ) := Set.uIcc_subset_uIcc hzre_u hx_u hs
    rcases Set.mem_uIcc.mp hs' with hs'' | hs''
    · constructor <;> nlinarith [hs''.1, hs''.2]
    · constructor <;> nlinarith [hs''.1, hs''.2]
  have hquot_unif :
      TendstoUniformlyOn
        (fun k : ℝ ↦ fun s : ℝ ↦ (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
        (fun s : ℝ ↦ dPdy (Complex.mk s z.im))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (Set.uIcc z.re x) :=
    (partial_difference_quotient_tendstoUniformlyOn hδ_pos hdPdy_cont hP_dy hbox).mono hI_subset
  have hcont_event :
      ∀ᶠ k : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
        ContinuousOn
          (fun s : ℝ ↦ (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
          (Set.uIcc z.re x) := by
    have hball : {k : ℝ | |k| < δ} ∈ nhds (0 : ℝ) := by
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using Metric.ball_mem_nhds (0 : ℝ) hδ_pos
    have hball_within : {k : ℝ | |k| < δ} ∈ nhdsWithin (0 : ℝ) ({0}ᶜ) :=
      nhdsWithin_le_nhds hball
    filter_upwards [self_mem_nhdsWithin, hball_within] with k hk0 hkδlt
    have hkδ : |k| ≤ δ := le_of_lt hkδlt
    have havg_cont :
        ContinuousOn
          (fun s : ℝ ↦ ((1 / k : ℂ) * ∫ t in z.im..z.im + k, dPdy (Complex.mk s t)))
          (Set.uIcc z.re x) :=
      average_partial_continuous_in_horizontal_parameter hdPdy_cont hbox hx hkδ
    -- For fixed `k`, the quotient equals the averaged partial derivative formula pointwise.
    refine havg_cont.congr ?_
    intro s hs
    exact partial_difference_quotient_eq_average_partial hdPdy_cont hP_dy hbox (hI_subset hs) hkδ hk0
  -- Apply the interval-integral convergence theorem on the restricted horizontal segment.
  simpa using
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (a := z.re) (b := x) (μ := MeasureTheory.volume) hcont_event hquot_unif

/-- Helper for Proposition 3.1: after passing `k → 0` in the primitive quotient identity, the
horizontal change of `Q` equals the integral of `dPdy` along the horizontal segment. -/
lemma vertical_difference_eq_integral_of_partial
    {D : Set ℂ} {P Q F dPdy : ℂ → ℂ} {z : ℂ} {δ x : ℝ}
    (hδ_pos : 0 < δ)
    (hF : IsPrimitiveOn D (P dx + Q dy) F)
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hbox :
      ∀ s ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk s y ∈ D)
    (hx : x ∈ Set.Icc (z.re - δ) (z.re + δ)) :
    Q (Complex.mk x z.im) - Q z = ∫ s in z.re..x, dPdy (Complex.mk s z.im) := by
  have hzre_mem : z.re ∈ Set.Icc (z.re - δ) (z.re + δ) := by
    constructor <;> linarith
  have him_mem : z.im ∈ Set.Icc (z.im - δ) (z.im + δ) := by
    constructor <;> linarith
  have hxz_mem : Complex.mk x z.im ∈ D := hbox x hx z.im him_mem
  have hz_mem : z ∈ D := by
    simpa using hbox z.re hzre_mem z.im him_mem
  have hleft :
      Filter.Tendsto
        (fun k : ℝ ↦
          ((F (Complex.mk x (z.im + k)) - F (Complex.mk x z.im)) / k) -
            ((F (Complex.mk z.re (z.im + k)) - F z) / k))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (Q (Complex.mk x z.im) - Q z)) := by
    -- The two primitive difference quotients converge to the corresponding values of `Q`.
    simpa using
      (primitive_vertical_difference_quotient_tendsto_Q hF hxz_mem).sub
        (primitive_vertical_difference_quotient_tendsto_Q hF hz_mem)
  have hright :
      Filter.Tendsto
        (fun k : ℝ ↦ ∫ s in z.re..x, (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k)
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (∫ s in z.re..x, dPdy (Complex.mk s z.im))) :=
    partial_difference_quotient_interval_integral_tendsto hδ_pos hdPdy_cont hP_dy hbox hx
  have hEq :
      (fun k : ℝ ↦
        ((F (Complex.mk x (z.im + k)) - F (Complex.mk x z.im)) / k) -
          ((F (Complex.mk z.re (z.im + k)) - F z) / k)) =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
      (fun k : ℝ ↦ ∫ s in z.re..x, (P (Complex.mk s (z.im + k)) - P (Complex.mk s z.im)) / k) := by
    have hball : {k : ℝ | |k| < δ} ∈ nhds (0 : ℝ) := by
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using Metric.ball_mem_nhds (0 : ℝ) hδ_pos
    have hball_within : {k : ℝ | |k| < δ} ∈ nhdsWithin (0 : ℝ) ({0}ᶜ) :=
      nhdsWithin_le_nhds hball
    filter_upwards [self_mem_nhdsWithin, hball_within] with k hk0 hkδlt
    exact primitive_vertical_difference_quotient_eq_interval_integral
      hF hdPdy_cont hP_dy hbox hx (le_of_lt hkδlt) hk0
  have hleft_from_right :
      Filter.Tendsto
        (fun k : ℝ ↦
          ((F (Complex.mk x (z.im + k)) - F (Complex.mk x z.im)) / k) -
            ((F (Complex.mk z.re (z.im + k)) - F z) / k))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (∫ s in z.re..x, dPdy (Complex.mk s z.im))) := by
    exact Filter.Tendsto.congr' hEq.symm hright
  exact tendsto_nhds_unique hleft hleft_from_right

/-- Cartan section05 0008_Proposition_3_1 (Proposition 3.1, necessary condition): on an open
set, the existence of a primitive for `P dx + Q dy` implies that the cross partials satisfy
`∂P/∂y = ∂Q/∂x`. -/
theorem hasPrimitiveOn_imp_partialDeriv_eq
    {D : Set ℂ} (hD : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℂ}
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hprimitive : HasPrimitiveOn D (P dx + Q dy)) :
    ∀ z ∈ D, dPdy z = dQdx z := by
  rcases hprimitive with ⟨F, hF⟩
  intro z hz
  -- Route correction: the rectangle/Green route needs continuity of `dQdx`, which is absent from
  -- this Lean surface, so the proof follows the source's primitive-based FTC argument locally.
  rcases Metric.isOpen_iff.mp hD z hz with ⟨r, hr, hball⟩
  let δ : ℝ := r / 4
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_ball : 2 * δ < r := by
    dsimp [δ]
    linarith
  have hbox :
      ∀ x ∈ Set.Icc (z.re - δ) (z.re + δ),
        ∀ y ∈ Set.Icc (z.im - δ) (z.im + δ), Complex.mk x y ∈ D := by
    intro x hx y hy
    exact hball (complex_mk_mem_ball_of_coordinate_bounds hδ_ball hx hy)
  have hleft_deriv :
      HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im) - Q z) (dQdx z) z.re := by
    -- Differentiate the horizontal `Q`-slice and subtract the constant base value.
    simpa using (hQ_dx z hz).sub_const (Q z)
  have hdPdy_contAt : ContinuousAt dPdy z :=
    (hdPdy_cont z hz).continuousAt (hD.mem_nhds hz)
  have hmk_cont : Continuous (fun s : ℝ ↦ Complex.mk s z.im) := by
    -- The horizontal line map into `ℂ` is continuous.
    have hcont : Continuous (fun s : ℝ ↦ (s : ℂ) + (z.im : ℂ) * Complex.I) := by
      exact (Complex.continuous_ofReal.comp continuous_id).add continuous_const
    refine hcont.congr ?_
    intro s
    apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
  have hline_contAt :
      ContinuousAt (fun s : ℝ ↦ dPdy (Complex.mk s z.im)) z.re :=
    hdPdy_contAt.comp hmk_cont.continuousAt
  have hright_deriv :
      HasDerivAt
        (fun x : ℝ ↦ ∫ s in z.re..x, dPdy (Complex.mk s z.im))
        (dPdy z) z.re := by
    -- Differentiate the interval integral at the base point using continuity of the integrand.
    have hIoo_cont :
        ContinuousOn (fun s : ℝ ↦ dPdy (Complex.mk s z.im))
          (Set.Ioo (z.re - δ) (z.re + δ)) := by
      have him_mem : z.im ∈ Set.Icc (z.im - δ) (z.im + δ) := by
        constructor <;> dsimp [δ] <;> linarith
      have hmk_cont : Continuous (fun u : ℝ ↦ Complex.mk u z.im) := by
        have hcont : Continuous (fun u : ℝ ↦ (u : ℂ) + (z.im : ℂ) * Complex.I) := by
          exact (Complex.continuous_ofReal.comp continuous_id).add continuous_const
        refine hcont.congr ?_
        intro u
        apply Complex.ext <;> simp [Complex.mk_eq_add_mul_I]
      refine hdPdy_cont.comp hmk_cont.continuousOn ?_
      intro s hs
      have hsIcc : s ∈ Set.Icc (z.re - δ) (z.re + δ) := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact hbox s hsIcc z.im him_mem
    have hmeas :
        StronglyMeasurableAtFilter (fun s : ℝ ↦ dPdy (Complex.mk s z.im)) (nhds z.re)
          MeasureTheory.volume := by
      have hzre_mem_Ioo : z.re ∈ Set.Ioo (z.re - δ) (z.re + δ) := by
        dsimp [δ]
        constructor <;> linarith
      exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hIoo_cont z.re hzre_mem_Ioo
    simpa using
      intervalIntegral.integral_hasDerivAt_right
        (f := fun s : ℝ ↦ dPdy (Complex.mk s z.im))
        (IntervalIntegrable.refl (f := fun s : ℝ ↦ dPdy (Complex.mk s z.im))
          (μ := MeasureTheory.volume) (a := z.re))
        hmeas hline_contAt
  have hEqNear :
      (fun x : ℝ ↦ Q (Complex.mk x z.im) - Q z) =ᶠ[nhds z.re]
        (fun x : ℝ ↦ ∫ s in z.re..x, dPdy (Complex.mk s z.im)) := by
    have hIoo : Set.Ioo (z.re - δ) (z.re + δ) ∈ nhds z.re := by
      refine Ioo_mem_nhds ?_ ?_ <;> dsimp [δ] <;> linarith
    filter_upwards [hIoo] with x hx
    have hxIcc : x ∈ Set.Icc (z.re - δ) (z.re + δ) := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    -- The source proof's limiting identity holds for every nearby horizontal parameter.
    exact vertical_difference_eq_integral_of_partial hδ_pos hF hdPdy_cont hP_dy hbox hxIcc
  have hright_on_left :
      HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im) - Q z) (dPdy z) z.re :=
    hright_deriv.congr_of_eventuallyEq hEqNear
  -- Compare the two derivatives of the same nearby-equal function at the base point.
  simpa [eq_comm] using HasDerivAt.unique hleft_deriv hright_on_left
-- Proof sketch: Green's formula turns the identity `∂P/∂y = ∂Q/∂x` into vanishing of the
-- boundary integral over every axis-parallel rectangle inside the disc, and one continuous mixed
-- second partial suffices because the equality identifies the other one with it on the disc.
/-- Proposition 3.1 (2): on an open disc in `ℂ`, the identity `∂P/∂y = ∂Q/∂x` is sufficient for
the form `Complex.planarDifferentialForm P Q` to admit a primitive. -/
theorem partialDeriv_eq_imp_hasPrimitiveOn_ball
    (c : ℂ) (r : ℝ) {P Q dPdy dQdx : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Metric.ball c r)) (hQ_cont : ContinuousOn Q (Metric.ball c r))
    (hdPdy_cont : ContinuousOn dPdy (Metric.ball c r))
    (hP_dy : ∀ z ∈ Metric.ball c r, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ Metric.ball c r, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hpartial : ∀ z ∈ Metric.ball c r, dPdy z = dQdx z) :
    HasPrimitiveOn (Metric.ball c r) (Complex.planarDifferentialForm P Q) := by
  -- Route correction: use the explicit source primitive `ballPrimitive c P Q`, prove that
  -- rectangles in the ball have zero boundary integral from Green's formula, and then derive the
  -- Fréchet derivative from the resulting local wedge identity.
  refine ⟨ballPrimitive c P Q, ?_⟩
  intro z hz
  have hrectangle :
      ∀ w₀ w₁ : ℂ,
        Complex.Rectangle w₀ w₁ ⊆ Metric.ball c r →
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁, Complex.planarDifferentialForm P Q ζ = 0 :=
    rectangleBoundaryIntegral_eq_zero_onBall_of_partialDeriv_eq
      hP_cont hQ_cont hdPdy_cont hP_dy hQ_dx hpartial
  -- The rectangle-vanishing invariant is exactly the hypothesis needed for the wedge primitive
  -- linearization proved above.
  exact hasFDerivAt_ballPrimitive_of_zeroRectangleBoundary hP_cont hQ_cont hz hrectangle
