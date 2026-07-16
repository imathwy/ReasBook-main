import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2»
import DifferentialForms_Cartan_1970.cartan.III.section12.«0034_Exercise_21».Index



noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

/-- Helper for Exercise 21: once an explicit strip chart already has the horizontal-axis branch
formula and the signed side test, restricting the affine homeomorphism to a small open strip
packages those data into an `IsBoundaryStraighteningAt` chart. This local copy avoids importing
the rectangle-boundary example module, whose duplicate `axisParallelRectangleBoundaryPath`
declaration collides with the older section-II API still used elsewhere in this file's import
closure. -/
lemma affineBoundaryStripChartExists
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
  · -- The centered strip contains the base point `(t₀, 0)`.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, δ₀, strip] using hstrip
  · intro p hp
    -- Any source point still projects to a parameter in the ambient unit interval.
    have hpStrip : p ∈ strip := by
      simpa [δ, δ₀, strip] using hp
    exact ⟨hstrip_param hpStrip.1, Set.mem_univ _⟩
  · -- The forward chart stays affine, hence `C¹`, after restricting to the open strip.
    simpa [δ, δ₀, strip] using e.toContinuousAffineMap.contDiff.contDiffOn
  · -- The inverse chart inherits the same affine regularity on its open target.
    simpa [δ, δ₀, strip] using e.symm.toContinuousAffineMap.contDiff.contDiffOn
  · intro t ht
    -- On the restricted source, the horizontal axis is exactly the chosen branch of `γ`.
    have htStrip : (t, 0) ∈ strip := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, δ, δ₀, strip] using ht
    simpa [δ, δ₀] using hmap_axis htStrip.1
  · -- The chart image of the boundary branch is exactly the horizontal axis in the strip.
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


/-- Helper for Exercise 21: near an interior upper-lip point, the explicit affine normal tube
stays inside the ambient annulus and keeps the same sign pattern `re z < 0 < im z`. This is the
radius/control part of the source-faithful strip chart before converting signed height into
membership in the slit annulus. -/
lemma exercise21_upper_lip_small_strip_ambient
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let φ := Real.pi - Real.arctan (ε / r)
      let z := circleMap 0 ρ φ + (s : ℂ) * circleMap 0 1 (φ - Real.pi / 2)
      ε < ‖z‖ ∧ ‖z‖ < r ∧ z.re < 0 ∧ 0 < z.im := by
  let θ : ℝ := Real.arctan (ε / r)
  have hr : 0 < r := lt_trans hε hεr
  have hρ₀_pos : 0 < ρ₀ := lt_trans hε hρ₀.1
  have hcos_pos : 0 < Real.cos θ := by
    simpa [θ] using Real.cos_arctan_pos (ε / r)
  have hsin_pos : 0 < Real.sin θ := by
    simpa [θ] using Real.sin_arctan_pos.mpr (div_pos hε hr)
  have hsin_nonneg : 0 ≤ Real.sin θ := hsin_pos.le
  have hcos_nonneg : 0 ≤ Real.cos θ := hcos_pos.le
  have hsin_le_one : Real.sin θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have hcos_le_one : Real.cos θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  let η : ℝ :=
    min ((ρ₀ - ε) / 4)
      (min ((r - ρ₀) / 4)
        (min (ρ₀ / 4)
          (min (ρ₀ * Real.cos θ / 4) (ρ₀ * Real.sin θ / 4))))
  have hη_pos : 0 < η := by
    have hρ₀ε : 0 < (ρ₀ - ε) / 4 := by
      nlinarith [hρ₀.1]
    have hrρ₀ : 0 < (r - ρ₀) / 4 := by
      nlinarith [hρ₀.2]
    have hρ₀q : 0 < ρ₀ / 4 := by
      positivity
    have hcosq : 0 < ρ₀ * Real.cos θ / 4 := by
      positivity
    have hsinq : 0 < ρ₀ * Real.sin θ / 4 := by
      positivity
    dsimp [η]
    exact lt_min hρ₀ε (lt_min hrρ₀ (lt_min hρ₀q (lt_min hcosq hsinq)))
  refine ⟨η, hη_pos, ?_⟩
  intro ρ s hρ hs
  let φ : ℝ := Real.pi - Real.arctan (ε / r)
  let n : ℂ := circleMap 0 1 (φ - Real.pi / 2)
  let z : ℂ := circleMap 0 ρ φ + (s : ℂ) * n
  have hη_rhoε : η ≤ (ρ₀ - ε) / 4 := by
    dsimp [η]
    exact min_le_left _ _
  have hη_rhor : η ≤ (r - ρ₀) / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_rho : η ≤ ρ₀ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_cos : η ≤ ρ₀ * Real.cos θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hη_sin : η ≤ ρ₀ * Real.sin θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hρ_lower : ρ₀ - η < ρ := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_upper : ρ < ρ₀ + η := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_pos : 0 < ρ := by
    linarith
  have hnorm_upper :
      ‖z‖ < r := by
    have hupper :
        ‖z‖ ≤ ρ + |s| := by
      calc
        ‖z‖ = ‖circleMap 0 ρ φ + (s : ℂ) * n‖ := by rfl
        _ ≤ ‖circleMap 0 ρ φ‖ + ‖(s : ℂ) * n‖ := norm_add_le _ _
        _ = ρ + |s| := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp [n]
    have hρs_lt : ρ + |s| < r := by
      have hη_half : 2 * η ≤ (r - ρ₀) / 2 := by
        nlinarith
      have hstep : ρ + |s| < ρ₀ + 2 * η := by
        linarith
      linarith
    exact lt_of_le_of_lt hupper hρs_lt
  have hnorm_lower :
      ε < ‖z‖ := by
    have hlower :
        ρ - |s| ≤ ‖z‖ := by
      calc
        ρ - |s| = ‖circleMap 0 ρ φ‖ - ‖(s : ℂ) * n‖ := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp
        _ ≤ ‖circleMap 0 ρ φ - (-((s : ℂ) * n))‖ := by
          simpa using norm_sub_norm_le (circleMap 0 ρ φ) (-((s : ℂ) * n))
        _ = ‖z‖ := by simp [z]
    have hρs_gt : ε < ρ - |s| := by
      have hstep : ρ₀ - 2 * η < ρ - |s| := by
        linarith
      have hη_half : 2 * η ≤ (ρ₀ - ε) / 2 := by
        nlinarith
      linarith
    exact lt_of_lt_of_le hρs_gt hlower
  have hz_re_formula :
      z.re = -(ρ * Real.cos θ) + s * Real.sin θ := by
    dsimp [z, n, φ, θ]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
  have hz_im_formula :
      z.im = ρ * Real.sin θ + s * Real.cos θ := by
    dsimp [z, n, φ, θ]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
  have hs_sin_le : s * Real.sin θ ≤ |s| := by
    have hs_mul :
        s * Real.sin θ ≤ |s| * Real.sin θ := by
      exact mul_le_mul_of_nonneg_right (le_abs_self s) hsin_nonneg
    have hs_mul' : |s| * Real.sin θ ≤ |s| := by
      nlinarith [abs_nonneg s, hsin_le_one]
    exact hs_mul.trans hs_mul'
  have hs_cos_ge : -|s| ≤ s * Real.cos θ := by
    have hleft : -|s| * Real.cos θ ≤ s * Real.cos θ := by
      exact mul_le_mul_of_nonneg_right (neg_abs_le s) hcos_nonneg
    have hright : -|s| ≤ -|s| * Real.cos θ := by
      nlinarith [abs_nonneg s, hcos_le_one]
    exact hright.trans hleft
  have hz_re_neg : z.re < 0 := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρcos_big : 3 * (ρ₀ * Real.cos θ) / 4 < ρ * Real.cos θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.cos θ / 4 := by
      exact lt_of_lt_of_le hs hη_cos
    rw [hz_re_formula]
    nlinarith
  have hz_im_pos : 0 < z.im := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρsin_big : 3 * (ρ₀ * Real.sin θ) / 4 < ρ * Real.sin θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.sin θ / 4 := by
      exact lt_of_lt_of_le hs hη_sin
    rw [hz_im_formula]
    nlinarith
  exact ⟨hnorm_lower, hnorm_upper, hz_re_neg, hz_im_pos⟩

/-- Helper for Exercise 21: near an interior lower-lip point, the explicit affine normal tube
stays inside the ambient annulus and keeps the sign pattern `re z < 0` and `im z < 0`. This is
the symmetric lower-branch radius/control lemma needed before translating signed height into slit-
annulus membership. -/
lemma exercise21_lower_lip_small_strip_ambient
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let φ := -Real.pi + Real.arctan (ε / r)
      let z := circleMap 0 ρ φ + (s : ℂ) * circleMap 0 1 (φ + Real.pi / 2)
      ε < ‖z‖ ∧ ‖z‖ < r ∧ z.re < 0 ∧ z.im < 0 := by
  let θ : ℝ := Real.arctan (ε / r)
  have hr : 0 < r := lt_trans hε hεr
  have hρ₀_pos : 0 < ρ₀ := lt_trans hε hρ₀.1
  have hcos_pos : 0 < Real.cos θ := by
    simpa [θ] using Real.cos_arctan_pos (ε / r)
  have hsin_pos : 0 < Real.sin θ := by
    simpa [θ] using Real.sin_arctan_pos.mpr (div_pos hε hr)
  have hsin_nonneg : 0 ≤ Real.sin θ := hsin_pos.le
  have hcos_nonneg : 0 ≤ Real.cos θ := hcos_pos.le
  have hsin_le_one : Real.sin θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have hcos_le_one : Real.cos θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  let η : ℝ :=
    min ((ρ₀ - ε) / 4)
      (min ((r - ρ₀) / 4)
        (min (ρ₀ / 4)
          (min (ρ₀ * Real.cos θ / 4) (ρ₀ * Real.sin θ / 4))))
  have hη_pos : 0 < η := by
    have hρ₀ε : 0 < (ρ₀ - ε) / 4 := by
      nlinarith [hρ₀.1]
    have hrρ₀ : 0 < (r - ρ₀) / 4 := by
      nlinarith [hρ₀.2]
    have hρ₀q : 0 < ρ₀ / 4 := by
      positivity
    have hcosq : 0 < ρ₀ * Real.cos θ / 4 := by
      positivity
    have hsinq : 0 < ρ₀ * Real.sin θ / 4 := by
      positivity
    dsimp [η]
    exact lt_min hρ₀ε (lt_min hrρ₀ (lt_min hρ₀q (lt_min hcosq hsinq)))
  refine ⟨η, hη_pos, ?_⟩
  intro ρ s hρ hs
  let φ : ℝ := -Real.pi + Real.arctan (ε / r)
  let n : ℂ := circleMap 0 1 (φ + Real.pi / 2)
  let z : ℂ := circleMap 0 ρ φ + (s : ℂ) * n
  have hη_rhoε : η ≤ (ρ₀ - ε) / 4 := by
    dsimp [η]
    exact min_le_left _ _
  have hη_rhor : η ≤ (r - ρ₀) / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_rho : η ≤ ρ₀ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_cos : η ≤ ρ₀ * Real.cos θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hη_sin : η ≤ ρ₀ * Real.sin θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hρ_lower : ρ₀ - η < ρ := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_upper : ρ < ρ₀ + η := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_pos : 0 < ρ := by
    linarith
  have hnorm_upper : ‖z‖ < r := by
    have hupper : ‖z‖ ≤ ρ + |s| := by
      calc
        ‖z‖ = ‖circleMap 0 ρ φ + (s : ℂ) * n‖ := by rfl
        _ ≤ ‖circleMap 0 ρ φ‖ + ‖(s : ℂ) * n‖ := norm_add_le _ _
        _ = ρ + |s| := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp [n]
    have hρs_lt : ρ + |s| < r := by
      have hη_half : 2 * η ≤ (r - ρ₀) / 2 := by
        nlinarith
      have hstep : ρ + |s| < ρ₀ + 2 * η := by
        linarith
      linarith
    exact lt_of_le_of_lt hupper hρs_lt
  have hnorm_lower : ε < ‖z‖ := by
    have hlower : ρ - |s| ≤ ‖z‖ := by
      calc
        ρ - |s| = ‖circleMap 0 ρ φ‖ - ‖(s : ℂ) * n‖ := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp
        _ ≤ ‖circleMap 0 ρ φ - (-((s : ℂ) * n))‖ := by
          simpa using norm_sub_norm_le (circleMap 0 ρ φ) (-((s : ℂ) * n))
        _ = ‖z‖ := by simp [z]
    have hρs_gt : ε < ρ - |s| := by
      have hstep : ρ₀ - 2 * η < ρ - |s| := by
        linarith
      have hη_half : 2 * η ≤ (ρ₀ - ε) / 2 := by
        nlinarith
      linarith
    exact lt_of_lt_of_le hρs_gt hlower
  have hz_re_formula :
      z.re = -(ρ * Real.cos θ) + s * Real.sin θ := by
    have hφ : -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi := by
      ring
    have hcombo :
        Real.arctan (ε / r) - Real.pi + Real.pi / 2 = Real.arctan (ε / r) - Real.pi / 2 := by
      ring
    dsimp [z, n, φ, θ]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, hφ, hcombo, Real.cos_sub_pi, Real.sin_sub_pi,
      Real.cos_sub_pi_div_two]
  have hz_im_formula :
      z.im = -(ρ * Real.sin θ) - s * Real.cos θ := by
    have hφ : -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi := by
      ring
    have hcombo :
        Real.arctan (ε / r) - Real.pi + Real.pi / 2 = Real.arctan (ε / r) - Real.pi / 2 := by
      ring
    dsimp [z, n, φ, θ]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, hφ, hcombo, Real.sin_sub_pi,
      Real.sin_sub_pi_div_two]
    ring
  have hs_sin_le : s * Real.sin θ ≤ |s| := by
    have hs_mul : s * Real.sin θ ≤ |s| * Real.sin θ := by
      exact mul_le_mul_of_nonneg_right (le_abs_self s) hsin_nonneg
    have hs_mul' : |s| * Real.sin θ ≤ |s| := by
      nlinarith [abs_nonneg s, hsin_le_one]
    exact hs_mul.trans hs_mul'
  have hs_cos_ge : -|s| ≤ s * Real.cos θ := by
    have hleft : -|s| * Real.cos θ ≤ s * Real.cos θ := by
      exact mul_le_mul_of_nonneg_right (neg_abs_le s) hcos_nonneg
    have hright : -|s| ≤ -|s| * Real.cos θ := by
      nlinarith [abs_nonneg s, hcos_le_one]
    exact hright.trans hleft
  have hz_re_neg : z.re < 0 := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρcos_big : 3 * (ρ₀ * Real.cos θ) / 4 < ρ * Real.cos θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.cos θ / 4 := by
      exact lt_of_lt_of_le hs hη_cos
    rw [hz_re_formula]
    nlinarith
  have hz_im_neg : z.im < 0 := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρsin_big : 3 * (ρ₀ * Real.sin θ) / 4 < ρ * Real.sin θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.sin θ / 4 := by
      exact lt_of_lt_of_le hs hη_sin
    rw [hz_im_formula]
    nlinarith
  exact ⟨hnorm_lower, hnorm_upper, hz_re_neg, hz_im_neg⟩

/-- Helper for Exercise 21: on the upper half-plane side of the slit, membership in the slit
annulus is equivalent to lying on or above the upper boundary line of the removed wedge. This is
the canonical rewrite that turns the affine-strip signed-height identity into a set-membership
statement. -/
lemma exercise21NegativeWedgeAnnulus_mem_iff_upper_signed_height_nonneg
    {r ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzr : ‖z‖ < r) (hzre : z.re < 0) (hzim : 0 < z.im) :
    z ∈ exercise21NegativeWedgeAnnulus r ε ↔ 0 ≤ z.im + (ε / r) * z.re := by
  constructor
  · intro hz
    have hnot_height : ¬ z.im < (ε / r) * (-z.re) := by
      intro hlt
      exact hz.2 ⟨hzre, by simpa [abs_of_pos hzim] using hlt⟩
    have hheight : (ε / r) * (-z.re) ≤ z.im := le_of_not_gt hnot_height
    linarith
  · intro hheight
    refine ⟨⟨le_of_lt hεz, le_of_lt hzr⟩, ?_⟩
    intro hwedge
    have hlt : z.im < (ε / r) * (-z.re) := by
      simpa [abs_of_pos hzim] using hwedge.2
    linarith

/-- Helper for Exercise 21: on the lower half-plane side of the slit, membership in the slit
annulus is equivalent to lying on or above the lower boundary line measured by the reflected
signed height `-im z + (ε / r) re z`. -/
lemma exercise21NegativeWedgeAnnulus_mem_iff_lower_signed_height_nonneg
    {r ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzr : ‖z‖ < r) (hzre : z.re < 0) (hzim : z.im < 0) :
    z ∈ exercise21NegativeWedgeAnnulus r ε ↔ 0 ≤ -z.im + (ε / r) * z.re := by
  constructor
  · intro hz
    have hnot_height : ¬ -z.im < (ε / r) * (-z.re) := by
      intro hlt
      exact hz.2 ⟨hzre, by simpa [abs_of_neg hzim] using hlt⟩
    have hheight : (ε / r) * (-z.re) ≤ -z.im := le_of_not_gt hnot_height
    linarith
  · intro hheight
    refine ⟨⟨le_of_lt hεz, le_of_lt hzr⟩, ?_⟩
    intro hwedge
    have hlt : -z.im < (ε / r) * (-z.re) := by
      simpa [abs_of_neg hzim] using hwedge.2
    linarith

/-- Helper for Exercise 21: strict annulus bounds together with a positive upper signed height put
a point in the interior of the slit annulus. This owner-facing bridge lets the chart proofs use
the explicit strip inequalities directly, without reopening the frontier transport each time. -/
lemma exercise21NegativeWedgeAnnulus_mem_interior_of_upper_gap
    {r ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzr : ‖z‖ < r) (hzim : 0 < z.im)
    (hheight : 0 < z.im + (ε / r) * z.re) :
    z ∈ interior (exercise21NegativeWedgeAnnulus r ε) := by
  let U : Set ℂ :=
    {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < r ∧ 0 < w.im ∧ 0 < w.im + (ε / r) * w.re}
  have hU_open : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_norm).inter <|
      (isOpen_lt continuous_norm continuous_const).inter <|
        (isOpen_lt continuous_const continuous_im).inter ?_
    simpa using
      isOpen_lt continuous_const (continuous_im.add (continuous_const.mul continuous_re))
  have hzU : z ∈ U := ⟨hεz, hzr, hzim, hheight⟩
  refine mem_interior.mpr ⟨U, ?_, hU_open, hzU⟩
  intro w hw
  refine ⟨⟨le_of_lt hw.1, le_of_lt hw.2.1⟩, ?_⟩
  intro hwedge
  have hw_im_lt : w.im < (ε / r) * (-w.re) := by
    simpa [abs_of_pos hw.2.2.1] using hwedge.2
  have hw_gap_pos : 0 < w.im - (ε / r) * (-w.re) := by
    linarith [hw.2.2.2]
  linarith

/-- Helper for Exercise 21: the reflected lower signed-height inequality likewise upgrades a point
to interior membership in the slit annulus. This is the lower-lip companion to the upper-gap
criterion. -/
lemma exercise21NegativeWedgeAnnulus_mem_interior_of_lower_gap
    {r ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzr : ‖z‖ < r) (hzim : z.im < 0)
    (hheight : 0 < -z.im + (ε / r) * z.re) :
    z ∈ interior (exercise21NegativeWedgeAnnulus r ε) := by
  let U : Set ℂ :=
    {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < r ∧ w.im < 0 ∧ w.im < (ε / r) * w.re}
  have hU_open : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_norm).inter <|
      (isOpen_lt continuous_norm continuous_const).inter <|
        (isOpen_lt continuous_im continuous_const).inter ?_
    simpa using isOpen_lt continuous_im (continuous_const.mul continuous_re)
  have hzU : z ∈ U := by
    refine ⟨hεz, hzr, hzim, ?_⟩
    linarith
  refine mem_interior.mpr ⟨U, ?_, hU_open, hzU⟩
  intro w hw
  refine ⟨⟨le_of_lt hw.1, le_of_lt hw.2.1⟩, ?_⟩
  intro hwedge
  have hw_im_lt : -w.im < (ε / r) * (-w.re) := by
    simpa [abs_of_neg hw.2.2.1] using hwedge.2
  have hw_gap_pos : 0 < -w.im - (ε / r) * (-w.re) := by
    linarith [hw.2.2.2]
  linarith

/-- Helper for Exercise 21: near an interior upper-lip point, the sign of the transverse
parameter decides whether the explicit affine strip point lies inside or outside the slit annulus.
This is the pointwise side-of-boundary statement used later to package the upper strip chart. -/
lemma exercise21_upper_lip_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let z := circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) +
        (s : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
      (s < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < s → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  rcases exercise21_upper_lip_small_strip_ambient hε hεr hρ₀ with ⟨η, hη, hambient⟩
  refine ⟨η, hη, ?_⟩
  intro ρ s hρ hs
  let z := circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) +
    (s : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
  have hambient' := hambient hρ hs
  have hsigned :
      z.im + (ε / r) * z.re =
        s *
          (Real.cos (Real.arctan (ε / r)) +
            (ε / r) * Real.sin (Real.arctan (ε / r))) := by
    simpa [z] using exercise21_upper_lip_normal_signed_height r ε ρ s
  have hcoeff :
      0 <
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) :=
    exercise21_lip_transverse_coefficient_pos r ε hε hεr
  constructor
  · intro hsneg hzmem
    have hheight :
        0 ≤ z.im + (ε / r) * z.re :=
      (exercise21NegativeWedgeAnnulus_mem_iff_upper_signed_height_nonneg
        hambient'.1 hambient'.2.1 hambient'.2.2.1 hambient'.2.2.2).1 hzmem
    rw [hsigned] at hheight
    nlinarith
  · intro hspos
    have hheight :
        0 < z.im + (ε / r) * z.re := by
      rw [hsigned]
      nlinarith
    exact exercise21NegativeWedgeAnnulus_mem_interior_of_upper_gap
      hambient'.1 hambient'.2.1 hambient'.2.2.2 hheight

/-- Helper for Exercise 21: near an interior lower-lip point, positive transverse height moves
into the slit annulus and negative transverse height moves out of it. This is the reflected
pointwise side-of-boundary statement for the lower strip chart. -/
lemma exercise21_lower_lip_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let z := circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) +
        (s : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
      (s < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < s → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  rcases exercise21_lower_lip_small_strip_ambient hε hεr hρ₀ with ⟨η, hη, hambient⟩
  refine ⟨η, hη, ?_⟩
  intro ρ s hρ hs
  let z := circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) +
    (s : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
  have hambient' := hambient hρ hs
  have hsigned :
      -z.im + (ε / r) * z.re =
        s *
          (Real.cos (Real.arctan (ε / r)) +
            (ε / r) * Real.sin (Real.arctan (ε / r))) := by
    simpa [z] using exercise21_lower_lip_normal_signed_height r ε ρ s
  have hcoeff :
      0 <
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) :=
    exercise21_lip_transverse_coefficient_pos r ε hε hεr
  constructor
  · intro hsneg hzmem
    have hheight :
        0 ≤ -z.im + (ε / r) * z.re :=
      (exercise21NegativeWedgeAnnulus_mem_iff_lower_signed_height_nonneg
        hambient'.1 hambient'.2.1 hambient'.2.2.1 hambient'.2.2.2).1 hzmem
    rw [hsigned] at hheight
    nlinarith
  · intro hspos
    have hheight :
        0 < -z.im + (ε / r) * z.re := by
      rw [hsigned]
      nlinarith
    exact exercise21NegativeWedgeAnnulus_mem_interior_of_lower_gap
      hambient'.1 hambient'.2.1 hambient'.2.2.2 hheight

/-- Helper for Exercise 21: once the angle stays in the surviving principal-argument interval,
membership of a circle point in the slit annulus is purely radial. This is the canonical circle
rewrite used by the inner and outer boundary charts. -/
lemma exercise21NegativeWedgeAnnulus_circleMap_mem_iff_radius_mem_Icc
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (-Real.pi) Real.pi)
    (hφsurvive :
      φ ∈ Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r))) :
    circleMap 0 ρ φ ∈ exercise21NegativeWedgeAnnulus r ε ↔ ρ ∈ Set.Icc ε r := by
  constructor
  · intro hz
    simpa [norm_circleMap_zero, abs_of_pos hρ] using hz.1
  · intro hρIcc
    refine ⟨?_, ?_⟩
    · simpa [norm_circleMap_zero, abs_of_pos hρ] using hρIcc
    · exact
        (exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
          r ε ρ hε hεr hρ hφ).2 hφsurvive

/-- Helper for Exercise 21: strict annulus bounds together with a positive real part already put a
point in the interior of the slit annulus, because the removed wedge lies entirely in the left
half-plane. -/
lemma exercise21NegativeWedgeAnnulus_mem_interior_of_pos_re
    {r ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzr : ‖z‖ < r) (hzre : 0 < z.re) :
    z ∈ interior (exercise21NegativeWedgeAnnulus r ε) := by
  let U : Set ℂ := {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < r ∧ 0 < w.re}
  have hU_open : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_norm).inter <|
      (isOpen_lt continuous_norm continuous_const).inter ?_
    simpa using isOpen_lt continuous_const continuous_re
  have hzU : z ∈ U := ⟨hεz, hzr, hzre⟩
  refine mem_interior.mpr ⟨U, ?_, hU_open, hzU⟩
  intro w hw
  refine ⟨⟨le_of_lt hw.1, le_of_lt hw.2.1⟩, ?_⟩
  intro hwedge
  exact not_lt_of_ge hw.2.2.le hwedge.1

/-- Helper for Exercise 21: a circle point with strict radius and surviving principal angle lies in
the interior of the slit annulus. This owner-facing bridge removes the repeated frontier transport
from the circular chart proofs. -/
lemma exercise21NegativeWedgeAnnulus_circleMap_mem_interior_of_radius_mem_Ioo
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : ρ ∈ Set.Ioo ε r) {φ : ℝ}
    (hφ :
      φ ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r))) :
    circleMap 0 ρ φ ∈ interior (exercise21NegativeWedgeAnnulus r ε) := by
  let z : ℂ := circleMap 0 ρ φ
  have hr : 0 < r := lt_trans hε hεr
  have hρ_pos : 0 < ρ := lt_trans hε hρ.1
  have hθ := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hφIcc : φ ∈ Set.Icc (-Real.pi) Real.pi := by
    constructor
    · linarith [hφ.1, hθ.1]
    · linarith [hφ.2, hθ.2, Real.pi_pos]
  have hεz : ε < ‖z‖ := by
    simpa [z, norm_circleMap_zero, abs_of_pos hρ_pos] using hρ.1
  have hzr : ‖z‖ < r := by
    simpa [z, norm_circleMap_zero, abs_of_pos hρ_pos] using hρ.2
  by_cases hzre : 0 < z.re
  · -- On the right half-plane side, the point is automatically away from the removed wedge.
    exact exercise21NegativeWedgeAnnulus_mem_interior_of_pos_re hεz hzr hzre
  · by_cases hzim : 0 < z.im
    · -- On the upper side, the surviving-angle inequality is exactly the positive signed height.
      have hφpos : 0 < φ := by
        by_contra hφ_nonpos
        have hsin_nonpos : Real.sin φ ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hφ_nonpos) hφIcc.1
        have hz_im_nonpos : z.im ≤ 0 := by
          calc
            z.im = ρ * Real.sin φ := by simp [z, circleMap_zero_im]
            _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ_pos.le hsin_nonpos
        linarith
      have hangle :
          φ + Real.arctan (ε / r) ∈ Set.Ioo (0 : ℝ) Real.pi := by
        constructor
        · linarith
        · linarith [hφ.2, hθ.2, Real.pi_pos]
      have hheight' :
          0 < Real.sin φ + (ε / r) * Real.cos φ := by
        have hrewrite :
            Real.sin φ + (ε / r) * Real.cos φ =
              Real.sin (φ + Real.arctan (ε / r)) / Real.cos (Real.arctan (ε / r)) := by
          have hcos : Real.cos (Real.arctan (ε / r)) ≠ 0 := by
            exact (Real.cos_arctan_pos (ε / r)).ne'
          rw [Real.sin_add, Real.sin_arctan, Real.cos_arctan]
          field_simp [hcos]
        rw [hrewrite]
        exact div_pos (Real.sin_pos_of_mem_Ioo hangle) (Real.cos_arctan_pos (ε / r))
      have hheight :
          0 < z.im + (ε / r) * z.re := by
        calc
          z.im + (ε / r) * z.re = ρ * (Real.sin φ + (ε / r) * Real.cos φ) := by
            simp [z, circleMap_zero_re, circleMap_zero_im]
            ring
          _ = ρ * (Real.sin φ + (ε / r) * Real.cos φ) := rfl
          _ > 0 := mul_pos hρ_pos hheight'
      exact exercise21NegativeWedgeAnnulus_mem_interior_of_upper_gap hεz hzr hzim hheight
    · by_cases hzim_neg : z.im < 0
      · -- On the lower side, the reflected signed height is positive by the same angle algebra.
        have hφneg : φ < 0 := by
          by_contra hφ_nonneg
          have hsinnn : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc ⟨le_of_not_gt hφ_nonneg, hφIcc.2⟩
          have hz_im_nn : 0 ≤ z.im := by
            calc
              z.im = ρ * Real.sin φ := by simp [z, circleMap_zero_im]
              _ ≥ 0 := mul_nonneg hρ_pos.le hsinnn
          linarith
        have hangle :
            Real.arctan (ε / r) - φ ∈ Set.Ioo (0 : ℝ) Real.pi := by
          constructor <;> linarith [hφ.1, hφ.2, hφneg, hθ.1, hθ.2, Real.pi_pos]
        have hheight' :
            0 < -Real.sin φ + (ε / r) * Real.cos φ := by
          have hrewrite :
              -Real.sin φ + (ε / r) * Real.cos φ =
                Real.sin (Real.arctan (ε / r) - φ) / Real.cos (Real.arctan (ε / r)) := by
            have hcos : Real.cos (Real.arctan (ε / r)) ≠ 0 := by
              exact (Real.cos_arctan_pos (ε / r)).ne'
            rw [Real.sin_sub, Real.sin_arctan, Real.cos_arctan]
            field_simp [hcos]
            ring
          rw [hrewrite]
          exact div_pos (Real.sin_pos_of_mem_Ioo hangle) (Real.cos_arctan_pos (ε / r))
        have hheight :
            0 < -z.im + (ε / r) * z.re := by
          calc
            -z.im + (ε / r) * z.re = ρ * (-Real.sin φ + (ε / r) * Real.cos φ) := by
              simp [z, circleMap_zero_re, circleMap_zero_im]
              ring
            _ > 0 := mul_pos hρ_pos hheight'
        exact exercise21NegativeWedgeAnnulus_mem_interior_of_lower_gap hεz hzr hzim_neg hheight
      · -- If both imaginary-side tests fail, the principal-angle interval forces `φ = 0`.
        have hzim_zero : z.im = 0 := le_antisymm (le_of_not_gt hzim) (le_of_not_gt hzim_neg)
        have hsin_zero : Real.sin φ = 0 := by
          have hz_im_eq : z.im = ρ * Real.sin φ := by simp [z, circleMap_zero_im]
          rw [hz_im_eq] at hzim_zero
          nlinarith
        have hφ_eq_zero : φ = 0 := by
          have hφ_lt_pi : φ < Real.pi := by
            linarith [hφ.2, hθ.2, Real.pi_pos]
          have hneg_pi_lt_φ : -Real.pi < φ := by
            linarith [hφ.1, hθ.1]
          exact (Real.sin_eq_zero_iff_of_lt_of_lt hneg_pi_lt_φ hφ_lt_pi).1 hsin_zero
        have hzre_pos : 0 < z.re := by
          calc
            z.re = ρ * Real.cos φ := by simp [z, circleMap_zero_re]
            _ = ρ := by simp [hφ_eq_zero]
            _ > 0 := hρ_pos
        exact exercise21NegativeWedgeAnnulus_mem_interior_of_pos_re hεz hzr hzre_pos

/-- Helper for Exercise 21: moving the inner surviving circle in the radial direction only changes
its radius, so the tube map can be rewritten without any transport noise. -/
private lemma exercise21_inner_arc_add_real_mul_radial_eq_circleMap_radius_add
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

/-- Helper for Exercise 21: moving the outer surviving circle against the inward radial direction
decreases the radius while keeping the angle fixed. -/
private lemma exercise21_outer_arc_add_real_mul_inward_eq_circleMap_radius_sub
    (r α u : ℝ) :
    circleMap 0 r α + (u : ℂ) * (-Complex.exp (α * Complex.I)) =
      circleMap 0 (r - u) α := by
  rw [circleMap, zero_add, circleMap, zero_add]
  calc
    (r : ℂ) * Complex.exp (α * Complex.I) + (u : ℂ) * (-Complex.exp (α * Complex.I)) =
        (((r : ℂ) - u) * Complex.exp (α * Complex.I)) := by
          ring
    _ = (((r - u : ℝ) : ℂ) * Complex.exp (α * Complex.I)) := by
          norm_num

/-- Helper for Exercise 21: near an interior point of the inner circular branch, negative
transverse height exits through the inner boundary and positive transverse height moves into the
slit-annulus interior while keeping the same surviving angle. -/
lemma exercise21_inner_arc_chart_side_of_annulus
    {r ε t₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (ht₀ : t₀ ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let α := AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (8 * p.1 - 1)
      let z := circleMap 0 (ε + p.2) α
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  let eps_t : ℝ := min (t₀ - 1 / 8) (1 / 4 - t₀) / 2
  let eps_u : ℝ := min (ε / 2) ((r - ε) / 2)
  let η : ℝ := min eps_t eps_u
  have hθ := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hεt_pos : 0 < eps_t := by
    dsimp [eps_t]
    have hleft : 0 < t₀ - 1 / 8 := sub_pos.mpr ht₀.1
    have hright : 0 < 1 / 4 - t₀ := sub_pos.mpr ht₀.2
    have hmin : 0 < min (t₀ - 1 / 8) (1 / 4 - t₀) := lt_min hleft hright
    linarith
  have hεu_pos : 0 < eps_u := by
    dsimp [eps_u]
    have hleft : 0 < ε / 2 := by positivity
    have hright : 0 < (r - ε) / 2 := by linarith
    exact lt_min hleft hright
  have hη_pos : 0 < η := lt_min hεt_pos hεu_pos
  have hεu_lt_ε : eps_u < ε := by
    dsimp [eps_u]
    have hmin_le : min (ε / 2) ((r - ε) / 2) ≤ ε / 2 := min_le_left _ _
    linarith
  have hε_plus : ε + eps_u < r := by
    dsimp [eps_u]
    have hmin_le : min (ε / 2) ((r - ε) / 2) ≤ (r - ε) / 2 := min_le_right _ _
    linarith
  refine ⟨η, hη_pos, ?_⟩
  intro p hp₁ hp₂
  have hp₂η : |p.2| < eps_u := lt_of_lt_of_le hp₂ (min_le_right _ _)
  have hp₂_lower : -eps_u < p.2 := (abs_lt.mp hp₂η).1
  have hp₂_upper : p.2 < eps_u := (abs_lt.mp hp₂η).2
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
    (Real.pi - Real.arctan (ε / r))
    (-Real.pi + Real.arctan (ε / r))
    (8 * p.1 - 1)
  have hparam : 8 * p.1 - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp₁_branch.1, hp₁_branch.2]
  have hα :
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
  constructor
  · intro hp₂_neg hz
    have hρ_pos : 0 < ε + p.2 := by
      linarith
    have hρ_lt : ε + p.2 < ε := by
      linarith
    have hz_norm : ε ≤ ε + p.2 := by
      simpa [α, norm_circleMap_zero, abs_of_pos hρ_pos] using hz.1.1
    exact (not_le_of_gt hρ_lt) hz_norm
  · intro hp₂_pos
    have hρ : ε + p.2 ∈ Set.Ioo ε r := by
      constructor
      · linarith
      · linarith [hε_plus]
    simpa [α] using
      exercise21NegativeWedgeAnnulus_circleMap_mem_interior_of_radius_mem_Ioo
        r ε (ε + p.2) hε hεr hρ hα

/-- Helper for Exercise 21: near an interior point of the outer circular branch, moving inward
enters the slit-annulus interior and moving outward exits through the outer boundary while keeping
the same surviving angle. -/
lemma exercise21_outer_arc_chart_side_of_annulus
    {r ε t₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (ht₀ : t₀ ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let α := AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (2 * p.1 - 1)
      let z := circleMap 0 (r - p.2) α
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  let eps_t : ℝ := min (t₀ - 1 / 2) (1 - t₀) / 2
  let eps_u : ℝ := (r - ε) / 2
  let η : ℝ := min eps_t eps_u
  have hθ := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
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
  have hε_minus : ε < r - eps_u := by
    dsimp [eps_u]
    linarith
  refine ⟨η, hη_pos, ?_⟩
  intro p hp₁ hp₂
  have hp₂η : |p.2| < eps_u := lt_of_lt_of_le hp₂ (min_le_right _ _)
  have hp₂_lower : -eps_u < p.2 := (abs_lt.mp hp₂η).1
  have hp₂_upper : p.2 < eps_u := (abs_lt.mp hp₂η).2
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
    (-Real.pi + Real.arctan (ε / r))
    (Real.pi - Real.arctan (ε / r))
    (2 * p.1 - 1)
  have hparam : 2 * p.1 - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp₁_branch.1, hp₁_branch.2]
  have hα :
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
  constructor
  · intro hp₂_neg hz
    have hρ_pos : 0 < r - p.2 := by
      linarith [hεr, hε]
    have hρ_gt : r < r - p.2 := by
      linarith
    have hz_norm : r - p.2 ≤ r := by
      simpa [α, norm_circleMap_zero, abs_of_pos hρ_pos] using hz.1.2
    exact (not_le_of_gt hρ_gt) hz_norm
  · intro hp₂_pos
    have hρ : r - p.2 ∈ Set.Ioo ε r := by
      constructor
      · linarith [hε_minus]
      · linarith
    simpa [α] using
      exercise21NegativeWedgeAnnulus_circleMap_mem_interior_of_radius_mem_Ioo
        r ε (r - p.2) hε hεr hρ hα

/-- Helper for Exercise 21: quarter-turning a complex tangent in real coordinates is multiplication
by `I` before converting back to `Plane`. -/
lemma exercise21_rot90_equivRealProd_eq_equivRealProd_mul_I (z : ℂ) :
    rot90 (Complex.equivRealProd z) = Complex.equivRealProd (z * Complex.I) := by
  ext <;> simp [rot90, Complex.equivRealProd]

/-- Helper for Exercise 21: a tube map around a `C¹` branch has the expected tangent and
transverse derivative columns at the base point. -/
lemma exercise21_radial_tube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
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
  · -- At `p.2 = 0`, the transverse derivative contributes only the normal vector itself.
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

/-- Helper for Exercise 21: rescaling the second `Plane` coordinate by a nonzero real factor is
the linear equivalence used to normalize the tangent/normal frame in the strip charts. -/
noncomputable def exercise21_plane_second_rescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
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

/-- Helper for Exercise 21: quarter-turning a circular tangent in plane coordinates produces the
radial direction scaled by the negated angular-speed factor. -/
lemma exercise21_circleMap_rot90_tangent_eq_scaled_radial
    {c θ : ℝ} :
    rot90
      (Complex.equivRealProd
        ((((c : ℂ) * Complex.I) * Complex.exp (θ * Complex.I)))) =
      (-c) • Complex.equivRealProd (Complex.exp (θ * Complex.I)) := by
  -- Compute both real coordinates directly after rewriting the quarter-turn in `Plane`.
  ext <;>
    simp [rot90, Complex.equivRealProd, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Helper for Exercise 21: once a radial tube has the correct horizontal-axis formula, side test,
and normalized tangent/normal frame, the inverse function theorem packages it into a local
boundary-straightening chart. -/
lemma exercise21_radialBoundaryStripChartExists
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
  -- Route correction: the owner-facing geometry is already encoded in `hstrip_side`, so the
  -- remaining work is the inverse-function packaging of the radial tube itself.
  let Ψ : Plane → ℂ := fun p ↦ γ p.1 + p.2 • n p.1
  let Φ : Plane → Plane := fun p ↦ Complex.equivRealProd (Ψ p)
  obtain ⟨hΨcont, hΨderiv⟩ :=
    exercise21_radial_tube_hasFDerivAt
      (γ := γ) (n := n) (t₀ := t₀) (v := tangent) hγCont hγDeriv hnCont
  have hΦcont : ContDiffAt ℝ 1 Φ (t₀, 0) := by
    -- Converting the complex tube to `Plane` coordinates preserves the `C¹` regularity.
    simpa [Φ] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_contDiffAt_iff).2 hΨcont
  let v : Plane := Complex.equivRealProd tangent
  let radial : Plane := Complex.equivRealProd (n t₀)
  obtain ⟨e₀, he₀⟩ := rot90_frame_equiv_of_ne_zero v hv
  let e : Plane ≃L[ℝ] Plane := (exercise21_plane_second_rescale c hc).trans e₀
  have hderiv_map :
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] Plane).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight tangent +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- The tube derivative columns are exactly the tangent and radial vectors in `Plane`.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    simp [ContinuousLinearMap.comp_apply, v, radial, ContinuousLinearMap.smulRight_apply]
  have hΦderiv :
      HasFDerivAt Φ
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial)
        (t₀, 0) := by
    -- The real-plane tube keeps the same tangent and radial columns after `equivRealProd`.
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
  · -- The centered strip contains `(t₀, 0)` because `t₀` sits between its two endpoints.
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
  · -- Restricting the inverse-function chart preserves the `C¹` regularity on the smaller
    -- source.
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

/-- Helper for Exercise 21: the upper slit-lip side test can be read directly in `Plane`
coordinates, so later chart proofs can use the transverse coordinate `p.2` without repackaging
back to separate `(ρ, s)` variables. -/
lemma exercise21_upper_lip_plane_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - ρ₀| < η → |p.2| < η →
      let z := circleMap 0 p.1 (Real.pi - Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  rcases exercise21_upper_lip_side_of_annulus hε hεr hρ₀ with ⟨η, hη, hside⟩
  refine ⟨η, hη, ?_⟩
  intro p hpρ hp2
  simpa using hside hpρ hp2

/-- Helper for Exercise 21: the lower slit-lip side test likewise packages cleanly in `Plane`
coordinates, which is the form needed by the later strip-chart boundary fields. -/
lemma exercise21_lower_lip_plane_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - ρ₀| < η → |p.2| < η →
      let z := circleMap 0 p.1 (-Real.pi + Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  rcases exercise21_lower_lip_side_of_annulus hε hεr hρ₀ with ⟨η, hη, hside⟩
  refine ⟨η, hη, ?_⟩
  intro p hpρ hp2
  simpa using hside hpρ hp2

/-- Helper for Exercise 21: composing the upper-lip side test with the affine branch parameter
`t ↦ lineMap r ε (8 t)` packages the annulus-side information directly in the strip-chart
coordinates `(t, s)`. -/
lemma exercise21_upper_lip_chart_side_of_annulus
    {r ε t₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let z := circleMap 0 (AffineMap.lineMap r ε (8 * p.1))
          (Real.pi - Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  let ρ₀ : ℝ := AffineMap.lineMap r ε (8 * t₀)
  have hparam₀ : 8 * t₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht₀.1, ht₀.2]
  have hρ₀ : ρ₀ ∈ Set.Ioo ε r := by
    have hseg : ρ₀ ∈ openSegment ℝ r ε := by
      simpa [ρ₀] using lineMap_mem_openSegment (𝕜 := ℝ) r ε hparam₀
    have hre : (r : ℝ) ≠ ε := by
      linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ₀, min_eq_right (le_of_lt hεr), max_eq_left (le_of_lt hεr)] using hseg
  rcases exercise21_upper_lip_plane_side_of_annulus hε hεr hρ₀ with ⟨η₀, hη₀, hside⟩
  let η : ℝ := min η₀ (η₀ / (8 * (r - ε)))
  have hscale : 0 < 8 * (r - ε) := by
    nlinarith
  refine ⟨η, lt_min hη₀ (div_pos hη₀ hscale), ?_⟩
  intro p hp ht
  have hp₂ : |p.2| < η₀ := by
    exact lt_of_lt_of_le ht (min_le_left _ _)
  have hp₁ : |AffineMap.lineMap r ε (8 * p.1) - ρ₀| < η₀ := by
    have hp₁' : |p.1 - t₀| < η₀ / (8 * (r - ε)) := by
      exact lt_of_lt_of_le hp (min_le_right _ _)
    have hlin :
        AffineMap.lineMap r ε (8 * p.1) - ρ₀ = (8 * (p.1 - t₀)) * (ε - r) := by
      dsimp [ρ₀]
      simp [AffineMap.lineMap_apply_module]
      ring
    calc
      |AffineMap.lineMap r ε (8 * p.1) - ρ₀|
          = |8 * (p.1 - t₀)| * |ε - r| := by
              rw [hlin, abs_mul]
      _ = (8 * |p.1 - t₀|) * (r - ε) := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ (8 : ℝ) by norm_num),
              abs_of_neg (by linarith : ε - r < 0)]
            ring
      _ = (8 * (r - ε)) * |p.1 - t₀| := by
            ring
      _ < (8 * (r - ε)) * (η₀ / (8 * (r - ε))) := by
            gcongr
      _ = η₀ := by
            have hne : r - ε ≠ 0 := by linarith
            field_simp [hscale.ne', hne]
  simpa [ρ₀] using
    (hside (p := (AffineMap.lineMap r ε (8 * p.1), p.2)) hp₁ hp₂)

/-- Helper for Exercise 21: composing the reflected lower-lip side test with the affine branch
parameter `t ↦ lineMap ε r (4 t - 1)` packages the annulus-side information in the actual lower
strip-chart coordinates `(t, s)`. -/
lemma exercise21_lower_lip_chart_side_of_annulus
    {r ε t₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (ht₀ : t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let z := circleMap 0 (AffineMap.lineMap ε r (4 * p.1 - 1))
          (-Real.pi + Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
  let ρ₀ : ℝ := AffineMap.lineMap ε r (4 * t₀ - 1)
  have hparam₀ : 4 * t₀ - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht₀.1, ht₀.2]
  have hρ₀ : ρ₀ ∈ Set.Ioo ε r := by
    have hseg : ρ₀ ∈ openSegment ℝ ε r := by
      simpa [ρ₀] using lineMap_mem_openSegment (𝕜 := ℝ) ε r hparam₀
    have hre : (ε : ℝ) ≠ r := by
      linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ₀, min_eq_left (le_of_lt hεr), max_eq_right (le_of_lt hεr)] using hseg
  rcases exercise21_lower_lip_plane_side_of_annulus hε hεr hρ₀ with ⟨η₀, hη₀, hside⟩
  let η : ℝ := min η₀ (η₀ / (4 * (r - ε)))
  have hscale : 0 < 4 * (r - ε) := by
    nlinarith
  refine ⟨η, lt_min hη₀ (div_pos hη₀ hscale), ?_⟩
  intro p hp ht
  have hp₂ : |p.2| < η₀ := by
    exact lt_of_lt_of_le ht (min_le_left _ _)
  have hp₁ : |AffineMap.lineMap ε r (4 * p.1 - 1) - ρ₀| < η₀ := by
    have hp₁' : |p.1 - t₀| < η₀ / (4 * (r - ε)) := by
      exact lt_of_lt_of_le hp (min_le_right _ _)
    have hlin :
        AffineMap.lineMap ε r (4 * p.1 - 1) - ρ₀ = (4 * (p.1 - t₀)) * (r - ε) := by
      dsimp [ρ₀]
      simp [AffineMap.lineMap_apply_module]
      ring
    calc
      |AffineMap.lineMap ε r (4 * p.1 - 1) - ρ₀|
          = |4 * (p.1 - t₀)| * |r - ε| := by
              rw [hlin, abs_mul]
      _ = (4 * |p.1 - t₀|) * (r - ε) := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num),
              abs_of_nonneg (show 0 ≤ r - ε by linarith)]
      _ = (4 * (r - ε)) * |p.1 - t₀| := by
            ring
      _ < (4 * (r - ε)) * (η₀ / (4 * (r - ε))) := by
            gcongr
      _ = η₀ := by
            have hne : r - ε ≠ 0 := by linarith
            field_simp [hscale.ne', hne]
  simpa [ρ₀] using
    (hside (p := (AffineMap.lineMap ε r (4 * p.1 - 1), p.2)) hp₁ hp₂)

/-- Helper for Exercise 21: rotating plane coordinates by `θ` corresponds to multiplication by
`exp (θ i)` after identifying `Plane` with `ℂ`. This keeps the lip charts affine while still
presenting their image in the complex model. -/
private noncomputable def exercise21PlaneRotation (θ : ℝ) : Plane ≃ᴬ[ℝ] Plane :=
  let c : ℂˣ := Units.mk0 (Complex.exp (θ * Complex.I)) (Complex.exp_ne_zero _)
  (((Complex.equivRealProdCLM.symm.trans (ContinuousLinearEquiv.smulLeft c)).trans
      Complex.equivRealProdCLM)).toContinuousAffineEquiv

/-- Helper for Exercise 21: reflecting the second plane coordinate is the affine involution that
switches the rotated `+π/2` normal to the upper-lip `-π/2` normal. -/
private noncomputable def exercise21PlaneFlipSecond : Plane ≃ᴬ[ℝ] Plane :=
  let m : ℝˣ := ⟨-1, -1, by ring, by ring⟩
  (ContinuousAffineEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv)

/-- Helper for Exercise 21: the upper-lip boundary chart is the affine strip whose first
coordinate parametrizes the radial segment and whose reflected second coordinate points into the
slit annulus. -/
private noncomputable def exercise21UpperLipChart (r ε : ℝ) (hεr : ε < r) :
    Plane ≃ᴬ[ℝ] Plane :=
  let m : ℝˣ := ⟨8 * (ε - r), (8 * (ε - r))⁻¹, by
      have hne : ε - r ≠ 0 := by linarith
      field_simp [hne], by
      have hne : ε - r ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ r)
  ((ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)).trans exercise21PlaneFlipSecond).trans
    (exercise21PlaneRotation (Real.pi - Real.arctan (ε / r)))

/-- Helper for Exercise 21: the lower-lip boundary chart uses the direct `+π/2` normal, so no
reflection is needed before the rotation to the lower slit angle. -/
private noncomputable def exercise21LowerLipChart (r ε : ℝ) (hεr : ε < r) :
    Plane ≃ᴬ[ℝ] Plane :=
  let m : ℝˣ := ⟨4 * (r - ε), (4 * (r - ε))⁻¹, by
      have hne : r - ε ≠ 0 := by linarith
      field_simp [hne], by
      have hne : r - ε ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (ε - (r - ε)))
  (ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)).trans
    (exercise21PlaneRotation (-Real.pi + Real.arctan (ε / r)))

/-- Helper for Exercise 21: after applying the affine rotation, the complex representative of a
plane point is just `(x + y i) exp (θ i)`. This is the base computation behind both slit-lip
chart formulas. -/
private lemma exercise21PlaneRotation_apply
    (θ : ℝ) (p : Plane) :
    Complex.equivRealProdCLM.symm (exercise21PlaneRotation θ p) =
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * Complex.exp (θ * Complex.I) := by
  -- Convert back to `Plane` and compute the rotated real and imaginary parts coordinatewise.
  apply Complex.equivRealProdCLM.injective
  ext <;> simp [exercise21PlaneRotation] <;> ring

/-- Helper for Exercise 21: the upper-lip affine chart evaluates to the fixed-angle radial point
plus the inward `-π/2` normal displacement. -/
private lemma exercise21UpperLipChart_apply
    (r ε : ℝ) (hεr : ε < r) (p : Plane) :
    Complex.equivRealProdCLM.symm (exercise21UpperLipChart r ε hεr p) =
      circleMap 0 (AffineMap.lineMap r ε (8 * p.1))
        (Real.pi - Real.arctan (ε / r)) +
      (p.2 : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2) := by
  -- First rewrite the rotated reflected strip point as the simple complex product formula.
  let m : ℝˣ := ⟨8 * (ε - r), (8 * (ε - r))⁻¹, by
      have hne : ε - r ≠ 0 := by linarith
      field_simp [hne], by
      have hne : ε - r ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ r)
  have hex_apply (x : ℝ) : ex x = 8 * (ε - r) * x + r := by
    change (ContinuousAffineEquiv.constVAdd ℝ ℝ r) ((ContinuousLinearEquiv.unitsEquivAut ℝ m) x) =
      8 * (ε - r) * x + r
    rw [ContinuousLinearEquiv.unitsEquivAut_apply]
    change r + x * (8 * (ε - r)) = 8 * (ε - r) * x + r
    ring
  have hbase :
      Complex.equivRealProdCLM.symm (exercise21UpperLipChart r ε hεr p) =
        ((((AffineMap.lineMap r ε (8 * p.1)) : ℂ) - (p.2 : ℂ) * Complex.I) *
          Complex.exp ((Real.pi - Real.arctan (ε / r)) * Complex.I)) := by
    change Complex.equivRealProdCLM.symm
        (exercise21PlaneRotation (Real.pi - Real.arctan (ε / r))
          (exercise21PlaneFlipSecond ((ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)) p))) = _
    rw [exercise21PlaneRotation_apply]
    simp [exercise21PlaneFlipSecond, ex, hex_apply, AffineMap.lineMap_apply]
    ring
  rw [hbase]
  -- Then split the complex product back into the boundary point and the inward normal term.
  rw [circleMap, zero_add, circleMap, zero_add]
  rw [show ((((Real.pi - Real.arctan (ε / r)) - Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      (Real.pi - Real.arctan (ε / r)) * Complex.I - (Real.pi / 2 : ℂ) * Complex.I by
        simp [sub_eq_add_neg, add_mul]]
  rw [Complex.exp_sub]
  simp
  ring

/-- Helper for Exercise 21: the lower-lip affine chart evaluates to the reflected radial point
plus the inward `+π/2` normal displacement. -/
private lemma exercise21LowerLipChart_apply
    (r ε : ℝ) (hεr : ε < r) (p : Plane) :
    Complex.equivRealProdCLM.symm (exercise21LowerLipChart r ε hεr p) =
      circleMap 0 (AffineMap.lineMap ε r (4 * p.1 - 1))
        (-Real.pi + Real.arctan (ε / r)) +
      (p.2 : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2) := by
  -- The lower chart uses the same rotation computation without the second-coordinate reflection.
  let m : ℝˣ := ⟨4 * (r - ε), (4 * (r - ε))⁻¹, by
      have hne : r - ε ≠ 0 := by linarith
      field_simp [hne], by
      have hne : r - ε ≠ 0 := by linarith
      field_simp [hne]⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (ε - (r - ε)))
  have hex_apply (x : ℝ) : ex x = 4 * (r - ε) * x + (ε - (r - ε)) := by
    change
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (ε - (r - ε)))
          ((ContinuousLinearEquiv.unitsEquivAut ℝ m) x) =
        4 * (r - ε) * x + (ε - (r - ε))
    rw [ContinuousLinearEquiv.unitsEquivAut_apply]
    change (ε - (r - ε)) + x * (4 * (r - ε)) = 4 * (r - ε) * x + (ε - (r - ε))
    ring
  have hbase :
      Complex.equivRealProdCLM.symm (exercise21LowerLipChart r ε hεr p) =
        ((((AffineMap.lineMap ε r (4 * p.1 - 1)) : ℂ) + (p.2 : ℂ) * Complex.I) *
          Complex.exp ((-Real.pi + Real.arctan (ε / r)) * Complex.I)) := by
    change Complex.equivRealProdCLM.symm
        (exercise21PlaneRotation (-Real.pi + Real.arctan (ε / r))
          ((ex.prodCongr (ContinuousAffineEquiv.refl ℝ ℝ)) p)) = _
    rw [exercise21PlaneRotation_apply]
    simp [ex, hex_apply, AffineMap.lineMap_apply]
    ring
  rw [hbase]
  rw [circleMap, zero_add, circleMap, zero_add]
  rw [show ((((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      (-Real.pi + Real.arctan (ε / r)) * Complex.I + (Real.pi / 2 : ℂ) * Complex.I by
        simp [add_mul]]
  rw [Complex.exp_add]
  simp
  ring

/-- Helper for Exercise 21: an interior point on the upper slit lip admits an explicit affine
boundary-straightening chart whose positive transverse side enters the slit annulus. -/
lemma exercise21_upper_lip_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the owner-side interior upgrade is now isolated in the strengthened
  -- upper-lip side lemma, so the remaining work is the standard affine strip packaging.
  let e : Plane ≃ᴬ[ℝ] Plane := exercise21UpperLipChart r ε hεr
  let eps_t₀ : ℝ := min (t₀ - 0) (1 / 8 - t₀) / 2
  have hεt₀_pos : 0 < eps_t₀ := by
    dsimp [eps_t₀]
    have hleft : 0 < t₀ - 0 := by simpa using ht₀.1
    have hright : 0 < 1 / 8 - t₀ := sub_pos.mpr ht₀.2
    have hmin : 0 < min (t₀ - 0) (1 / 8 - t₀) := lt_min hleft hright
    linarith
  have hstrip₀ :
      Set.Ioo (t₀ - eps_t₀) (t₀ + eps_t₀) ⊆ Set.Ioo (0 : ℝ) (1 / 8 : ℝ) := by
    intro t ht
    have hleft : 0 < t₀ - 0 := by simpa using ht₀.1
    have hright : 0 < 1 / 8 - t₀ := sub_pos.mpr ht₀.2
    have hmin_left : min (t₀ - 0) (1 / 8 - t₀) / 2 < t₀ - 0 := by
      have hmin_le : min (t₀ - 0) (1 / 8 - t₀) ≤ t₀ - 0 := min_le_left _ _
      linarith
    have hmin_right : min (t₀ - 0) (1 / 8 - t₀) / 2 < 1 / 8 - t₀ := by
      have hmin_le : min (t₀ - 0) (1 / 8 - t₀) ≤ 1 / 8 - t₀ := min_le_right _ _
      linarith
    constructor
    · have h0 : 0 < t₀ - eps_t₀ := by
        dsimp [eps_t₀]
        linarith
      exact lt_trans h0 ht.1
    · have h18 : t₀ + eps_t₀ < 1 / 8 := by
        dsimp [eps_t₀]
        linarith
      exact lt_trans ht.2 h18
  rcases exercise21_upper_lip_chart_side_of_annulus hε hεr ht₀ with ⟨η, hη, hside⟩
  let eps_t : ℝ := min eps_t₀ η
  have hεt_pos : 0 < eps_t := by
    exact lt_min hεt₀_pos hη
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
  refine affineBoundaryStripChartExists e hεt_pos hη hstrip_param ?_ ?_
  · intro t ht
    have htBranch : t ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ) := hstrip_param_branch ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
    -- On the horizontal axis, the affine strip chart recovers the upper-lip branch exactly.
    apply Complex.equivRealProdCLM.symm.injective
    calc
      Complex.equivRealProdCLM.symm (e (t, 0)) =
          circleMap 0 (AffineMap.lineMap r ε (8 * t))
            (Real.pi - Real.arctan (ε / r)) +
            ((0 : ℝ) : ℂ) *
              circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2) := by
                simpa [e] using exercise21UpperLipChart_apply r ε hεr (t, 0)
      _ = circleMap 0 (AffineMap.lineMap r ε (8 * t))
            (Real.pi - Real.arctan (ε / r)) := by simp
      _ = Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t) := by
            symm
            exact exercise21Delta_realCurve_symm_eq_on_upper_lip r ε htIcc
  · intro t u ht hu
    have htAbs : |t - t₀| < eps_t := by
      have htLower : -eps_t < t - t₀ := by
        linarith [ht.1]
      have htUpper : t - t₀ < eps_t := by
        linarith [ht.2]
      exact abs_lt.mpr ⟨htLower, htUpper⟩
    have htAbsη : |t - t₀| < η := lt_of_lt_of_le htAbs (min_le_right _ _)
    have huLower : -η < u := by
      linarith [hu.1]
    have huUpper : u < η := by
      linarith [hu.2]
    have huAbs : |u| < η := abs_lt.mpr ⟨huLower, huUpper⟩
    have hside' := hside (p := (t, u)) htAbsη huAbs
    constructor
    · intro hu_neg
      -- Negative strip height points outward, so they stay outside the slit annulus.
      rw [show Complex.equivRealProdCLM.symm (e (t, u)) =
          circleMap 0 (AffineMap.lineMap r ε (8 * t))
            (Real.pi - Real.arctan (ε / r)) +
            ((u : ℝ) : ℂ) *
              circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2) by
          simpa [e] using exercise21UpperLipChart_apply r ε hεr (t, u)]
      exact hside'.1 hu_neg
    · intro hu_pos
      -- Positive strip height moves into the owner interior by the strengthened side lemma.
      rw [show Complex.equivRealProdCLM.symm (e (t, u)) =
          circleMap 0 (AffineMap.lineMap r ε (8 * t))
            (Real.pi - Real.arctan (ε / r)) +
            ((u : ℝ) : ℂ) *
              circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2) by
          simpa [e] using exercise21UpperLipChart_apply r ε hεr (t, u)]
      exact hside'.2 hu_pos

/-- Helper for Exercise 21: an interior point on the lower slit lip admits the reflected affine
boundary-straightening chart whose positive transverse side again enters the slit annulus. -/
lemma exercise21_lower_lip_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: as on the upper lip, the lower branch is now a direct affine strip chart
  -- application because the positive side already lands in the owner interior.
  let e : Plane ≃ᴬ[ℝ] Plane := exercise21LowerLipChart r ε hεr
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
    have hleft : 0 < t₀ - 1 / 4 := sub_pos.mpr ht₀.1
    have hright : 0 < 1 / 2 - t₀ := sub_pos.mpr ht₀.2
    have hmin_left : min (t₀ - 1 / 4) (1 / 2 - t₀) / 2 < t₀ - 1 / 4 := by
      have hmin_le : min (t₀ - 1 / 4) (1 / 2 - t₀) ≤ t₀ - 1 / 4 := min_le_left _ _
      linarith
    have hmin_right : min (t₀ - 1 / 4) (1 / 2 - t₀) / 2 < 1 / 2 - t₀ := by
      have hmin_le : min (t₀ - 1 / 4) (1 / 2 - t₀) ≤ 1 / 2 - t₀ := min_le_right _ _
      linarith
    constructor
    · have h14 : 1 / 4 < t₀ - eps_t₀ := by
        dsimp [eps_t₀]
        linarith
      exact lt_trans h14 ht.1
    · have h12 : t₀ + eps_t₀ < 1 / 2 := by
        dsimp [eps_t₀]
        linarith
      exact lt_trans ht.2 h12
  rcases exercise21_lower_lip_chart_side_of_annulus hε hεr ht₀ with ⟨η, hη, hside⟩
  let eps_t : ℝ := min eps_t₀ η
  have hεt_pos : 0 < eps_t := by
    exact lt_min hεt₀_pos hη
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
  refine affineBoundaryStripChartExists e hεt_pos hη hstrip_param ?_ ?_
  · intro t ht
    have htBranch : t ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) := hstrip_param_branch ht
    have htIcc : t ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
    -- On the horizontal axis, the lower-lip chart reproduces the reflected slit branch.
    apply Complex.equivRealProdCLM.symm.injective
    calc
      Complex.equivRealProdCLM.symm (e (t, 0)) =
          circleMap 0 (AffineMap.lineMap ε r (4 * t - 1))
            (-Real.pi + Real.arctan (ε / r)) +
            ((0 : ℝ) : ℂ) *
              circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2) := by
                simpa [e] using exercise21LowerLipChart_apply r ε hεr (t, 0)
      _ = circleMap 0 (AffineMap.lineMap ε r (4 * t - 1))
            (-Real.pi + Real.arctan (ε / r)) := by simp
      _ = Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t) := by
            symm
            exact exercise21Delta_realCurve_symm_eq_on_lower_lip r ε htIcc
  · intro t u ht hu
    have htAbs : |t - t₀| < eps_t := by
      have htLower : -eps_t < t - t₀ := by
        linarith [ht.1]
      have htUpper : t - t₀ < eps_t := by
        linarith [ht.2]
      exact abs_lt.mpr ⟨htLower, htUpper⟩
    have htAbsη : |t - t₀| < η := lt_of_lt_of_le htAbs (min_le_right _ _)
    have huLower : -η < u := by
      linarith [hu.1]
    have huUpper : u < η := by
      linarith [hu.2]
    have huAbs : |u| < η := abs_lt.mpr ⟨huLower, huUpper⟩
    have hside' := hside (p := (t, u)) htAbsη huAbs
    constructor
    · intro hu_neg
      -- Negative strip height points into the removed wedge side, so it stays outside the owner.
      rw [show Complex.equivRealProdCLM.symm (e (t, u)) =
          circleMap 0 (AffineMap.lineMap ε r (4 * t - 1))
            (-Real.pi + Real.arctan (ε / r)) +
            ((u : ℝ) : ℂ) *
              circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2) by
          simpa [e] using exercise21LowerLipChart_apply r ε hεr (t, u)]
      exact hside'.1 hu_neg
    · intro hu_pos
      -- Positive strip height enters the lower side of the slit-annulus interior.
      rw [show Complex.equivRealProdCLM.symm (e (t, u)) =
          circleMap 0 (AffineMap.lineMap ε r (4 * t - 1))
            (-Real.pi + Real.arctan (ε / r)) +
            ((u : ℝ) : ℂ) *
              circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2) by
          simpa [e] using exercise21LowerLipChart_apply r ε hεr (t, u)]
      exact hside'.2 hu_pos

/-- Helper for Exercise 21: once a regular parameter lies on one of the two slit lips, the
boundary-straightening problem is reduced to the explicit affine strip chart aligned with that
lip. -/
lemma exercise21_ray_branch_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hbranch :
      t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨ t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2))
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  let _ := hdiff
  let _ := hderiv
  rcases hbranch with htupper | htlower
  · exact exercise21_upper_lip_exists_boundary_chart r ε hε hεr htupper
  · exact exercise21_lower_lip_exists_boundary_chart r ε hε hεr htlower

/-- Helper for Exercise 21: once a regular parameter lies on one of the two circular branches, the
boundary-straightening problem is reduced to the explicit radial strip chart for that circle. -/
lemma exercise21_circle_branch_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hbranch :
      t₀ ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨ t₀ ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ))
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the owner-facing interior bridge and the two branchwise side lemmas are now
  -- closed, so the only remaining work is the inverse-function-theorem packaging of those local
  -- radial strip models into `IsBoundaryStraighteningAt` charts for the inner and outer arcs.
  let _ := hdiff
  let _ := hderiv
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
    rcases exercise21_inner_arc_chart_side_of_annulus hε hεr htinner with ⟨η, hη, hside⟩
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
    let θ : ℝ → ℝ := fun t ↦
      AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (8 * t - 1)
    let γ : ℝ → ℂ := fun t ↦ circleMap 0 ε (θ t)
    let n : ℝ → ℂ := fun t ↦ Complex.exp (θ t * Complex.I)
    let c : ℝ := 16 * (Real.pi - Real.arctan (ε / r)) * ε
    let tangent : ℂ :=
      (8 * ((-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r)))) •
        (circleMap 0 ε (θ t₀) * Complex.I)
    have hθCont : ContDiffAt ℝ 1 θ t₀ := by
      -- The inner-arc angle is an affine function of the contour parameter.
      have hθ :
          ContDiff ℝ 1
            (fun t : ℝ ↦
              (Real.pi - Real.arctan (ε / r)) +
                (8 * t - 1) *
                  ((-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r)))) := by
        fun_prop
      simpa [θ, AffineMap.lineMap_apply_module, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hθ.contDiffAt
    have hγCont : ContDiffAt ℝ 1 γ t₀ := by
      -- The circular branch is smooth after composing `circleMap` with the affine angle.
      simpa [γ] using (contDiff_circleMap 0 ε).contDiffAt.comp t₀ hθCont
    have hnCont : ContDiffAt ℝ 1 n t₀ := by
      -- The outward radial unit field varies smoothly along the open inner arc.
      have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
        simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
      have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
        simpa [one_mul] using hθComplex.mul contDiffAt_const
      simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner)
    have hθDeriv :
        HasDerivAt θ
          (8 * ((-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r)))) t₀ := by
      -- Differentiate the affine angle interpolation before applying `circleMap`.
      simpa [θ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := Real.pi - Real.arctan (ε / r))
          (b := -Real.pi + Real.arctan (ε / r))
          (x := (8 : ℝ) * t₀ - 1)).comp t₀
          (((hasDerivAt_id t₀).const_mul 8).sub_const 1)
    have hγDeriv : HasDerivAt γ tangent t₀ := by
      -- The clockwise inner arc differentiates to the explicit tangent used by the frame lemma.
      convert (hasDerivAt_circleMap 0 ε (θ t₀)).scomp t₀ hθDeriv using 1
    have htangent_formula :
        tangent = (((-c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) := by
      -- Rewrite the derivative in the explicit exponential form used by the frame normalization.
      let κ : ℝ :=
        8 * ((-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r))) * ε
      have hk : κ = -c := by
        dsimp [κ, c]
        ring
      calc
        tangent = (((κ : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
                simp [tangent, κ, circleMap, zero_add]
                ring
        _ = (((-c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) := by
              rw [hk]
    have hv : Complex.equivRealProd tangent ≠ 0 := by
      -- The inner circular tangent is nonzero because both the scale and the exponential factor
      -- are nonzero.
      intro hv0
      have htangent : tangent = 0 := Complex.equivRealProd.injective hv0
      rw [htangent_formula] at htangent
      have hcpos : 0 < c := by
        have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
        nlinarith [hε, Real.pi_pos, hθlt]
      have hc' : (((c : ℝ) : ℂ) : ℂ) ≠ 0 := by
        exact_mod_cast hcpos.ne'
      have hmul :
          (((-c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) = 0 := by
        simpa using htangent
      exact Complex.exp_ne_zero (θ t₀ * Complex.I) <|
        (mul_eq_zero.mp hmul).resolve_left <| by
          exact mul_ne_zero (by simpa using hc') Complex.I_ne_zero
    have hrot :
        rot90 (Complex.equivRealProd tangent) = c • Complex.equivRealProd (n t₀) := by
      -- Quarter-turning the tangent points in the outward radial direction on the inner circle.
      rw [htangent_formula]
      simpa [n, c] using
        (exercise21_circleMap_rot90_tangent_eq_scaled_radial (c := -c) (θ := θ t₀))
    have hc : c ≠ 0 := by
      have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
      have hcpos : 0 < c := by
        nlinarith [hε, Real.pi_pos, hθlt]
      exact hcpos.ne'
    refine exercise21_radialBoundaryStripChartExists
      (K := exercise21NegativeWedgeAnnulus r ε)
      (curve := ((exercise21Delta r ε).toClosedPath.realCurve))
      (γ := γ) (n := n) (t₀ := t₀) (eps_t := eps_t) (eps_u := η) (c := c)
      (tangent := tangent) ht₀ hεt_pos hη hstrip_param
      hγCont hnCont hγDeriv hv hrot hc ?_ ?_
    · intro t ht
      have htBranch : t ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ) := hstrip_param_branch ht
      have htIcc : t ∈ Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
      -- On the horizontal axis, the radial chart recovers the inner circular branch exactly.
      apply Complex.equivRealProdCLM.symm.injective
      calc
        Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t) =
            circleMap 0 ε (θ t) := by
              simpa [γ, θ] using exercise21Delta_realCurve_symm_eq_on_inner_arc r ε htIcc
        _ = Complex.equivRealProdCLM.symm (Complex.equivRealProd (γ t)) := by
              rw [Complex.equivRealProdCLM_symm_apply]
              exact (Complex.re_add_im (γ t)).symm
    · intro p hp₁ hp₂
      -- The branch-local side lemma already states the exact owner test for this radial tube.
      simpa [γ, n, θ, exercise21_inner_arc_add_real_mul_radial_eq_circleMap_radius_add] using
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
    rcases exercise21_outer_arc_chart_side_of_annulus hε hεr htouter with ⟨η, hη, hside⟩
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
    let θ : ℝ → ℝ := fun t ↦
      AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (2 * t - 1)
    let γ : ℝ → ℂ := fun t ↦ circleMap 0 r (θ t)
    let n : ℝ → ℂ := fun t ↦ -Complex.exp (θ t * Complex.I)
    let c : ℝ := 4 * (Real.pi - Real.arctan (ε / r)) * r
    let tangent : ℂ :=
      (2 * ((Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)))) •
        (circleMap 0 r (θ t₀) * Complex.I)
    have hθCont : ContDiffAt ℝ 1 θ t₀ := by
      -- The outer-arc angle is again affine in the contour parameter.
      have hθ :
          ContDiff ℝ 1
            (fun t : ℝ ↦
              (-Real.pi + Real.arctan (ε / r)) +
                (2 * t - 1) *
                  ((Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)))) := by
        fun_prop
      simpa [θ, AffineMap.lineMap_apply_module, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hθ.contDiffAt
    have hγCont : ContDiffAt ℝ 1 γ t₀ := by
      -- The outer circular branch is smooth after composing `circleMap` with that affine angle.
      simpa [γ] using (contDiff_circleMap 0 r).contDiffAt.comp t₀ hθCont
    have hnCont : ContDiffAt ℝ 1 n t₀ := by
      -- The inward radial unit field also varies smoothly along the open outer arc.
      have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
        simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
      have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
        simpa [one_mul] using hθComplex.mul contDiffAt_const
      simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner).neg
    have hθDeriv :
        HasDerivAt θ
          (2 * ((Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)))) t₀ := by
      -- Differentiate the affine angle interpolation before differentiating the outer circle.
      simpa [θ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := -Real.pi + Real.arctan (ε / r))
          (b := Real.pi - Real.arctan (ε / r))
          (x := (2 : ℝ) * t₀ - 1)).comp t₀
          (((hasDerivAt_id t₀).const_mul 2).sub_const 1)
    have hγDeriv : HasDerivAt γ tangent t₀ := by
      -- The outer arc differentiates to the explicit tangent used in the frame normalization.
      convert (hasDerivAt_circleMap 0 r (θ t₀)).scomp t₀ hθDeriv using 1
    have htangent_formula :
        tangent = ((((c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
      -- Rewrite the derivative in the explicit exponential form used by the frame normalization.
      let κ : ℝ :=
        2 * ((Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r))) * r
      have hk : κ = c := by
        dsimp [κ, c]
        ring
      calc
        tangent = (((κ : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
                simp [tangent, κ, circleMap, zero_add]
                ring
        _ = ((((c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I)) := by
              rw [hk]
    have hv : Complex.equivRealProd tangent ≠ 0 := by
      -- The outer circular tangent is nonzero for the same reason as the inner one.
      intro hv0
      have htangent : tangent = 0 := Complex.equivRealProd.injective hv0
      rw [htangent_formula] at htangent
      have hcpos : 0 < c := by
        have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
        nlinarith [hε, hεr, Real.pi_pos, hθlt]
      have hc' : (((c : ℝ) : ℂ) : ℂ) ≠ 0 := by
        exact_mod_cast hcpos.ne'
      have hmul :
          (((c : ℝ) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) = 0 := by
        simpa using htangent
      exact Complex.exp_ne_zero (θ t₀ * Complex.I) <|
        (mul_eq_zero.mp hmul).resolve_left <| by
          exact mul_ne_zero (by simpa using hc') Complex.I_ne_zero
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
                (exercise21_circleMap_rot90_tangent_eq_scaled_radial (c := c) (θ := θ t₀))
        _ = c • Complex.equivRealProd (n t₀) := by
              let w : Plane := Complex.equivRealProd (Complex.exp (θ t₀ * Complex.I))
              have hw : (-c) • w = c • (-w) := by
                simp [w]
              simpa [w, n] using hw
    have hc : c ≠ 0 := by
      have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
      have hcpos : 0 < c := by
        nlinarith [hε, hεr, Real.pi_pos, hθlt]
      exact hcpos.ne'
    refine exercise21_radialBoundaryStripChartExists
      (K := exercise21NegativeWedgeAnnulus r ε)
      (curve := ((exercise21Delta r ε).toClosedPath.realCurve))
      (γ := γ) (n := n) (t₀ := t₀) (eps_t := eps_t) (eps_u := η) (c := c)
      (tangent := tangent) ht₀ hεt_pos hη hstrip_param
      hγCont hnCont hγDeriv hv hrot hc ?_ ?_
    · intro t ht
      have htBranch : t ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := hstrip_param_branch ht
      have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) (1 : ℝ) := ⟨htBranch.1.le, htBranch.2.le⟩
      -- On the horizontal axis, the radial chart recovers the outer circular branch exactly.
      apply Complex.equivRealProdCLM.symm.injective
      calc
        Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t) =
            circleMap 0 r (θ t) := by
              simpa [γ, θ] using exercise21Delta_realCurve_symm_eq_on_outer_arc r ε htIcc
        _ = Complex.equivRealProdCLM.symm (Complex.equivRealProd (γ t)) := by
              rw [Complex.equivRealProdCLM_symm_apply]
              exact (Complex.re_add_im (γ t)).symm
    · intro p hp₁ hp₂
      -- The outer-arc side lemma already matches the radial tube after rewriting the radius.
      let α : ℝ := AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (2 * p.1 - 1)
      have hside' :
          (p.2 < 0 →
            circleMap 0 (r - p.2) α ∉ exercise21NegativeWedgeAnnulus r ε) ∧
          (0 < p.2 →
            circleMap 0 (r - p.2) α ∈ interior (exercise21NegativeWedgeAnnulus r ε)) := by
        simpa [α] using hside (p := p) (lt_of_lt_of_le hp₁ (min_le_right _ _)) hp₂
      have hrewrite :
          circleMap 0 r α + (p.2 : ℂ) * (-Complex.exp (α * Complex.I)) =
            circleMap 0 (r - p.2) α := by
        simpa [α] using
          exercise21_outer_arc_add_real_mul_inward_eq_circleMap_radius_sub r α p.2
      dsimp [γ, n, θ]
      simpa only [α, smul_eq_mul, hrewrite] using hside'

/-- Helper for Exercise 21: every regular interior parameter of the keyhole contour admits a local
boundary straightening chart for the slit annulus it bounds. -/
theorem exercise21Delta_exists_boundary_straightening_at_regular_point
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  rcases exercise21Delta_regular_parameter_mem_open_branch r ε hε hεr ht₀ hdiff with
    htupper | htinner | htlower | htouter
  · -- The upper slit lip uses the affine strip chart for the ray branches.
    exact exercise21_ray_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inl htupper) hdiff hderiv
  · -- The inner circular branch uses the radial chart package.
    exact exercise21_circle_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inl htinner) hdiff hderiv
  · -- The lower slit lip reuses the same affine strip chart with the lower-branch data.
    exact exercise21_ray_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inr htlower) hdiff hderiv
  · -- The outer circular branch reuses the radial chart package for the surviving outer arc.
    exact exercise21_circle_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inr htouter) hdiff hderiv

/-- Helper for Exercise 21: the keyhole contour should be the oriented boundary of the explicit
slit annulus. -/
theorem exercise21Delta_isOrientedBoundaryOf_negative_wedge_annulus
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    IsOrientedBoundaryOf (exercise21NegativeWedgeAnnulus r ε)
      (fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise21Delta r ε).toClosedPath
  change IsOrientedBoundaryOf (exercise21NegativeWedgeAnnulus r ε) Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The slit annulus is already packaged as a compact set.
    simpa using isCompact_exercise21NegativeWedgeAnnulus r ε
  · rintro ⟨⟩
    simpa [Γ, Path.toClosedPath] using exercise21Delta_isPiecewiseDifferentiable r ε
  · rintro ⟨⟩ s t hst
    exact exercise21Delta_simple_eq_or_endpoints r ε hε hεr hst
  · intro i j hij
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i : Unit, Set.range ((Γ i).toPath)) = Set.range (exercise21Delta r ε) := by
      simpa [Γ] using exercise21Delta_singleton_iUnion_range r ε
    simpa [exercise21NegativeWedgeAnnulus_frontier_eq_range r ε hε hεr] using hboundary
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    exact exercise21Delta_exists_boundary_straightening_at_regular_point
      r ε hε hεr ht₀ hdiff hderiv

/-- Helper for Exercise 21: the explicit keyhole contour bounds a compact slit-annulus region that
contains the three poles together with small residue circles around them. -/
theorem exercise21Delta_orientedBoundary_residue_data
    (a r ε : ℝ) (hε : 0 < ε) (hεa : ε < a) (har : a < r) (hε1 : ε < 1) (h1r : 1 < r) :
    ∃ K : Set ℂ, ∃ ρ₁ ρ₂ ρ₃ : ℝ,
      IsOrientedBoundaryOf K (fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) ∧
      K ⊆ Complex.slitPlane ∧
      0 < ρ₁ ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆
          Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₂ ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
          Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₃ ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
          Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ) := by
  let K : Set ℂ := exercise21NegativeWedgeAnnulus r ε
  obtain ⟨ρ₁, ρ₂, ρ₃, hK_subset, hρ₁, hK₁, hD₁, hρ₂, hK₂, hD₂, hρ₃, hK₃, hD₃⟩ :=
    exercise21_negative_wedge_annulus_pole_ball_data a r ε hε hεa har hε1 h1r
  refine ⟨K, ρ₁, ρ₂, ρ₃, ?_, hK_subset, hρ₁, hK₁, hD₁, hρ₂, hK₂, hD₂, hρ₃, hK₃, hD₃⟩
  exact exercise21Delta_isOrientedBoundaryOf_negative_wedge_annulus r ε hε (lt_trans hεa har)


/-- Exercise 21 (1): if `0 < ε < a < r` and `ε < 1 < r`, so the keyhole contour `δ(r, ε)`
encloses the poles at `z = 1` and `z = ± a i`, then the integral of
`z ↦ 1 / (((z^2 + a^2) log z))` equals the sum of those residues, using the principal branch of
`Complex.log`. -/
theorem contourIntegral_exercise21_delta
    (a r ε : ℝ) (hε : 0 < ε) (hεa : ε < a) (har : a < r) (hε1 : ε < 1) (h1r : 1 < r) :
    (∫ᶜ z in exercise21Delta r ε,
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) /
      (2 * Real.pi * Complex.I : ℂ) =
        1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
          1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
            1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I))) := by
  have ha : 0 < a := lt_trans hε hεa
  obtain ⟨K, ρ₁, ρ₂, ρ₃, hΓ, hKD, hρ₁, hK₁, hD₁, hρ₂, hK₂, hD₂, hρ₃, hK₃, hD₃⟩ :=
    exercise21Delta_orientedBoundary_residue_data a r ε hε hεa har hε1 h1r
  have hhol :
      DifferentiableOn ℂ
        (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
        (Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) :=
    exercise21_integrand_differentiableOn_slitPlane_off_poles_finset a
  have hres :
      ∀ z ∈ exercise21PoleFinset a,
        IsolatedLocalResidueCircle
          K
          Complex.slitPlane
          (exercise21PoleFinset a)
          (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
          z
          (exercise21Residue a z) :=
    exercise21_isolatedLocalResidueCircle_data
      (K := K) a ha hρ₁ hK₁ hD₁ hρ₂ hK₂ hD₂ hρ₃ hK₃ hD₃
  have hboundary :
      ∑ i : Unit,
        ∫ᶜ z in ((fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) i).toPath,
          (((fun w ↦ ((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) dz) z) =
        (2 * Real.pi * Complex.I : ℂ) *
          Finset.sum (exercise21PoleFinset a) (exercise21Residue a) := by
    exact orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
      (Γ := fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath)
      (K := K) (D := Complex.slitPlane)
      (f := fun w ↦ ((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)
      (s := exercise21PoleFinset a) (residue := exercise21Residue a)
      hΓ hKD Complex.isOpen_slitPlane hhol hres
  have htwo_pi_I_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hboundary' :
      ∫ᶜ z in exercise21Delta r ε,
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
      (2 * Real.pi * Complex.I : ℂ) *
        Finset.sum (exercise21PoleFinset a) (exercise21Residue a) := by
    let γ :
        Path
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 r (Real.pi - Real.arctan (ε / r))) :=
      exercise21Delta r ε
    have htoClosed :
        γ.toClosedPath.toPath =
          γ.cast
            γ.source
            γ.source := by
      cases γ
      rfl
    calc
      ∫ᶜ z in exercise21Delta r ε,
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
        ∫ᶜ z in γ.cast
            γ.source
            γ.source,
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) := by
            simp [γ]
      _ = ∫ᶜ z in γ.toClosedPath.toPath,
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) := by
            rw [htoClosed]
            rfl
      _ = (2 * Real.pi * Complex.I : ℂ) *
          Finset.sum (exercise21PoleFinset a) (exercise21Residue a) := by
            simpa [γ] using hboundary
  calc
    (∫ᶜ z in exercise21Delta r ε,
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) /
        (2 * Real.pi * Complex.I : ℂ) =
      ((2 * Real.pi * Complex.I : ℂ) *
          Finset.sum (exercise21PoleFinset a) (exercise21Residue a)) /
        (2 * Real.pi * Complex.I : ℂ) := by
          rw [hboundary']
    _ = Finset.sum (exercise21PoleFinset a) (exercise21Residue a) := by
          field_simp [htwo_pi_I_ne]
    _ = ((1 + (a : ℂ) ^ 2)⁻¹ +
        -((Complex.log ((a : ℂ) * Complex.I))⁻¹ *
            (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) +
        (Complex.log (-((a : ℂ) * Complex.I)))⁻¹ *
          (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) := by
            rw [exercise21PoleFinset_sum_residue_normalized a ha]
    _ = 1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
          1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
            1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I))) := by
              rw [exercise21_pos_imag_coeff_normalized]
              have hneg :=
                congrArg
                  (fun z : ℂ =>
                    (1 + (a : ℂ) ^ 2)⁻¹ +
                      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) + z)
                  (exercise21_neg_imag_coeff_normalized a).symm
              simpa [sub_eq_add_neg] using hneg

/-- Helper for Exercise 21: after specializing the keyhole to `ε = 1 / R`, the contour integral
is eventually equal to the constant residue value coming from the three enclosed poles. -/
lemma exercise21Delta_invRadius_curveIntegral_tendsto_residue
    (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ ↦
        ∫ᶜ z in exercise21Delta R (1 / R),
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z))
      Filter.atTop
      (nhds
        ((2 * Real.pi * Complex.I : ℂ) *
          (1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
            1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
              1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I)))))) := by
  have htwo_pi_I_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hresidue_eventually_eq :
      (fun R : ℝ ↦
        ∫ᶜ z in exercise21Delta R (1 / R),
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) =ᶠ[Filter.atTop]
        fun _ : ℝ ↦
          (2 * Real.pi * Complex.I : ℂ) *
            (1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
              1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
                1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I)))) := by
    -- Once `R` is large, the contour `δ(R, R⁻¹)` satisfies the residue-theorem side conditions.
    filter_upwards [Filter.eventually_gt_atTop (max 1 (max a (1 / a)))] with R hR
    have h1R : 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
    have hRpos : 0 < R := lt_trans (by norm_num) h1R
    have haR : a < R := by
      exact lt_of_le_of_lt
        (le_trans (le_max_left _ _) (le_max_right _ _)) hR
    have hRa_inv : 1 / a < R := by
      exact lt_of_le_of_lt
        (le_trans (le_max_right a (1 / a)) (le_max_right _ _)) hR
    have hε : 0 < 1 / R := by
      exact one_div_pos.mpr hRpos
    have hεa : 1 / R < a := by
      exact (one_div_lt hRpos ha).2 hRa_inv
    have hε1 : 1 / R < 1 := by
      simpa using (one_div_lt_one_div hRpos zero_lt_one).2 h1R
    have hbase :=
      contourIntegral_exercise21_delta a R (1 / R) hε hεa haR hε1 h1R
    have hcont :
        (∫ᶜ z in exercise21Delta R (1 / R),
            (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) =
          (2 * Real.pi * Complex.I : ℂ) *
            (1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
              1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
                1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I)))) := by
      have hcont' :
          (∫ᶜ z in exercise21Delta R (1 / R),
              (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) =
            (1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
                1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
                  1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I)))) *
              (2 * Real.pi * Complex.I : ℂ) := by
        exact (div_eq_iff htwo_pi_I_ne).1 <| by simpa using hbase
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcont'
    simpa [exercise21_pos_imag_coeff_normalized, exercise21_neg_imag_coeff_normalized,
      sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hcont
  -- The large-`R` contour family is eventually constant, so its limit is that constant.
  exact Filter.Tendsto.congr' hresidue_eventually_eq.symm tendsto_const_nhds

/-- Helper for Exercise 21: any `C¹` path that stays in the slit plane away from the three poles
of the integrand is curve integrable for the scalar form `dz / ((z^2 + a^2) log z)`. -/
lemma exercise21Integrand_curveIntegrable_of_contDiffOn_range_subset
    (a : ℝ) {u v : ℂ} {γ : Path u v}
    (hγdiff : ContDiffOn ℝ 1 γ.extend I)
    (hγrange :
      Set.range γ ⊆ Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) :
    CurveIntegrable
      ((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
      γ := by
  have hscalar_cont :
      ContinuousOn
        (fun z : ℂ ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)
        (Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) :=
    (exercise21_integrand_differentiableOn_slitPlane_off_poles_finset a).continuousOn
  have hform_cont :
      ContinuousOn
        ((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
        (Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) := by
    -- Turn continuity of the scalar coefficient into continuity of the associated scalar `1`-form.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ))
              (Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ))).prodMk hscalar_cont)
  -- The curve integrability theorem now applies directly on the pole-free slit-plane range.
  exact hform_cont.curveIntegrable_of_contDiffOn hγdiff fun t ↦ hγrange ⟨t, rfl⟩

/-- Helper for Exercise 21: a radial slit-lip segment is curve integrable once its image is known
to stay in the slit plane away from the three poles. -/
lemma exercise21RadialLip_curveIntegrable
    (a ρ₀ ρ₁ φ : ℝ)
    (hRange :
      Set.range (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) ⊆
        Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) :
    CurveIntegrable
      ((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
      (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) := by
  have hsegment_diff :
      ContDiffOn ℝ 1
        (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)).extend I := by
    have hbase :
        ContDiff ℝ 1
          (fun t : ℝ ↦
            (1 - t) • circleMap 0 ρ₀ φ + t • circleMap 0 ρ₁ φ) := by
      fun_prop
    -- On the unit interval, the segment extension is literally the affine line map.
    refine hbase.contDiffOn.congr ?_
    intro t ht
    simpa [AffineMap.lineMap_apply_module] using
      Path.eqOn_extend_segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ) ht
  -- Reuse the generic pole-free integrability interface instead of rebuilding continuity locally.
  exact exercise21Integrand_curveIntegrable_of_contDiffOn_range_subset
    a hsegment_diff hRange

/-- Helper for Exercise 21: a circular branch parameterized by a mapped angle segment is curve
integrable once its image is known to stay in the slit plane away from the three poles. -/
lemma exercise21MappedCircleArc_curveIntegrable
    (a ρ α β : ℝ)
    (hRange :
      Set.range (((Path.segment α β).map (continuous_circleMap 0 ρ))) ⊆
        Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) :
    CurveIntegrable
      ((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
      (((Path.segment α β).map (continuous_circleMap 0 ρ))) := by
  have hbase :
      ContDiff ℝ 1
        (fun t : ℝ ↦ circleMap 0 ρ (((1 - t) * α) + t * β)) := by
    exact (contDiff_circleMap 0 ρ).comp (by fun_prop)
  have hcircle_diff :
      ContDiffOn ℝ 1
        (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) I := by
    -- The mapped arc is the smooth `circleMap` of the affine angle interpolation.
    refine hbase.contDiffOn.congr ?_
    intro t ht
    rw [Path.extend_apply _ ht, Path.map_coe]
    simp [Function.comp_apply, Path.segment_apply, AffineMap.lineMap_apply_module, mul_comm,
      add_comm]
  -- Again, the generic pole-free path lemma closes the curve-integrability obligation.
  exact exercise21Integrand_curveIntegrable_of_contDiffOn_range_subset
    a hcircle_diff hRange

/-- Helper for Exercise 21: once `ε = 1 / R` is fixed with `1 / R < a < R`, the keyhole contour
integral splits into the four explicit textbook branch integrals. This isolates the remaining work
to the analytic normalization of the two slit lips and the vanishing of the two circle terms. -/
lemma exercise21Delta_invRadius_curveIntegral_eq_pieceSum
    (a R : ℝ) (ha : 0 < a) (h1R : 1 < R) (hRa : 1 / R < a) (haR : a < R) :
    ∫ᶜ z in exercise21Delta R (1 / R),
      (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
      let θ := Real.arctan ((1 / R) / R)
      let upper : Path (circleMap 0 R (Real.pi - θ)) (circleMap 0 (1 / R) (Real.pi - θ)) :=
        Path.segment (circleMap 0 R (Real.pi - θ)) (circleMap 0 (1 / R) (Real.pi - θ))
      let inner : Path (circleMap 0 (1 / R) (Real.pi - θ)) (circleMap 0 (1 / R) (-Real.pi + θ)) :=
        (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R))
      let lower : Path (circleMap 0 (1 / R) (-Real.pi + θ)) (circleMap 0 R (-Real.pi + θ)) :=
        Path.segment (circleMap 0 (1 / R) (-Real.pi + θ)) (circleMap 0 R (-Real.pi + θ))
      let outer : Path (circleMap 0 R (-Real.pi + θ)) (circleMap 0 R (Real.pi - θ)) :=
        (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R)
      (∫ᶜ z in upper, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in inner, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in lower, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in outer, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) := by
  let θ : ℝ := Real.arctan ((1 / R) / R)
  let ω : ℂ → ℂ →L[ℂ] ℂ :=
    ((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz)
  let upper : Path (circleMap 0 R (Real.pi - θ)) (circleMap 0 (1 / R) (Real.pi - θ)) :=
    Path.segment (circleMap 0 R (Real.pi - θ)) (circleMap 0 (1 / R) (Real.pi - θ))
  let inner : Path (circleMap 0 (1 / R) (Real.pi - θ)) (circleMap 0 (1 / R) (-Real.pi + θ)) :=
    (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R))
  let lower : Path (circleMap 0 (1 / R) (-Real.pi + θ)) (circleMap 0 R (-Real.pi + θ)) :=
    Path.segment (circleMap 0 (1 / R) (-Real.pi + θ)) (circleMap 0 R (-Real.pi + θ))
  let outer : Path (circleMap 0 R (-Real.pi + θ)) (circleMap 0 R (Real.pi - θ)) :=
    (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R)
  have hRpos : 0 < R := lt_trans (by norm_num) h1R
  have hε : 0 < 1 / R := one_div_pos.mpr hRpos
  have hεr : 1 / R < R := by
    nlinarith [h1R, hRpos]
  have hε1 : 1 / R < 1 := by
    simpa using (one_div_lt_one_div hRpos zero_lt_one).2 h1R
  have hθbounds : 0 < θ ∧ θ < Real.pi / 2 := by
    simpa [θ] using exercise21_keyhole_angle_bounds (r := R) (ε := 1 / R) hε hεr
  have hupperAngle : Real.pi - θ ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · nlinarith [hθbounds.2, Real.pi_pos]
    · nlinarith [hθbounds.1]
  have hlowerAngle : -Real.pi + θ ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · nlinarith [hθbounds.1]
    · nlinarith [hθbounds.2, Real.pi_pos]
  have hupperRange :
      Set.range upper ⊆ Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · -- The upper lip stays on the surviving branch of the slit plane.
      simpa [upper, θ] using
        exercise21_radial_segment_range_subset_slitPlane_of_angle hRpos hε hupperAngle hz
    · rcases hz with ⟨t, rfl⟩
      let ρ : ℝ := AffineMap.lineMap R (1 / R) (t : ℝ)
      have hρpos : 0 < ρ := by
        dsimp [ρ]
        rw [AffineMap.lineMap_apply_module]
        have ht0 : 0 ≤ (t : ℝ) := t.2.1
        have ht1 : (t : ℝ) ≤ 1 := t.2.2
        simpa [smul_eq_mul] using
          show 0 < (1 - (t : ℝ)) * R + (t : ℝ) * (1 / R) by
            nlinarith [hRpos, hε, ht0, ht1]
      have hre : (circleMap 0 ρ (Real.pi - θ)).re < 0 := by
        simpa [θ, ρ] using
          exercise21Delta_upper_lip_re_neg (r := R) (ε := 1 / R) (ρ := ρ) hρpos
      have hzform : upper t = circleMap 0 ρ (Real.pi - θ) := by
        simp [upper, ρ, Path.segment_apply, exercise21_lineMap_circleMap_same_angle]
      rw [hzform]
      rw [exercise21PoleFinset_coe]
      simp only [exercise21PoleSet, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hEq
        have : ((1 : ℂ).re) < 0 := by simpa [hEq] using hre
        norm_num at this
      constructor
      · intro hEq
        rw [hEq] at hre
        simp at hre
      · intro hEq
        rw [hEq] at hre
        simp at hre
  have hinnerRange :
      Set.range inner ⊆ Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · -- The inner circular arc keeps all arguments strictly between `-π` and `π`.
      simpa [inner, θ] using
        exercise21_circle_arc_range_subset_slitPlane_of_endpoints hε hupperAngle hlowerAngle hz
    · rcases hz with ⟨t, rfl⟩
      have hzform :
          inner t =
            circleMap 0 (1 / R)
              (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (t : ℝ)) := by
        simp [inner, Path.map_coe, Function.comp_apply, Path.segment_apply]
      rw [hzform]
      rw [exercise21PoleFinset_coe]
      simp only [exercise21PoleSet, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hEq
        have : ‖circleMap 0 (1 / R)
            (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (t : ℝ))‖ = ‖(1 : ℂ)‖ := by
          simpa [hEq] using congrArg norm hEq
        have habs : (|R|⁻¹ : ℝ) = 1 := by
          simpa [norm_circleMap_zero, abs_of_pos hε, Complex.norm_natCast] using this
        have : (1 / R : ℝ) = 1 := by
          simpa [abs_of_pos hRpos] using habs
        linarith
      constructor
      · intro hEq
        have : ‖circleMap 0 (1 / R)
            (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (t : ℝ))‖ =
            ‖(a : ℂ) * Complex.I‖ := by
          simpa [hEq] using congrArg norm hEq
        have habs : (|R|⁻¹ : ℝ) = a := by
          simpa [norm_circleMap_zero, abs_of_pos hε, Complex.norm_mul, Complex.norm_real,
            Complex.norm_I, abs_of_pos ha] using this
        have : (1 / R : ℝ) = a := by
          simpa [abs_of_pos hRpos] using habs
        linarith
      · intro hEq
        have : ‖circleMap 0 (1 / R)
            (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (t : ℝ))‖ =
            ‖-((a : ℂ) * Complex.I)‖ := by
          simpa [hEq] using congrArg norm hEq
        have habs : (|R|⁻¹ : ℝ) = a := by
          simpa [norm_circleMap_zero, abs_of_pos hε, Complex.norm_mul, Complex.norm_real,
            Complex.norm_I, abs_of_pos ha] using this
        have : (1 / R : ℝ) = a := by
          simpa [abs_of_pos hRpos] using habs
        linarith
  have hlowerRange :
      Set.range lower ⊆ Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · -- The lower lip is the companion radial branch on the opposite side of the slit.
      simpa [lower, θ] using
        exercise21_radial_segment_range_subset_slitPlane_of_angle hε hRpos hlowerAngle hz
    · rcases hz with ⟨t, rfl⟩
      let ρ : ℝ := AffineMap.lineMap (1 / R) R (t : ℝ)
      have hρpos : 0 < ρ := by
        dsimp [ρ]
        rw [AffineMap.lineMap_apply_module]
        have ht0 : 0 ≤ (t : ℝ) := t.2.1
        have ht1 : (t : ℝ) ≤ 1 := t.2.2
        simpa [smul_eq_mul] using
          show 0 < (1 - (t : ℝ)) * (1 / R) + (t : ℝ) * R by
            nlinarith [hRpos, hε, ht0, ht1]
      have hre : (circleMap 0 ρ (-Real.pi + θ)).re < 0 := by
        simpa [θ, ρ] using
          exercise21Delta_lower_lip_re_neg (r := R) (ε := 1 / R) (ρ := ρ) hρpos
      have hzform : lower t = circleMap 0 ρ (-Real.pi + θ) := by
        simp [lower, ρ, Path.segment_apply, exercise21_lineMap_circleMap_same_angle]
      rw [hzform]
      rw [exercise21PoleFinset_coe]
      simp only [exercise21PoleSet, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hEq
        have : ((1 : ℂ).re) < 0 := by simpa [hEq] using hre
        norm_num at this
      constructor
      · intro hEq
        rw [hEq] at hre
        simp at hre
      · intro hEq
        rw [hEq] at hre
        simp at hre
  have houterRange :
      Set.range outer ⊆ Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · -- The outer arc also avoids the deleted negative-axis angle throughout its sweep.
      simpa [outer, θ] using
        exercise21_circle_arc_range_subset_slitPlane_of_endpoints hRpos hlowerAngle hupperAngle hz
    · rcases hz with ⟨t, rfl⟩
      have hzform :
          outer t =
            circleMap 0 R
              (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (t : ℝ)) := by
        simp [outer, Path.map_coe, Function.comp_apply, Path.segment_apply]
      rw [hzform]
      rw [exercise21PoleFinset_coe]
      simp only [exercise21PoleSet, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hEq
        have : ‖circleMap 0 R
            (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (t : ℝ))‖ = ‖(1 : ℂ)‖ := by
          simp [hEq]
        have : (R : ℝ) = 1 := by
          simpa [norm_circleMap_zero, abs_of_pos hRpos, Complex.norm_natCast] using this
        linarith
      constructor
      · intro hEq
        have : ‖circleMap 0 R
            (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (t : ℝ))‖ =
            ‖(a : ℂ) * Complex.I‖ := by
          simp [hEq]
        have : (R : ℝ) = a := by
          simpa [norm_circleMap_zero, abs_of_pos hRpos, Complex.norm_mul, Complex.norm_real,
            Complex.norm_I, abs_of_pos ha] using this
        linarith
      · intro hEq
        have : ‖circleMap 0 R
            (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (t : ℝ))‖ =
            ‖-((a : ℂ) * Complex.I)‖ := by
          simp [hEq]
        have : (R : ℝ) = a := by
          simpa [norm_circleMap_zero, abs_of_pos hRpos, Complex.norm_mul, Complex.norm_real,
            Complex.norm_I, abs_of_pos ha] using this
        linarith
  have hupperInt : CurveIntegrable ω upper := by
    -- The upper slit lip is a `C¹` radial segment staying in the pole-free slit plane.
    simpa [ω, upper] using exercise21RadialLip_curveIntegrable a R (1 / R) (Real.pi - θ) hupperRange
  have hinnerInt : CurveIntegrable ω inner := by
    -- The inner circular branch is the mapped angle segment at radius `1 / R`.
    simpa [ω, inner] using
      exercise21MappedCircleArc_curveIntegrable a (1 / R) (Real.pi - θ) (-Real.pi + θ) hinnerRange
  have hlowerInt : CurveIntegrable ω lower := by
    -- The lower slit lip is the same radial argument with reversed orientation.
    simpa [ω, lower] using
      exercise21RadialLip_curveIntegrable a (1 / R) R (-Real.pi + θ) hlowerRange
  have houterInt : CurveIntegrable ω outer := by
    -- The outer circular branch is the surviving large circle arc.
    simpa [ω, outer] using
      exercise21MappedCircleArc_curveIntegrable a R (-Real.pi + θ) (Real.pi - θ) houterRange
  have hupperInnerInt : CurveIntegrable ω (upper.trans inner) := hupperInt.trans hinnerInt
  have hthreeInt : CurveIntegrable ω ((upper.trans inner).trans lower) :=
    hupperInnerInt.trans hlowerInt
  -- Route correction: `exercise21Delta` is now rewritten only through the canonical four-path
  -- concatenation, and the branchwise integrability obligations are discharged by the new API.
  rw [exercise21Delta_def]
  calc
    ∫ᶜ z in ((upper.trans inner).trans lower).trans outer, ω z =
        ∫ᶜ z in (upper.trans inner).trans lower, ω z + ∫ᶜ z in outer, ω z := by
          rw [curveIntegral_trans hthreeInt houterInt]
    _ = (∫ᶜ z in upper.trans inner, ω z + ∫ᶜ z in lower, ω z) + ∫ᶜ z in outer, ω z := by
          rw [curveIntegral_trans hupperInnerInt hlowerInt]
    _ = ((∫ᶜ z in upper, ω z + ∫ᶜ z in inner, ω z) + ∫ᶜ z in lower, ω z) +
          ∫ᶜ z in outer, ω z := by
          rw [curveIntegral_trans hupperInt hinnerInt]
    _ = (∫ᶜ z in upper, ω z) + (∫ᶜ z in inner, ω z) + (∫ᶜ z in lower, ω z) +
          (∫ᶜ z in outer, ω z) := by
          abel

/-- Helper for Cartan section12 0034_Exercise_21: the upper and lower slit-branch interval
integrands are integrable on the common truncation window `(1 / R)..R`. -/
lemma exercise21LipPairBranchIntervalIntegrable
    (a R : ℝ) (h1R : 1 < R) :
    IntervalIntegrable
        (fun x : ℝ ↦
          Complex.exp ((Real.pi - Real.arctan ((1 / R) / R)) * Complex.I) /
            ((((x : ℂ) * Complex.exp ((Real.pi - Real.arctan ((1 / R) / R)) * Complex.I)) ^ 2 +
                (a : ℂ) ^ 2) *
              (Real.log x + (Real.pi - Real.arctan ((1 / R) / R)) * Complex.I)))
        volume (1 / R) R ∧
      IntervalIntegrable
        (fun x : ℝ ↦
          Complex.exp (-(Real.pi - Real.arctan ((1 / R) / R)) * Complex.I) /
            ((((x : ℂ) * Complex.exp (-(Real.pi - Real.arctan ((1 / R) / R)) * Complex.I)) ^ 2 +
                (a : ℂ) ^ 2) *
              (Real.log x - (Real.pi - Real.arctan ((1 / R) / R)) * Complex.I)))
        volume (1 / R) R := by
  let α : ℝ := Real.pi - Real.arctan ((1 / R) / R)
  have hRpos : 0 < R := lt_trans (by norm_num) h1R
  have hε : 0 < 1 / R := one_div_pos.mpr hRpos
  have hεR : 1 / R ≤ R := by
    field_simp [hRpos.ne']
    nlinarith
  have hεr : 1 / R < R := by
    field_simp [hRpos.ne']
    nlinarith
  have hθbounds :
      0 < Real.arctan ((1 / R) / R) ∧ Real.arctan ((1 / R) / R) < Real.pi / 2 := by
    simpa using exercise21_keyhole_angle_bounds (r := R) (ε := 1 / R) hε hεr
  have hαpos : 0 < α := by
    -- The principal slit angle stays strictly between `0` and `π`.
    dsimp [α]
    nlinarith [hθbounds.2, Real.pi_pos]
  have hαne : α ≠ 0 := hαpos.ne'
  have hlogCont : ContinuousOn Real.log (Set.Icc (1 / R) R) := by
    -- The truncation window stays inside `(0, ∞)`, so `Real.log` is continuous there.
    refine Real.continuousOn_log.mono ?_
    intro x hx
    exact (lt_of_lt_of_le hε hx.1).ne'
  constructor
  · have hquadCont :
        ContinuousOn
          (fun x : ℝ ↦
            (((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2))
          (Set.Icc (1 / R) R) := by
      exact ((Complex.continuous_ofReal.continuousOn.mul continuousOn_const).pow 2).add
        continuousOn_const
    have hlogComplex :
        ContinuousOn (fun x : ℝ ↦ (Real.log x : ℂ)) (Set.Icc (1 / R) R) := by
      simpa [Function.comp] using Complex.continuous_ofReal.comp_continuousOn hlogCont
    have hlogTermCont :
        ContinuousOn
          (fun x : ℝ ↦ (Real.log x : ℂ) + α * Complex.I)
          (Set.Icc (1 / R) R) := by
      exact hlogComplex.add continuousOn_const
    have hdenCont :
        ContinuousOn
          (fun x : ℝ ↦
            ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x + α * Complex.I)))
          (Set.Icc (1 / R) R) := by
      simpa using hquadCont.mul hlogTermCont
    have hdenNe :
        ∀ x ∈ Set.Icc (1 / R) R,
          ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x + α * Complex.I)) ≠ 0 := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hε hx.1
      have hquadNe :
          (((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) ≠ 0 := by
        intro hzero
        let ai : ℂ := (a : ℂ) * Complex.I
        have hai_sq : ai ^ 2 = -((a : ℂ) ^ 2) := by
          dsimp [ai]
          calc
            (((a : ℂ) * Complex.I) ^ 2) = (a : ℂ) ^ 2 * (Complex.I ^ 2) := by
              ring
            _ = -((a : ℂ) ^ 2) := by
              simp [Complex.I_sq]
        have hfactor :
            ((((x : ℂ) * Complex.exp (α * Complex.I)) - ai) *
                (((x : ℂ) * Complex.exp (α * Complex.I)) + ai)) =
              (((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) := by
          calc
            ((((x : ℂ) * Complex.exp (α * Complex.I)) - ai) *
                (((x : ℂ) * Complex.exp (α * Complex.I)) + ai)) =
              (((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 - ai ^ 2) := by
                ring
            _ = (((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) := by
                rw [hai_sq]
                ring
        rw [← hfactor] at hzero
        rcases mul_eq_zero.mp hzero with hminus | hplus
        · have hre : (circleMap 0 x α).re < 0 := by
            simpa [α] using
              exercise21Delta_upper_lip_re_neg (r := R) (ε := 1 / R) (ρ := x) hxpos
          have hre' : (((x : ℂ) * Complex.exp (α * Complex.I))).re < 0 := by
            simpa [circleMap_zero] using hre
          have hEq : ((x : ℂ) * Complex.exp (α * Complex.I)) = ai := by
            exact sub_eq_zero.mp hminus
          rw [hEq] at hre'
          simp [ai] at hre'
        · have hre : (circleMap 0 x α).re < 0 := by
            simpa [α] using
              exercise21Delta_upper_lip_re_neg (r := R) (ε := 1 / R) (ρ := x) hxpos
          have hre' : (((x : ℂ) * Complex.exp (α * Complex.I))).re < 0 := by
            simpa [circleMap_zero] using hre
          have hEq : ((x : ℂ) * Complex.exp (α * Complex.I)) = -ai := by
            exact eq_neg_iff_add_eq_zero.mpr hplus
          rw [hEq] at hre'
          simp [ai] at hre'
      have hlogNe : (Real.log x + α * Complex.I) ≠ 0 := by
        intro hzero
        have : α = 0 := by
          simpa using congrArg Complex.im hzero
        exact hαne this
      exact mul_ne_zero hquadNe hlogNe
    have hcont :
        ContinuousOn
          (fun x : ℝ ↦
            Complex.exp (α * Complex.I) /
              ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
                (Real.log x + α * Complex.I)))
          (Set.Icc (1 / R) R) := by
      exact continuousOn_const.div hdenCont hdenNe
    -- Closed-interval continuity gives interval integrability of the upper-lip kernel.
    simpa [α] using ContinuousOn.intervalIntegrable_of_Icc hεR hcont
  · have hquadCont :
        ContinuousOn
          (fun x : ℝ ↦
            (((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2))
          (Set.Icc (1 / R) R) := by
      exact ((Complex.continuous_ofReal.continuousOn.mul continuousOn_const).pow 2).add
        continuousOn_const
    have hlogComplex :
        ContinuousOn (fun x : ℝ ↦ (Real.log x : ℂ)) (Set.Icc (1 / R) R) := by
      simpa [Function.comp] using Complex.continuous_ofReal.comp_continuousOn hlogCont
    have hlogTermCont :
        ContinuousOn
          (fun x : ℝ ↦ (Real.log x : ℂ) - α * Complex.I)
          (Set.Icc (1 / R) R) := by
      exact hlogComplex.sub continuousOn_const
    have hdenCont :
        ContinuousOn
          (fun x : ℝ ↦
            ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x - α * Complex.I)))
          (Set.Icc (1 / R) R) := by
      simpa using hquadCont.mul hlogTermCont
    have hdenNe :
        ∀ x ∈ Set.Icc (1 / R) R,
          ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
            (Real.log x - α * Complex.I)) ≠ 0 := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hε hx.1
      have hquadNe :
          (((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) ≠ 0 := by
        intro hzero
        let ai : ℂ := (a : ℂ) * Complex.I
        have hai_sq : ai ^ 2 = -((a : ℂ) ^ 2) := by
          dsimp [ai]
          calc
            (((a : ℂ) * Complex.I) ^ 2) = (a : ℂ) ^ 2 * (Complex.I ^ 2) := by
              ring
            _ = -((a : ℂ) ^ 2) := by
              simp [Complex.I_sq]
        have hfactor :
            ((((x : ℂ) * Complex.exp (-α * Complex.I)) - ai) *
                (((x : ℂ) * Complex.exp (-α * Complex.I)) + ai)) =
              (((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) := by
          calc
            ((((x : ℂ) * Complex.exp (-α * Complex.I)) - ai) *
                (((x : ℂ) * Complex.exp (-α * Complex.I)) + ai)) =
              (((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 - ai ^ 2) := by
                ring
            _ = (((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) := by
                rw [hai_sq]
                ring
        rw [← hfactor] at hzero
        rcases mul_eq_zero.mp hzero with hminus | hplus
        · have hre : (circleMap 0 x (-α)).re < 0 := by
            simpa [α, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              exercise21Delta_lower_lip_re_neg (r := R) (ε := 1 / R) (ρ := x) hxpos
          have hre' : (((x : ℂ) * Complex.exp (-α * Complex.I))).re < 0 := by
            simpa [circleMap_zero] using hre
          have hEq : ((x : ℂ) * Complex.exp (-α * Complex.I)) = ai := by
            exact sub_eq_zero.mp hminus
          rw [hEq] at hre'
          simp [ai] at hre'
        · have hre : (circleMap 0 x (-α)).re < 0 := by
            simpa [α, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              exercise21Delta_lower_lip_re_neg (r := R) (ε := 1 / R) (ρ := x) hxpos
          have hre' : (((x : ℂ) * Complex.exp (-α * Complex.I))).re < 0 := by
            simpa [circleMap_zero] using hre
          have hEq : ((x : ℂ) * Complex.exp (-α * Complex.I)) = -ai := by
            exact eq_neg_iff_add_eq_zero.mpr hplus
          rw [hEq] at hre'
          simp [ai] at hre'
      have hlogNe : (Real.log x - α * Complex.I) ≠ 0 := by
        intro hzero
        have : -α = 0 := by
          simpa using congrArg Complex.im hzero
        exact hαne (neg_eq_zero.mp this)
      exact mul_ne_zero hquadNe hlogNe
    have hcont :
        ContinuousOn
          (fun x : ℝ ↦
            Complex.exp (-α * Complex.I) /
              ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
                (Real.log x - α * Complex.I)))
          (Set.Icc (1 / R) R) := by
      exact continuousOn_const.div hdenCont hdenNe
    -- The same closed-interval argument works for the companion lower-lip kernel.
    simpa [α] using ContinuousOn.intervalIntegrable_of_Icc hεR hcont

/-- Helper for Cartan section12 0034_Exercise_21: the two radial slit-branch integrals collapse to
one interval integral of the paired kernel. -/
lemma exercise21UpperLower_curveIntegral_eq_lipPairInterval
    (a R : ℝ) (h1R : 1 < R) :
    (∫ᶜ z in Path.segment
        (circleMap 0 R (Real.pi - Real.arctan ((1 / R) / R)))
        (circleMap 0 (1 / R) (Real.pi - Real.arctan ((1 / R) / R))),
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
      (∫ᶜ z in Path.segment
          (circleMap 0 (1 / R) (-(Real.pi - Real.arctan ((1 / R) / R))))
          (circleMap 0 R (-(Real.pi - Real.arctan ((1 / R) / R)))),
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) =
      ∫ x in (1 / R)..R,
        exercise21LipPairKernel a (Real.pi - Real.arctan ((1 / R) / R)) x := by
  let α : ℝ := Real.pi - Real.arctan ((1 / R) / R)
  have hRpos : 0 < R := lt_trans (by norm_num) h1R
  have hε : 0 < 1 / R := one_div_pos.mpr hRpos
  have hεR : 1 / R ≤ R := by
    field_simp [hRpos.ne']
    nlinarith
  have hεr : 1 / R < R := by
    field_simp [hRpos.ne']
    nlinarith
  have hθbounds :
      0 < Real.arctan ((1 / R) / R) ∧ Real.arctan ((1 / R) / R) < Real.pi / 2 := by
    simpa using exercise21_keyhole_angle_bounds (r := R) (ε := 1 / R) hε hεr
  have hαmem : α ∈ Set.Ioo (-Real.pi) Real.pi := by
    -- The slit branches stay inside the principal logarithm strip.
    constructor
    · dsimp [α]
      nlinarith [hθbounds.2, Real.pi_pos]
    · dsimp [α]
      nlinarith [hθbounds.1]
  rcases exercise21LipPairBranchIntervalIntegrable a R h1R with ⟨hupperInt, hlowerInt⟩
  have hupper :
      ∫ᶜ z in Path.segment (circleMap 0 R α) (circleMap 0 (1 / R) α),
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
        -∫ x in (1 / R)..R,
          Complex.exp (α * Complex.I) /
            ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x + α * Complex.I)) := by
    simpa [α] using exercise21UpperLip_curveIntegral_eq_intervalIntegral a R α hRpos hαmem
  have hlower :
      ∫ᶜ z in Path.segment (circleMap 0 (1 / R) (-α)) (circleMap 0 R (-α)),
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
        ∫ x in (1 / R)..R,
          Complex.exp (-α * Complex.I) /
            ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x - α * Complex.I)) := by
    simpa [α] using exercise21LowerLip_curveIntegral_eq_intervalIntegral a R α hRpos hαmem
  -- Rewrite each slit lip separately, then use interval linearity to package the paired kernel.
  calc
    (∫ᶜ z in Path.segment (circleMap 0 R α) (circleMap 0 (1 / R) α),
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in Path.segment (circleMap 0 (1 / R) (-α)) (circleMap 0 R (-α)),
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) =
      (∫ x in (1 / R)..R,
          Complex.exp (-α * Complex.I) /
            ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x - α * Complex.I))) -
        ∫ x in (1 / R)..R,
          Complex.exp (α * Complex.I) /
            ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x + α * Complex.I)) := by
            rw [hupper, hlower]
            abel
    _ =
      ∫ x in (1 / R)..R,
        (Complex.exp (-α * Complex.I) /
            ((((x : ℂ) * Complex.exp (-α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x - α * Complex.I)) -
          Complex.exp (α * Complex.I) /
            ((((x : ℂ) * Complex.exp (α * Complex.I)) ^ 2 + (a : ℂ) ^ 2) *
              (Real.log x + α * Complex.I))) := by
            symm
            simpa [α] using intervalIntegral.integral_sub hlowerInt hupperInt
    _ = ∫ x in (1 / R)..R, exercise21LipPairKernel a α x := by
          rfl
    _ = ∫ x in (1 / R)..R,
          exercise21LipPairKernel a (Real.pi - Real.arctan ((1 / R) / R)) x := by
            simp [α]

/-- Helper for Cartan section12 0034_Exercise_21: at the special angle `π`, the paired slit kernel
is exactly `-(2π i)` times the truncated real target kernel. -/
lemma exercise21LipPairKernel_pi_intervalIntegral
    (a R : ℝ) (ha : 0 < a) (hR : 1 < R) :
    ∫ x in (1 / R)..R, exercise21LipPairKernel a Real.pi x =
      (-(2 * Real.pi * Complex.I : ℂ)) *
        (((∫ x in (1 / R)..R, exercise21TargetKernel a x : ℝ) : ℂ)) := by
  let _ := ha
  have hRpos : 0 < R := lt_trans (by norm_num) hR
  have hε : 0 < 1 / R := one_div_pos.mpr hRpos
  have hεR : 1 / R ≤ R := by
    field_simp [hRpos.ne']
    nlinarith
  -- Normalize the `π`-kernel pointwise on the truncation interval and then factor out
  -- the constant `-(2π i)`.
  calc
    ∫ x in (1 / R)..R, exercise21LipPairKernel a Real.pi x =
      ∫ x in (1 / R)..R,
        (-(2 * Real.pi * Complex.I : ℂ)) * (exercise21TargetKernel a x : ℂ) := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          have hx' : x ∈ Set.Icc (1 / R) R := by
            simpa only [Set.uIcc_of_le hεR] using (hx : x ∈ Set.uIcc (1 / R) R)
          have hxpos : 0 < x := lt_of_lt_of_le hε hx'.1
          simpa using exercise21LipPairKernel_pi a x hxpos
    _ = (-(2 * Real.pi * Complex.I : ℂ)) *
          (∫ x in (1 / R)..R, (exercise21TargetKernel a x : ℂ)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = (-(2 * Real.pi * Complex.I : ℂ)) *
          (((∫ x in (1 / R)..R, exercise21TargetKernel a x : ℝ) : ℂ)) := by
            rw [intervalIntegral.integral_ofReal]

/-- Helper for Cartan section12 0034_Exercise_21: after regrouping the four branch integrals of
`exercise21Delta R (1 / R)`, the contour integral splits into lip error, truncated target term,
and circle remainder. -/
lemma exercise21Delta_invRadius_curveIntegral_eq_lipError_add_truncTarget_add_circle
    (a R : ℝ) (ha : 0 < a) (h1R : 1 < R) (hRa : 1 / R < a) (haR : a < R) :
    ∫ᶜ z in exercise21Delta R (1 / R),
      (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
      (∫ x in (1 / R)..R,
        (exercise21LipPairKernel a (Real.pi - Real.arctan ((1 / R) / R)) x -
          exercise21LipPairKernel a Real.pi x)) +
        (-(2 * Real.pi * Complex.I : ℂ)) *
          (((∫ x in (1 / R)..R, exercise21TargetKernel a x : ℝ) : ℂ)) +
        (let θ := Real.arctan ((1 / R) / R)
         let inner :
             Path (circleMap 0 (1 / R) (Real.pi - θ))
               (circleMap 0 (1 / R) (-Real.pi + θ)) :=
           (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R))
         let outer :
             Path (circleMap 0 R (-Real.pi + θ))
               (circleMap 0 R (Real.pi - θ)) :=
           (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R)
         (∫ᶜ z in inner, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
           (∫ᶜ z in outer, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z))) := by
  let θ : ℝ := Real.arctan ((1 / R) / R)
  let α : ℝ := Real.pi - θ
  let upper : Path (circleMap 0 R (Real.pi - θ)) (circleMap 0 (1 / R) (Real.pi - θ)) :=
    Path.segment (circleMap 0 R (Real.pi - θ)) (circleMap 0 (1 / R) (Real.pi - θ))
  let inner : Path (circleMap 0 (1 / R) (Real.pi - θ)) (circleMap 0 (1 / R) (-Real.pi + θ)) :=
    (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R))
  let lower : Path (circleMap 0 (1 / R) (-Real.pi + θ)) (circleMap 0 R (-Real.pi + θ)) :=
    Path.segment (circleMap 0 (1 / R) (-Real.pi + θ)) (circleMap 0 R (-Real.pi + θ))
  let outer : Path (circleMap 0 R (-Real.pi + θ)) (circleMap 0 R (Real.pi - θ)) :=
    (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R)
  let circleRemainder : ℂ :=
    (∫ᶜ z in inner, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
      (∫ᶜ z in outer, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z))
  have hα :
      α = Real.pi - Real.arctan ((1 / R) / R) := by
    simp [α, θ]
  have hRpos : 0 < R := lt_trans (by norm_num) h1R
  have hε : 0 < 1 / R := one_div_pos.mpr hRpos
  have hεR : 1 / R ≤ R := by
    field_simp [hRpos.ne']
    nlinarith
  rcases exercise21LipPairBranchIntervalIntegrable a R h1R with ⟨hupperInt, hlowerInt⟩
  have hpairInt :
      IntervalIntegrable (fun x : ℝ ↦ exercise21LipPairKernel a α x) volume (1 / R) R := by
    -- The paired kernel is the lower slit kernel minus the upper slit kernel.
    have hkernel :
        (fun x : ℝ ↦ exercise21LipPairKernel a α x) =
          (fun x : ℝ ↦
            Complex.exp (-(Real.pi - Real.arctan ((1 / R) / R)) * Complex.I) /
                ((((x : ℂ) * Complex.exp (-(Real.pi - Real.arctan ((1 / R) / R)) * Complex.I)) ^ 2 +
                    (a : ℂ) ^ 2) *
                  (Real.log x - (Real.pi - Real.arctan ((1 / R) / R)) * Complex.I)) -
              Complex.exp ((Real.pi - Real.arctan ((1 / R) / R)) * Complex.I) /
                ((((x : ℂ) * Complex.exp ((Real.pi - Real.arctan ((1 / R) / R)) * Complex.I)) ^ 2 +
                    (a : ℂ) ^ 2) *
                  (Real.log x + (Real.pi - Real.arctan ((1 / R) / R)) * Complex.I))) := by
      funext x
      rw [hα]
      simp [exercise21LipPairKernel]
    rw [hkernel]
    exact hlowerInt.sub hupperInt
  have htargetIcc :
      MeasureTheory.IntegrableOn (exercise21TargetKernel a) (Set.Icc (1 / R) R) volume := by
    refine (exercise21TargetKernel_integrableOnIoi a ha).mono_set ?_
    intro x hx
    exact lt_of_lt_of_le hε hx.1
  have htargetIccComplex :
      MeasureTheory.IntegrableOn (fun x : ℝ ↦ (exercise21TargetKernel a x : ℂ))
        (Set.Icc (1 / R) R) volume := by
    simpa [MeasureTheory.IntegrableOn] using
      (MeasureTheory.Integrable.ofReal htargetIcc.integrable)
  have hpiBaseIcc :
      MeasureTheory.IntegrableOn
        (fun x : ℝ ↦ (-(2 * Real.pi * Complex.I : ℂ)) * (exercise21TargetKernel a x : ℂ))
        (Set.Icc (1 / R) R) volume := by
    simpa [MeasureTheory.IntegrableOn] using
      (MeasureTheory.Integrable.ofReal htargetIcc.integrable).const_mul
        (-(2 * Real.pi * Complex.I : ℂ))
  have hpiBaseInt :
      IntervalIntegrable
        (fun x : ℝ ↦ (-(2 * Real.pi * Complex.I : ℂ)) * (exercise21TargetKernel a x : ℂ))
        volume (1 / R) R := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hεR).2 hpiBaseIcc
  have hpiInt :
      IntervalIntegrable (fun x : ℝ ↦ exercise21LipPairKernel a Real.pi x) volume (1 / R) R := by
    -- On the truncation window, the special-angle kernel is the explicit target kernel multiple.
    refine IntervalIntegrable.congr ?_ hpiBaseInt
    intro x hx
    have hx' : 1 / R < x ∧ x ≤ R := by
      rwa [Set.uIoc_of_le hεR] at hx
    have hxpos : 0 < x := lt_trans hε hx'.1
    symm
    simpa using exercise21LipPairKernel_pi a x hxpos
  have hpair :
      (∫ᶜ z in upper, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in lower, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) =
      ∫ x in (1 / R)..R, exercise21LipPairKernel a α x := by
    -- Route correction: rewrite the two slit branches through the stable paired-kernel helper
    -- instead of crossing the lower-angle spelling inline.
    have hstart :
        circleMap 0 (1 / R) (-(Real.pi - Real.arctan ((1 / R) / R))) =
          circleMap 0 (1 / R) (-Real.pi + θ) := by
      have hang :
          -(Real.pi - Real.arctan ((1 / R) / R)) = -Real.pi + θ := by
        simp [θ, sub_eq_add_neg, add_comm]
      rw [hang]
    have hend :
        circleMap 0 R (-(Real.pi - Real.arctan ((1 / R) / R))) =
          circleMap 0 R (-Real.pi + θ) := by
      have hang :
          -(Real.pi - Real.arctan ((1 / R) / R)) = -Real.pi + θ := by
        simp [θ, sub_eq_add_neg, add_comm]
      rw [hang]
    have hpairRaw := exercise21UpperLower_curveIntegral_eq_lipPairInterval a R h1R
    rw [hstart, hend] at hpairRaw
    rw [hα]
    simpa [θ, upper, lower] using hpairRaw
  have herrorDecomp :
      ∫ x in (1 / R)..R, exercise21LipPairKernel a α x =
        (∫ x in (1 / R)..R,
          (exercise21LipPairKernel a α x - exercise21LipPairKernel a Real.pi x)) +
          ∫ x in (1 / R)..R, exercise21LipPairKernel a Real.pi x := by
    -- Separate the special-angle `π` contribution before inserting the target-kernel identity.
    rw [intervalIntegral.integral_sub hpairInt hpiInt]
    abel
  have hpi :
      ∫ x in (1 / R)..R, exercise21LipPairKernel a Real.pi x =
        (-(2 * Real.pi * Complex.I : ℂ)) *
          (((∫ x in (1 / R)..R, exercise21TargetKernel a x : ℝ) : ℂ)) := by
    simpa using exercise21LipPairKernel_pi_intervalIntegral a R ha h1R
  -- Regroup the four explicit branches into slit-pair plus circle remainder and then split off
  -- the special-angle `π` contribution.
  calc
    ∫ᶜ z in exercise21Delta R (1 / R),
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z) =
      (∫ᶜ z in upper, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in inner, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in lower, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
        (∫ᶜ z in outer, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) := by
          simpa [θ, upper, inner, lower, outer, sub_eq_add_neg] using
            exercise21Delta_invRadius_curveIntegral_eq_pieceSum a R ha h1R hRa haR
    _ =
      ((∫ᶜ z in upper, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
          (∫ᶜ z in lower, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z))) +
        circleRemainder := by
          dsimp [circleRemainder]
          abel
    _ = (∫ x in (1 / R)..R, exercise21LipPairKernel a α x) + circleRemainder := by
          rw [hpair]
    _ =
      ((∫ x in (1 / R)..R,
          (exercise21LipPairKernel a α x - exercise21LipPairKernel a Real.pi x)) +
          ∫ x in (1 / R)..R, exercise21LipPairKernel a Real.pi x) +
        circleRemainder := by
          rw [herrorDecomp]
    _ =
      (∫ x in (1 / R)..R,
        (exercise21LipPairKernel a α x - exercise21LipPairKernel a Real.pi x)) +
        (-(2 * Real.pi * Complex.I : ℂ)) *
          (((∫ x in (1 / R)..R, exercise21TargetKernel a x : ℝ) : ℂ)) +
        circleRemainder := by
          rw [hpi]
    _ = _ := by
          simp [θ, α, circleRemainder, inner, outer]

/-- Cartan section12 0034_Exercise_21: after specializing the keyhole to `ε = 1 / R`,
the contour integral
tends to `-(2π i)` times the improper real integral. -/
lemma exercise21Delta_curveIntegral_tendsto_neg_two_pi_I_integral
    (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ ↦
        ∫ᶜ z in exercise21Delta R (1 / R),
          (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z))
      Filter.atTop
      (nhds
        (-(2 * Real.pi * Complex.I : ℂ) *
          ∫ x in Set.Ioi (0 : ℝ),
            (1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) : ℝ) ∂volume)) := by
  have hlarge :
      ∀ᶠ R : ℝ in Filter.atTop, 1 < R ∧ 1 / R < a ∧ a < R := by
    -- Once `R` dominates `max 1 (max a (1 / a))`, the specialized keyhole has the required
    -- geometric separation from all three poles.
    filter_upwards [Filter.eventually_gt_atTop (max 1 (max a (1 / a)))] with R hR
    have h1R : 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
    have hRpos : 0 < R := lt_trans (by norm_num) h1R
    have hRa_inv : 1 / a < R := lt_of_le_of_lt
      (le_trans (le_max_right a (1 / a)) (le_max_right _ _)) hR
    have hRa : 1 / R < a := (one_div_lt hRpos ha).2 hRa_inv
    have haR : a < R := lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hR
    exact ⟨h1R, hRa, haR⟩
  let contourTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in exercise21Delta R (1 / R),
      (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)
  let lipErrorTerm : ℝ → ℂ := fun R ↦
    ∫ x in (1 / R)..R,
      (exercise21LipPairKernel a (Real.pi - Real.arctan ((1 / R) / R)) x -
        exercise21LipPairKernel a Real.pi x)
  let truncTargetTerm : ℝ → ℂ := fun R ↦
    (-(2 * Real.pi * Complex.I : ℂ)) *
      ((∫ x in (1 / R)..R, exercise21TargetKernel a x : ℝ) : ℂ)
  let circleTerm : ℝ → ℂ := fun R ↦
    let θ := Real.arctan ((1 / R) / R)
    let inner :
        Path (circleMap 0 (1 / R) (Real.pi - θ))
          (circleMap 0 (1 / R) (-Real.pi + θ)) :=
      (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 (1 / R))
    let outer :
        Path (circleMap 0 R (-Real.pi + θ))
          (circleMap 0 R (Real.pi - θ)) :=
      (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 R)
    (∫ᶜ z in inner, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) +
      (∫ᶜ z in outer, (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z))
  have hrewrite :
      contourTerm =ᶠ[Filter.atTop]
        (fun R ↦ lipErrorTerm R + truncTargetTerm R + circleTerm R) := by
    filter_upwards [hlarge] with R hR
    rcases hR with ⟨h1R, hRa, haR⟩
    -- Route correction: invoke the dedicated contour-normalization helper instead of rebuilding
    -- continuity, pole avoidance, and branch regrouping inline.
    simpa [contourTerm, lipErrorTerm, truncTargetTerm, circleTerm, add_assoc] using
      exercise21Delta_invRadius_curveIntegral_eq_lipError_add_truncTarget_add_circle
        a R ha h1R hRa haR
  have hlip :
      Filter.Tendsto lipErrorTerm Filter.atTop (nhds 0) := by
    -- The angle defect on the paired slit kernel is isolated in the dedicated analytic helper.
    simpa [lipErrorTerm] using exercise21LipPair_intervalIntegral_sub_pi_tendsto_zero a ha
  have htargetReal :
      Filter.Tendsto
        (fun R : ℝ ↦ ∫ x in (1 / R)..R, exercise21TargetKernel a x)
        Filter.atTop
        (nhds
          (∫ x in Set.Ioi (0 : ℝ),
            exercise21TargetKernel a x ∂volume)) := by
    -- The real truncation limit is likewise delegated to the dedicated tail-normalization lemma.
    simpa using exercise21TargetKernel_truncatedIntegral_tendsto a ha
  have htargetComplex :
      Filter.Tendsto
        (fun R : ℝ ↦ ((∫ x in (1 / R)..R, exercise21TargetKernel a x : ℝ) : ℂ))
        Filter.atTop
        (nhds
          (((∫ x in Set.Ioi (0 : ℝ),
              exercise21TargetKernel a x ∂volume) : ℝ) : ℂ)) := by
    -- Coerce the real-valued truncation limit into `ℂ` before multiplying by `-(2π i)`.
    exact (Complex.continuous_ofReal.tendsto _).comp htargetReal
  have htarget :
      Filter.Tendsto truncTargetTerm Filter.atTop
        (nhds
          ((-(2 * Real.pi * Complex.I : ℂ)) *
            (((∫ x in Set.Ioi (0 : ℝ),
                exercise21TargetKernel a x ∂volume) : ℝ) : ℂ))) := by
    -- Multiplication by the constant factor `-(2π i)` preserves the target-kernel limit.
    simpa [truncTargetTerm] using Filter.Tendsto.const_mul
      (-(2 * Real.pi * Complex.I : ℂ)) htargetComplex
  have hcircle :
      Filter.Tendsto circleTerm Filter.atTop (nhds 0) := by
    -- The remaining circle contribution is exactly the named analytic remainder term.
    simpa [circleTerm] using exercise21Delta_circleBranchIntegrals_tendsto_zero a ha
  have hsum :
      Filter.Tendsto
        (fun R ↦ lipErrorTerm R + truncTargetTerm R + circleTerm R)
        Filter.atTop
        (nhds
          (0 +
            (-(2 * Real.pi * Complex.I : ℂ)) *
              (((∫ x in Set.Ioi (0 : ℝ),
                  exercise21TargetKernel a x ∂volume) : ℝ) : ℂ) +
            0)) := by
    -- After the contour normalization, the three analytic pieces converge independently.
    simpa [add_assoc] using hlip.add (htarget.add hcircle)
  -- The theorem now follows from the normalized contour decomposition and the three analytic
  -- convergence lemmas above.
  simpa [contourTerm, exercise21TargetKernel, add_assoc] using
    Filter.Tendsto.congr' hrewrite.symm hsum

/-- Closed-form deduction for Cartan section12 0034_Exercise_21: the improper real
integral obtained from the
keyhole-contour computation evaluates to the stated closed form. -/
theorem integral_inv_quadratic_log_sq_add_pi_sq
    (a : ℝ) (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) ∂volume =
      Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) - 1 / (1 + a ^ 2) := by
  let F : ℝ → ℂ := fun R ↦
    ∫ᶜ z in exercise21Delta R (1 / R),
      (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)
  let residueValue : ℂ :=
    1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
        1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I)))
  have htwo_pi_I_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hresidue_tendsto :
      Filter.Tendsto F Filter.atTop (nhds ((2 * Real.pi * Complex.I : ℂ) * residueValue)) := by
    -- Route correction: the residue-side tail is now isolated in its own helper, so the only
    -- remaining work in this theorem is comparing that constant limit with the contour-limit side.
    simpa [F, residueValue] using exercise21Delta_invRadius_curveIntegral_tendsto_residue a ha
  have hcontour_tendsto :
      Filter.Tendsto F Filter.atTop
        (nhds
          (-(2 * Real.pi * Complex.I : ℂ) *
            ∫ x in Set.Ioi (0 : ℝ),
              (1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) : ℝ) ∂volume)) := by
    simpa [F] using exercise21Delta_curveIntegral_tendsto_neg_two_pi_I_integral a ha
  have hlimit_eq :
      (-(2 * Real.pi * Complex.I : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ),
            (1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) : ℝ) ∂volume =
        (2 * Real.pi * Complex.I : ℂ) * residueValue := by
    exact tendsto_nhds_unique hcontour_tendsto hresidue_tendsto
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc_ne : c ≠ 0 := htwo_pi_I_ne
  have hcancel :
      (-(∫ x in Set.Ioi (0 : ℝ),
          (1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) : ℝ) ∂volume) : ℂ) =
        residueValue := by
    have hrewrite : c *
        (-(∫ x in Set.Ioi (0 : ℝ),
            (1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) : ℝ) ∂volume) : ℂ) =
          c * residueValue := by
      simpa [c, mul_assoc, mul_left_comm, mul_comm, neg_mul] using hlimit_eq
    exact mul_left_cancel₀ hc_ne hrewrite
  have hresidue_eval :
      residueValue =
        (1 / (1 + a ^ 2) - Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
    simpa [residueValue] using exercise21_residue_sum_eval a ha
  have hcancel_real :
      -(∫ x in Set.Ioi (0 : ℝ),
          1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) ∂volume) =
        1 / (1 + a ^ 2) - Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) := by
    have hcomplex := hcancel.trans hresidue_eval
    exact Complex.ofReal_inj.mp <| by simpa using hcomplex
  linarith
