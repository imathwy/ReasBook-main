import Mathlib
import DifferentialForms_Cartan_1970.III.section12.CircleSupNorm

-- Semantic recall tool `lean_leansearch` was unavailable in this environment.
-- No local precedent for Hadamard's three circles theorem was found in this repository.

-- Declarations for this item will be appended below by the statement pipeline.

open Metric Set
open Complex.HadamardThreeLines

/-- Exercise 8 (1): Hadamard's three circles theorem for the circle sup norm of a function that is
analytic on a neighborhood of the closed annulus `r₁ ≤ ‖z‖ ≤ r₂`. -/
theorem hadamard_three_circles
    {f : ℂ → ℂ} {r₁ r₂ r : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r₂ \ ball (0 : ℂ) r₁))
    (hr_left : r₁ ≤ r) (hr_right : r ≤ r₂) :
    circleSupNorm f r ≤
      Real.rpow (circleSupNorm f r₁)
        ((Real.log r₂ - Real.log r) / (Real.log r₂ - Real.log r₁)) *
      Real.rpow (circleSupNorm f r₂)
        ((Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁)) := by
  let A : Set ℂ := closedBall (0 : ℂ) r₂ \ ball (0 : ℂ) r₁
  let F : ℂ → ℂ := fun z ↦ f (Complex.exp z)
  let l : ℝ := Real.log r₁
  let u : ℝ := Real.log r₂
  have hr₂ : 0 < r₂ := lt_trans hr₁ hr₁₂
  have hr : 0 < r := lt_of_lt_of_le hr₁ hr_left
  -- Move from the annulus to the logarithmic strip where Hadamard's three-lines theorem applies.
  have hlu : l < u := by
    simp only [l, u]
    exact Real.log_lt_log hr₁ hr₁₂
  have hlog_left : l ≤ Real.log r := by
    simpa [l] using (Real.log_le_log hr₁ hr_left)
  have hlog_right : Real.log r ≤ u := by
    simpa [u] using (Real.log_le_log hr hr_right)
  have hcontA : ContinuousOn f A := hf.continuousOn
  have hsphere_subset_annulus :
      ∀ {ρ : ℝ}, r₁ ≤ ρ → ρ ≤ r₂ → sphere (0 : ℂ) ρ ⊆ A := by
    intro ρ hρ_left hρ_right z hz
    have hz_norm : ‖z‖ = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hz_norm.symm ▸ hρ_right
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      simpa [hz_norm] using not_lt_of_ge hρ_left
  have hmap_closed : MapsTo Complex.exp (verticalClosedStrip l u) A := by
    intro z hz
    rw [verticalClosedStrip, mem_preimage, mem_Icc] at hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_exp]
      calc
        Real.exp z.re ≤ Real.exp u := Real.exp_le_exp.mpr hz.2
        _ = r₂ := by simp [u, Real.exp_log hr₂]
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_exp]
      have : r₁ ≤ Real.exp z.re := by
        calc
          r₁ = Real.exp l := by simp [l, Real.exp_log hr₁]
          _ ≤ Real.exp z.re := Real.exp_le_exp.mpr hz.1
      exact not_lt_of_ge this
  have hExp : AnalyticOnNhd ℂ Complex.exp (verticalClosedStrip l u) := by
    exact analyticOnNhd_cexp.mono (by intro z hz; trivial)
  have hFanalytic : AnalyticOnNhd ℂ F (verticalClosedStrip l u) := by
    simpa [F] using AnalyticOnNhd.comp hf hExp hmap_closed
  have hFdiff : DifferentiableOn ℂ F (verticalClosedStrip l u) := hFanalytic.differentiableOn
  have hclosure_strip : closure (verticalStrip l u) = verticalClosedStrip l u := by
    simp [verticalStrip, verticalClosedStrip, Complex.closure_preimage_re, closure_Ioo hlu.ne]
  have hFdiff_closure : DifferentiableOn ℂ F (closure (verticalStrip l u)) := by
    rw [hclosure_strip]
    exact hFdiff
  have hFdcc : DiffContOnCl ℂ F (verticalStrip l u) := hFdiff_closure.diffContOnCl
  have hcompactA : IsCompact A := by
    simpa [A] using (isCompact_closedBall (0 : ℂ) r₂).diff isOpen_ball
  have hBddA : BddAbove ((norm ∘ f) '' A) := hcompactA.bddAbove_image hcontA.norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp hBddA
  have hBF : BddAbove ((norm ∘ F) '' verticalClosedStrip l u) := by
    refine bddAbove_def.mpr ?_
    refine ⟨C, ?_⟩
    rintro x ⟨z, hz, rfl⟩
    exact hC _ ⟨Complex.exp z, hmap_closed hz, rfl⟩
  have hcont_r₁ : ContinuousOn f (sphere (0 : ℂ) r₁) := by
    exact hcontA.mono <| hsphere_subset_annulus le_rfl hr₁₂.le
  have hcont_r₂ : ContinuousOn f (sphere (0 : ℂ) r₂) := by
    exact hcontA.mono <| hsphere_subset_annulus hr₁₂.le le_rfl
  have hcont_r : ContinuousOn f (sphere (0 : ℂ) r) := by
    exact hcontA.mono <| hsphere_subset_annulus hr_left hr_right
  have hbound_left : ∀ z ∈ Complex.re ⁻¹' ({l} : Set ℝ), ‖F z‖ ≤ circleSupNorm f r₁ := by
    intro z hz
    have hzre : z.re = l := by simpa [mem_preimage] using hz
    have hz_sphere : Complex.exp z ∈ sphere (0 : ℂ) r₁ := by
      simp [sub_zero, Complex.norm_exp, hzre, l, Real.exp_log hr₁]
    simpa [F] using hcont_r₁.norm_le_circleSupNorm hz_sphere
  have hbound_right : ∀ z ∈ Complex.re ⁻¹' ({u} : Set ℝ), ‖F z‖ ≤ circleSupNorm f r₂ := by
    intro z hz
    have hzre : z.re = u := by simpa [mem_preimage] using hz
    have hz_sphere : Complex.exp z ∈ sphere (0 : ℂ) r₂ := by
      simp [sub_zero, Complex.norm_exp, hzre, u, Real.exp_log hr₂]
    simpa [F] using hcont_r₂.norm_le_circleSupNorm hz_sphere
  have hpointwise :
      ∀ z ∈ sphere (0 : ℂ) r,
        ‖f z‖ ≤
          Real.rpow (circleSupNorm f r₁)
            ((Real.log r₂ - Real.log r) / (Real.log r₂ - Real.log r₁)) *
          Real.rpow (circleSupNorm f r₂)
            ((Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁)) := by
    intro z hz
    have hz_norm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    have hz_ne : z ≠ 0 := by
      apply norm_ne_zero_iff.mp
      simpa [hz_norm] using hr.ne'
    -- Use `log z` to place each circle point on the correct vertical line of the strip.
    have hz_strip : Complex.log z ∈ verticalClosedStrip l u := by
      rw [verticalClosedStrip, mem_preimage, Complex.log_re, hz_norm]
      exact ⟨hlog_left, hlog_right⟩
    have hstrip :=
      Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
        (l := l) (u := u) (f := F) (z := Complex.log z)
        (a := circleSupNorm f r₁) (b := circleSupNorm f r₂)
        hlu hz_strip hFdcc hBF hbound_left hbound_right
    have hlog_ne : Real.log r₂ - Real.log r₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlu)
    have hweight :
        1 - (Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁) =
          (Real.log r₂ - Real.log r) / (Real.log r₂ - Real.log r₁) := by
      field_simp [hlog_ne]
      ring
    simpa [F, Complex.exp_log hz_ne, Complex.log_re, hz_norm, l, u, hweight] using hstrip
  -- The pointwise strip estimate on the whole circle upgrades to the circle supremum.
  rw [circleSupNorm]
  refine csSup_le ?_ ?_
  · refine ⟨‖f (r : ℂ)‖, ?_⟩
    refine ⟨(r : ℂ), ?_, rfl⟩
    simp [sub_zero, hr.le]
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact hpointwise z hz

/-- Helper for Exercise 8: the Hadamard exponents on a logarithmic subannulus agree with the
affine interpolation weights. -/
lemma subannulus_hadamard_weights
    {x y a b : ℝ} (hxy : x < y) (hab : a + b = 1) :
    ((y - (a * x + b * y)) / (y - x) = a) ∧
      (((a * x + b * y) - x) / (y - x) = b) := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxy)
  have hnum_left : y - (a * x + b * y) = a * (y - x) := by
    have hb' : b = 1 - a := by
      linarith
    rw [hb']
    ring
  have hnum_right : (a * x + b * y) - x = b * (y - x) := by
    have ha' : a = 1 - b := by
      linarith
    rw [ha']
    ring
  constructor
  · -- Rewrite the first numerator as `a * (y - x)` and cancel the common factor.
    rw [hnum_left]
    field_simp [hne]
  · -- Rewrite the second numerator as `b * (y - x)` and cancel the common factor.
    rw [hnum_right]
    field_simp [hne]

/-- Helper for Exercise 8: taking logarithms converts a positive `rpow`-product bound into an
affine bound on logarithms. -/
lemma log_le_add_of_le_rpow_mul_rpow
    {m A B a b : ℝ} (hm : 0 < m) (hA : 0 < A) (hB : 0 < B)
    (hbound : m ≤ Real.rpow A a * Real.rpow B b) :
    Real.log m ≤ a * Real.log A + b * Real.log B := by
  have hlog : Real.log m ≤ Real.log (Real.rpow A a * Real.rpow B b) :=
    Real.log_le_log hm hbound
  have hmul :
      Real.log (Real.rpow A a * Real.rpow B b) =
        Real.log (Real.rpow A a) + Real.log (Real.rpow B b) := by
    simpa using
      Real.log_mul (x := Real.rpow A a) (y := Real.rpow B b)
        (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hB _).ne'
  have hlogA : Real.log (Real.rpow A a) = a * Real.log A := by
    simpa using Real.log_rpow hA a
  have hlogB : Real.log (Real.rpow B b) = b * Real.log B := by
    simpa using Real.log_rpow hB b
  -- Expand the logarithm of the product and then the logarithm of each `rpow`.
  rw [hmul, hlogA, hlogB] at hlog
  simpa using hlog

/-- Helper for Exercise 8: Hadamard's inequality on the smaller annulus `[exp x, exp y]` yields
the convexity inequality for `log (circleSupNorm f (exp •))` between `x` and `y`. -/
lemma subannulus_log_interpolation
    {f : ℂ → ℂ} {r₁ r₂ x y a b : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r₂ \ ball (0 : ℂ) r₁))
    (hpos : ∀ ⦃r⦄, r ∈ Icc r₁ r₂ → 0 < circleSupNorm f r)
    (hx : x ∈ Icc (Real.log r₁) (Real.log r₂))
    (hy : y ∈ Icc (Real.log r₁) (Real.log r₂))
    (hxy : x < y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.log (circleSupNorm f (Real.exp (a * x + b * y))) ≤
      a * Real.log (circleSupNorm f (Real.exp x)) +
        b * Real.log (circleSupNorm f (Real.exp y)) := by
  have hr₂ : 0 < r₂ := lt_trans hr₁ hr₁₂
  have hx_exp_mem : Real.exp x ∈ Icc r₁ r₂ := by
    constructor
    · -- Convert the lower logarithmic bound for `x` back to a radial bound.
      calc
        r₁ = Real.exp (Real.log r₁) := by rw [Real.exp_log hr₁]
        _ ≤ Real.exp x := Real.exp_le_exp.mpr hx.1
    · -- Convert the upper logarithmic bound for `x` back to a radial bound.
      calc
        Real.exp x ≤ Real.exp (Real.log r₂) := Real.exp_le_exp.mpr hx.2
        _ = r₂ := by rw [Real.exp_log hr₂]
  have hy_exp_mem : Real.exp y ∈ Icc r₁ r₂ := by
    constructor
    · -- Convert the lower logarithmic bound for `y` back to a radial bound.
      calc
        r₁ = Real.exp (Real.log r₁) := by rw [Real.exp_log hr₁]
        _ ≤ Real.exp y := Real.exp_le_exp.mpr hy.1
    · -- Convert the upper logarithmic bound for `y` back to a radial bound.
      calc
        Real.exp y ≤ Real.exp (Real.log r₂) := Real.exp_le_exp.mpr hy.2
        _ = r₂ := by rw [Real.exp_log hr₂]
  have hmid_left_eq : a * x + b * y - x = b * (y - x) := by
    have ha' : a = 1 - b := by
      linarith
    rw [ha']
    ring
  have hmid_right_eq : y - (a * x + b * y) = a * (y - x) := by
    have hb' : b = 1 - a := by
      linarith
    rw [hb']
    ring
  have hmid_left : x ≤ a * x + b * y := by
    have hnonneg : 0 ≤ a * x + b * y - x := by
      rw [hmid_left_eq]
      nlinarith [hb, hxy]
    linarith
  have hmid_right : a * x + b * y ≤ y := by
    have hnonneg : 0 ≤ y - (a * x + b * y) := by
      rw [hmid_right_eq]
      nlinarith [ha, hxy]
    linarith
  have hmid_mem : a * x + b * y ∈ Icc (Real.log r₁) (Real.log r₂) := by
    constructor
    · exact le_trans hx.1 hmid_left
    · exact le_trans hmid_right hy.2
  have hmid_exp_mem : Real.exp (a * x + b * y) ∈ Icc r₁ r₂ := by
    constructor
    · -- The interpolated logarithmic radius stays above `log r₁`.
      calc
        r₁ = Real.exp (Real.log r₁) := by rw [Real.exp_log hr₁]
        _ ≤ Real.exp (a * x + b * y) := Real.exp_le_exp.mpr hmid_mem.1
    · -- The interpolated logarithmic radius stays below `log r₂`.
      calc
        Real.exp (a * x + b * y) ≤ Real.exp (Real.log r₂) := Real.exp_le_exp.mpr hmid_mem.2
        _ = r₂ := by rw [Real.exp_log hr₂]
  have hsubset :
      closedBall (0 : ℂ) (Real.exp y) \ ball (0 : ℂ) (Real.exp x) ⊆
        closedBall (0 : ℂ) r₂ \ ball (0 : ℂ) r₁ := by
    intro z hz
    rcases hz with ⟨hz_closed, hz_ball⟩
    refine ⟨?_, ?_⟩
    · -- The smaller outer circle lies inside the original outer circle.
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz_closed ⊢
      exact le_trans hz_closed hy_exp_mem.2
    · -- The smaller inner disk contains the original inner disk.
      intro hz_r₁
      apply hz_ball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz_r₁ ⊢
      exact lt_of_lt_of_le hz_r₁ hx_exp_mem.1
  have hf_sub :
      AnalyticOnNhd ℂ f (closedBall (0 : ℂ) (Real.exp y) \ ball (0 : ℂ) (Real.exp x)) :=
    hf.mono hsubset
  have hmid_bound :=
    hadamard_three_circles
      (f := f) (r₁ := Real.exp x) (r₂ := Real.exp y) (r := Real.exp (a * x + b * y))
      (Real.exp_pos x) (Real.exp_lt_exp.mpr hxy) hf_sub
      (Real.exp_le_exp.mpr hmid_left) (Real.exp_le_exp.mpr hmid_right)
  have hweights := subannulus_hadamard_weights hxy hab
  have hmid_bound' :
      circleSupNorm f (Real.exp (a * x + b * y)) ≤
        Real.rpow (circleSupNorm f (Real.exp x)) a *
          Real.rpow (circleSupNorm f (Real.exp y)) b := by
    -- Rewrite the Hadamard exponents on the subannulus to the affine coefficients `a` and `b`.
    simpa [hweights.1, hweights.2] using hmid_bound
  have hmid_pos : 0 < circleSupNorm f (Real.exp (a * x + b * y)) := hpos hmid_exp_mem
  have hx_pos : 0 < circleSupNorm f (Real.exp x) := hpos hx_exp_mem
  have hy_pos : 0 < circleSupNorm f (Real.exp y) := hpos hy_exp_mem
  -- Convert the multiplicative Hadamard estimate to the additive convexity inequality.
  exact log_le_add_of_le_rpow_mul_rpow hmid_pos hx_pos hy_pos hmid_bound'

/-- Exercise 8 (2): under positivity of the circle sup norm on the annulus, Hadamard's inequality
states that `log M(r)` is convex as a function of `log r`. -/
theorem hadamard_three_circles_log_convex
    {f : ℂ → ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r₂ \ ball (0 : ℂ) r₁))
    (hpos : ∀ ⦃r⦄, r ∈ Icc r₁ r₂ → 0 < circleSupNorm f r) :
    ConvexOn ℝ (Icc (Real.log r₁) (Real.log r₂))
      (fun t ↦ Real.log (circleSupNorm f (Real.exp t))) := by
  refine convexOn_iff_forall_pos.mpr ?_
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Route correction: package the ordered branch through a single subannulus interpolation lemma,
  -- then finish convexity by splitting on the order of `x` and `y`.
  simp_rw [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · -- Apply Hadamard on the smaller annulus `[exp x, exp y]`.
    exact subannulus_log_interpolation hr₁ hr₁₂ hf hpos hx hy hxy ha hb hab
  · subst hxy
    -- On the diagonal, the convexity inequality is an equality because `a + b = 1`.
    have harg :
        a * x + b * x = x := by
      calc
        a * x + b * x = (a + b) * x := by ring
        _ = x := by rw [hab, one_mul]
    have hrhs :
        a * Real.log (circleSupNorm f (Real.exp x)) +
            b * Real.log (circleSupNorm f (Real.exp x)) =
          Real.log (circleSupNorm f (Real.exp x)) := by
      calc
        a * Real.log (circleSupNorm f (Real.exp x)) +
            b * Real.log (circleSupNorm f (Real.exp x)) =
          (a + b) * Real.log (circleSupNorm f (Real.exp x)) := by ring
        _ = Real.log (circleSupNorm f (Real.exp x)) := by rw [hab, one_mul]
    simp [harg, hrhs]
  · have hswap :=
      subannulus_log_interpolation hr₁ hr₁₂ hf hpos hy hx hyx hb ha (by nlinarith [hab])
    -- Swap the endpoints and coefficients back to the original order.
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hswap
