import Mathlib
import DifferentialForms_Cartan_1970.III.section08.«0001_Definition_III_2_extra_1»
import DifferentialForms_Cartan_1970.IV.section16.«0005_Theorem_IV_4_extra_5»

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Filter InnerProductSpace Metric Real Topology

-- Semantic search tool unavailable in this session; statement names were chosen by direct
-- inspection of the local harmonic-function and uniform-convergence APIs.

/-- Helper for Exercise 3: if the pole lies strictly inside a circle, then the Poisson kernel is
continuous along that circle. -/
lemma poissonKernel_continuousOn_sphere_of_mem_ball {c z : ℂ} {r : ℝ}
    (hz : z ∈ Metric.ball c r) :
    ContinuousOn (poissonKernel c z) (Metric.sphere c r) := by
  -- The numerator and denominator are continuous, and the interior pole keeps the denominator away
  -- from zero on the boundary circle.
  have h_num :
      ContinuousOn (fun x : ℂ ↦ ‖x - c‖ ^ 2 - ‖z - c‖ ^ 2) (Metric.sphere c r) := by
    exact ((continuousOn_id.sub continuousOn_const).norm.pow 2).sub continuousOn_const
  have h_den :
      ContinuousOn (fun x : ℂ ↦ ‖(x - c) - (z - c)‖ ^ 2) (Metric.sphere c r) := by
    exact (((continuousOn_id.sub continuousOn_const).sub continuousOn_const).norm.pow 2)
  refine ContinuousOn.div h_num h_den ?_
  intro x hx
  have hx_ne : x ≠ z := by
    intro hxz
    have : ‖z - c‖ = r := by simpa [hxz] using hx
    exact (mem_ball_iff_norm.mp hz).ne this
  have hsub_eq : (x - c) - (z - c) = x - z := by ring
  have hdiff : (x - c) - (z - c) ≠ 0 := by
    rw [hsub_eq]
    exact sub_ne_zero.mpr hx_ne
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hdiff)

/-- Helper for Exercise 3: the Harnack inequalities on a disc hold at every strictly smaller
comparison radius. -/
lemma harmonic_nonneg_ball_harnack_of_lt_radius {f : ℂ → ℝ} {c z : ℂ} {R r : ℝ}
    (hrR : r < R) (hf : HarmonicOnNhd f (Metric.ball c R))
    (hf_nonneg : ∀ w ∈ Metric.ball c R, 0 ≤ f w) (hz : z ∈ Metric.ball c r) :
    ((r - ‖z - c‖) / (r + ‖z - c‖)) * f c ≤ f z ∧
      f z ≤ ((r + ‖z - c‖) / (r - ‖z - c‖)) * f c := by
  have hr_pos : 0 < r := pos_of_mem_ball hz
  have hclosed : HarmonicOnNhd f (Metric.closedBall c |r|) := by
    apply hf.mono
    simpa [abs_of_pos hr_pos] using
      (Metric.closedBall_subset_ball hrR : Metric.closedBall c r ⊆ Metric.ball c R)
  have hz_abs : z ∈ Metric.ball c |r| := by
    simpa [abs_of_pos hr_pos] using hz
  have hmean : Real.circleAverage f c r = f c := by
    simpa [abs_of_pos hr_pos] using (HarmonicOnNhd.circleAverage_eq hclosed)
  have hpoisson : Real.circleAverage (poissonKernel c z • f) c r = f z :=
    by simpa [abs_of_pos hr_pos] using
      (HarmonicOnNhd.circleAverage_poissonKernel_smul hclosed hz_abs)
  have hf_circle : CircleIntegrable f c r := by
    apply ContinuousOn.circleIntegrable hr_pos.le
    exact hf.continuousOn.mono (Metric.sphere_subset_ball hrR)
  have hkernel_circle : CircleIntegrable (poissonKernel c z • f) c r := by
    exact hf_circle.smul_of_continuousOn
      (poissonKernel_continuousOn_sphere_of_mem_ball hz_abs)
  have hlower_circle : CircleIntegrable
      (fun x : ℂ ↦ ((r - ‖z - c‖) / (r + ‖z - c‖)) • f x) c r :=
    hf_circle.const_fun_smul
  have hupper_circle : CircleIntegrable
      (fun x : ℂ ↦ ((r + ‖z - c‖) / (r - ‖z - c‖)) • f x) c r :=
    hf_circle.const_fun_smul
  have hlower_point :
      ∀ x ∈ Metric.sphere c |r|,
        ((fun x : ℂ ↦ ((r - ‖z - c‖) / (r + ‖z - c‖)) • f x) x) ≤
          ((poissonKernel c z • f) x) := by
    intro x hx
    have hx' : x ∈ Metric.sphere c r := by simpa [abs_of_pos hr_pos] using hx
    have hkernel :
        (r - ‖z - c‖) / (r + ‖z - c‖) ≤ poissonKernel c z x := by
      simpa [poissonKernel_eq_re_herglotzRieszKernel, herglotzRieszKernel_def,
        Function.comp_apply] using
        (le_re_herglotzRieszKernel (c := c) (z := x) (w := z) (R := r) hx' hz)
    have hfx_nonneg : 0 ≤ f x := hf_nonneg x (Metric.sphere_subset_ball hrR hx')
    simpa [smul_eq_mul] using mul_le_mul_of_nonneg_right hkernel hfx_nonneg
  have hupper_point :
      ∀ x ∈ Metric.sphere c |r|,
        ((poissonKernel c z • f) x) ≤
          ((fun x : ℂ ↦ ((r + ‖z - c‖) / (r - ‖z - c‖)) • f x) x) := by
    intro x hx
    have hx' : x ∈ Metric.sphere c r := by simpa [abs_of_pos hr_pos] using hx
    have hkernel :
        poissonKernel c z x ≤ (r + ‖z - c‖) / (r - ‖z - c‖) := by
      simpa [poissonKernel_eq_re_herglotzRieszKernel, herglotzRieszKernel_def,
        Function.comp_apply] using
        (re_herglotzRieszKernel_le (c := c) (z := x) (w := z) (R := r) hx' hz)
    have hfx_nonneg : 0 ≤ f x := hf_nonneg x (Metric.sphere_subset_ball hrR hx')
    simpa [smul_eq_mul] using mul_le_mul_of_nonneg_right hkernel hfx_nonneg
  constructor
  · -- Compare the Poisson average from below with a constant multiple of the ordinary mean value.
    calc
      ((r - ‖z - c‖) / (r + ‖z - c‖)) * f c =
          Real.circleAverage (fun x : ℂ ↦ ((r - ‖z - c‖) / (r + ‖z - c‖)) • f x) c r := by
            rw [Real.circleAverage_fun_smul, hmean, smul_eq_mul]
      _ ≤ Real.circleAverage (poissonKernel c z • f) c r :=
        Real.circleAverage_mono hlower_circle hkernel_circle hlower_point
      _ = f z := hpoisson
  · -- The same comparison from above gives the second Harnack inequality.
    calc
      f z = Real.circleAverage (poissonKernel c z • f) c r := hpoisson.symm
      _ ≤ Real.circleAverage (fun x : ℂ ↦ ((r + ‖z - c‖) / (r - ‖z - c‖)) • f x) c r :=
        Real.circleAverage_mono hkernel_circle hupper_circle hupper_point
      _ = ((r + ‖z - c‖) / (r - ‖z - c‖)) * f c := by
            rw [Real.circleAverage_fun_smul, hmean, smul_eq_mul]

/-- Helper for Exercise 3: the exact Harnack inequalities on an open disc are obtained by proving
them on every smaller radius and letting the radius tend to the boundary. -/
lemma harmonic_nonneg_ball_harnack_center {f : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : HarmonicOnNhd f (Metric.ball c R))
    (hf_nonneg : ∀ z ∈ Metric.ball c R, 0 ≤ f z) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    ((R - ‖z - c‖) / (R + ‖z - c‖)) * f c ≤ f z ∧
      f z ≤ ((R + ‖z - c‖) / (R - ‖z - c‖)) * f c := by
  -- Route correction: positivity is only known on interior circles, so we prove the estimate for
  -- every radius `r < R` with `z ∈ ball c r` and then pass to the limit `r → R`.
  let ρ : ℝ := ‖z - c‖
  have hρlt : ρ < R := by simpa [ρ] using mem_ball_iff_norm.mp hz
  let radius : ℕ → ℝ := fun n ↦ R - (R - ρ) / ((n : ℝ) + 2)
  have hradius_mem : ∀ n, z ∈ Metric.ball c (radius n) := by
    intro n
    have hden_pos : 0 < (n : ℝ) + 2 := by positivity
    have hden_gt_one : 1 < (n : ℝ) + 2 := by nlinarith
    have hfrac_lt : (R - ρ) / ((n : ℝ) + 2) < R - ρ := by
      have hmul : R - ρ < (R - ρ) * ((n : ℝ) + 2) := by
        nlinarith [sub_pos.mpr hρlt, hden_gt_one]
      exact (div_lt_iff₀ hden_pos).2 hmul
    have hlt : ρ < radius n := by
      dsimp [radius]
      nlinarith
    exact mem_ball_iff_norm.mpr <| by simpa [ρ, radius] using hlt
  have hradius_lt : ∀ n, radius n < R := by
    intro n
    have hfrac_pos : 0 < (R - ρ) / ((n : ℝ) + 2) := by
      exact div_pos (sub_pos.mpr hρlt) (by positivity)
    dsimp [radius]
    linarith
  have hstep :
      ∀ n, ((radius n - ρ) / (radius n + ρ)) * f c ≤ f z ∧
        f z ≤ ((radius n + ρ) / (radius n - ρ)) * f c := by
    intro n
    simpa [ρ] using
      harmonic_nonneg_ball_harnack_of_lt_radius (r := radius n) (c := c) (z := z)
        (hradius_lt n) hf hf_nonneg (hradius_mem n)
  have hradius_tendsto : Tendsto radius atTop (𝓝 R) := by
    have hdiv_tendsto :
        Tendsto (fun n : ℕ ↦ (R - ρ) / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
      apply tendsto_const_nhds.div_atTop
      simpa using tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa [radius] using tendsto_const_nhds.sub hdiv_tendsto
  have hlower_tendsto :
      Tendsto (fun n ↦ ((radius n - ρ) / (radius n + ρ)) * f c) atTop
        (𝓝 (((R - ρ) / (R + ρ)) * f c)) := by
    have hcont :
        ContinuousAt (fun t : ℝ ↦ ((t - ρ) / (t + ρ)) * f c) R := by
      refine (ContinuousAt.div ?_ ?_ ?_).mul continuousAt_const
      · exact (continuous_id'.sub continuous_const).continuousAt
      · exact (continuous_id'.add continuous_const).continuousAt
      · linarith [hR, norm_nonneg (z - c)]
    simpa [radius] using hcont.tendsto.comp hradius_tendsto
  have hupper_tendsto :
      Tendsto (fun n ↦ ((radius n + ρ) / (radius n - ρ)) * f c) atTop
        (𝓝 (((R + ρ) / (R - ρ)) * f c)) := by
    have hcont :
        ContinuousAt (fun t : ℝ ↦ ((t + ρ) / (t - ρ)) * f c) R := by
      refine (ContinuousAt.div ?_ ?_ ?_).mul continuousAt_const
      · exact (continuous_id'.add continuous_const).continuousAt
      · exact (continuous_id'.sub continuous_const).continuousAt
      · linarith
    simpa [radius] using hcont.tendsto.comp hradius_tendsto
  constructor
  · -- Pass the lower inequality to the limit along the comparison radii.
    simpa [ρ] using
      le_of_tendsto_of_tendsto' hlower_tendsto tendsto_const_nhds (fun n ↦ (hstep n).1)
  · -- Pass the upper inequality to the limit in the same way.
    simpa [ρ] using
      le_of_tendsto_of_tendsto' tendsto_const_nhds hupper_tendsto (fun n ↦ (hstep n).2)

/-- Exercise 3 (1). A nonnegative real-valued harmonic function on the disc `|z| < R` satisfies
the Harnack inequalities there. -/
theorem harmonic_nonneg_disc_harnack {f : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : HarmonicOnNhd f (Metric.ball (0 : ℂ) R))
    (hf_nonneg : ∀ z ∈ Metric.ball (0 : ℂ) R, 0 ≤ f z) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ((R - ‖z‖) / (R + ‖z‖)) * f 0 ≤ f z ∧
      f z ≤ ((R + ‖z‖) / (R - ‖z‖)) * f 0 := by
  -- Specialize the arbitrary-center Harnack estimate to the centered disc.
  simpa [sub_zero] using
    harmonic_nonneg_ball_harnack_center (c := (0 : ℂ)) hR hf hf_nonneg hz

/-- Exercise 3 (2). On the concentric half-disc, a nonnegative real-valued harmonic function is
bounded between one third and three times its value at the center. -/
theorem harmonic_nonneg_half_disc_bound {f : ℂ → ℝ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : HarmonicOnNhd f (Metric.ball a r))
    (hf_nonneg : ∀ z ∈ Metric.ball a r, 0 ≤ f z) {z : ℂ}
    (hz : z ∈ Metric.ball a (r / 2)) :
    (1 / 3 : ℝ) * f a ≤ f z ∧ f z ≤ 3 * f a := by
  -- First apply the exact Harnack estimate centered at `a`.
  have hfa_nonneg : 0 ≤ f a := hf_nonneg a (Metric.mem_ball_self hr)
  have hz' : z ∈ Metric.ball a r := by
    exact Metric.ball_subset_ball (by linarith) hz
  obtain ⟨hlower, hupper⟩ := harmonic_nonneg_ball_harnack_center (c := a) hr hf hf_nonneg hz'
  have hnorm_lt : ‖z - a‖ < r / 2 := by simpa using mem_ball_iff_norm.mp hz
  have hcoeff_lower : (1 / 3 : ℝ) ≤ (r - ‖z - a‖) / (r + ‖z - a‖) := by
    have hden_pos : 0 < r + ‖z - a‖ := by positivity
    field_simp [hden_pos.ne', (show (3 : ℝ) ≠ 0 by norm_num)]
    nlinarith [hnorm_lt, hr, norm_nonneg (z - a)]
  have hcoeff_upper : (r + ‖z - a‖) / (r - ‖z - a‖) ≤ (3 : ℝ) := by
    have hden_pos : 0 < r - ‖z - a‖ := by
      nlinarith [hnorm_lt]
    have hmain : r + ‖z - a‖ ≤ 3 * (r - ‖z - a‖) := by
      nlinarith [hnorm_lt, hr, norm_nonneg (z - a)]
    exact (div_le_iff₀ hden_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  constructor
  · -- Replace the Harnack coefficient by the coarser lower bound `1 / 3`.
    exact (mul_le_mul_of_nonneg_right hcoeff_lower hfa_nonneg).trans hlower
  · -- Replace the Harnack coefficient by the coarser upper bound `3`.
    exact hupper.trans <| mul_le_mul_of_nonneg_right hcoeff_upper hfa_nonneg

/-- Helper for Exercise 3: two points are harmonically comparable on `D` if one positive constant
controls the values of every nonnegative harmonic function at those two points. -/
def HarmonicComparable (D : Set ℂ) (x y : ℂ) : Prop :=
  ∃ C > 0, ∀ {f : ℂ → ℝ}, HarmonicOnNhd f D → (∀ z ∈ D, 0 ≤ f z) →
    f x ≤ C * f y ∧ f y ≤ C * f x

/-- Helper for Exercise 3: harmonic comparability is reflexive. -/
lemma harmonicComparable_refl {D : Set ℂ} (x : ℂ) :
    HarmonicComparable D x x := by
  -- The value at one point is trivially controlled by itself with constant `1`.
  refine ⟨1, zero_lt_one, ?_⟩
  intro f hf hf_nonneg
  constructor <;> simp

/-- Helper for Exercise 3: harmonic comparability is symmetric. -/
lemma harmonicComparable_symm {D : Set ℂ} {x y : ℂ}
    (hxy : HarmonicComparable D x y) :
    HarmonicComparable D y x := by
  rcases hxy with ⟨C, hC, hCprop⟩
  -- The defining inequalities are symmetric once the order of the pair is reversed.
  refine ⟨C, hC, ?_⟩
  intro f hf hf_nonneg
  simpa [and_comm] using hCprop hf hf_nonneg

/-- Helper for Exercise 3: harmonic comparability composes along chains of points. -/
lemma harmonicComparable_trans {D : Set ℂ} {x y z : ℂ}
    (hxy : HarmonicComparable D x y) (hyz : HarmonicComparable D y z) :
    HarmonicComparable D x z := by
  rcases hxy with ⟨Cxy, hCxy, hxy_prop⟩
  rcases hyz with ⟨Cyz, hCyz, hyz_prop⟩
  -- Multiply the two constants and compose the two comparison inequalities.
  refine ⟨Cxy * Cyz, mul_pos hCxy hCyz, ?_⟩
  intro f hf hf_nonneg
  obtain ⟨hxy₁, hxy₂⟩ := hxy_prop hf hf_nonneg
  obtain ⟨hyz₁, hyz₂⟩ := hyz_prop hf hf_nonneg
  constructor
  · calc
      f x ≤ Cxy * f y := hxy₁
      _ ≤ Cxy * (Cyz * f z) := by
            exact mul_le_mul_of_nonneg_left hyz₁ hCxy.le
      _ = (Cxy * Cyz) * f z := by ring
  · calc
      f z ≤ Cyz * f y := hyz₂
      _ ≤ Cyz * (Cxy * f x) := by
            exact mul_le_mul_of_nonneg_left hxy₂ hCyz.le
      _ = (Cxy * Cyz) * f x := by ring

/-- Helper for Exercise 3: the half-disc Harnack estimate gives a geometry-only local comparison
with constant `3`. -/
lemma harmonic_nonneg_local_comparable {D : Set ℂ} {x y : ℂ} (hx : x ∈ D) {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball x r ⊆ D) (hy : y ∈ Metric.ball x (r / 2)) :
    HarmonicComparable D x y := by
  refine ⟨3, by norm_num, ?_⟩
  intro f hf hf_nonneg
  -- Restrict the harmonic function to the comparison disc and apply the half-disc bound.
  have hf_ball : HarmonicOnNhd f (Metric.ball x r) := hf.mono hball
  have hf_nonneg_ball : ∀ z ∈ Metric.ball x r, 0 ≤ f z := fun z hz ↦ hf_nonneg z (hball hz)
  obtain ⟨hlower, hupper⟩ := harmonic_nonneg_half_disc_bound hr hf_ball hf_nonneg_ball hy
  have hfx_nonneg : 0 ≤ f x := hf_nonneg x hx
  constructor
  · -- The lower half-disc bound is equivalent to the reverse upper bound after multiplying by `3`.
    nlinarith
  · exact hupper

/-- Helper for Exercise 3: once one base point is fixed, every point of a connected open domain is
harmonically comparable with that base point. -/
lemma harmonic_nonneg_connected_comparable {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) {a : ℂ} (ha : a ∈ D) :
    ∀ x ∈ D, HarmonicComparable D x a := by
  classical
  let S : Set D := {x | HarmonicComparable D (x : ℂ) a}
  have hS_open : IsOpen S := by
    -- Every comparable point carries a small ball of comparable points via the local Harnack step.
    refine Metric.isOpen_iff.mpr ?_
    intro x hxS
    rcases Metric.isOpen_iff.mp hD_open x x.property with ⟨r, hr, hball⟩
    refine ⟨r / 2, by linarith, ?_⟩
    intro y hy
    have hy' : (y : ℂ) ∈ Metric.ball (x : ℂ) (r / 2) := by simpa using hy
    have hlocal : HarmonicComparable D (x : ℂ) (y : ℂ) :=
      harmonic_nonneg_local_comparable x.property hr hball hy'
    -- Route correction: propagate comparability by composing the local step with the known global
    -- comparison to the base point.
    exact harmonicComparable_trans (harmonicComparable_symm hlocal) hxS
  have hS_compl_open : IsOpen Sᶜ := by
    -- If a nearby point were comparable to the base point, transitivity would force the center to
    -- be comparable as well, contradicting the complement assumption.
    refine Metric.isOpen_iff.mpr ?_
    intro x hxS
    have hx_not : ¬ HarmonicComparable D (x : ℂ) a := by simpa [S] using hxS
    rcases Metric.isOpen_iff.mp hD_open x x.property with ⟨r, hr, hball⟩
    refine ⟨r / 2, by linarith, ?_⟩
    intro y hy
    have hy' : (y : ℂ) ∈ Metric.ball (x : ℂ) (r / 2) := by simpa using hy
    have hlocal : HarmonicComparable D (x : ℂ) (y : ℂ) :=
      harmonic_nonneg_local_comparable x.property hr hball hy'
    have hy_not : ¬ HarmonicComparable D (y : ℂ) a := by
      intro hyS'
      exact hx_not (harmonicComparable_trans hlocal hyS')
    simpa [S] using hy_not
  have hS_clopen : IsClopen S := ⟨isOpen_compl_iff.mp hS_compl_open, hS_open⟩
  have haS : (⟨a, ha⟩ : D) ∈ S := by
    simpa [S] using harmonicComparable_refl (D := D) a
  letI : PreconnectedSpace D := Subtype.preconnectedSpace hD_connected.isPreconnected
  have hSuniv : S = Set.univ := IsClopen.eq_univ hS_clopen ⟨⟨a, ha⟩, haS⟩
  intro x hx
  have hxS : (⟨x, hx⟩ : D) ∈ S := by simp [hSuniv]
  simpa [S] using hxS

/-- Exercise 3 (3). On a compact subset of a connected open set, nonnegative real-valued harmonic
functions are mutually comparable up to a constant depending only on the ambient domain and the
compact subset. -/
theorem harmonic_nonneg_compact_comparable {D K : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ M : ℝ, ∀ {f : ℂ → ℝ} (_hf : HarmonicOnNhd f D) (_hf_nonneg : ∀ z ∈ D, 0 ≤ f z)
      {z₁ z₂ : ℂ} (_ : z₁ ∈ K) (_ : z₂ ∈ K), f z₁ ≤ M * f z₂ := by
  classical
  by_cases hK_empty : K = ∅
  · -- The empty compact set has a vacuous comparison statement.
    refine ⟨0, ?_⟩
    intro f _hf _hf_nonneg z₁ z₂ hz₁ hz₂
    simp [hK_empty] at hz₁
  rcases Set.nonempty_iff_ne_empty.mpr hK_empty with ⟨a, haK⟩
  have haD : a ∈ D := hKD haK
  have hcompare_to_base := harmonic_nonneg_connected_comparable hD_open hD_connected haD
  have hlocal_cover :
      ∀ x : K,
        ∃ r > 0, Metric.ball (x : ℂ) r ⊆ D ∧
          ∃ C > 0,
            ∀ {f : ℂ → ℝ} (hf : HarmonicOnNhd f D) (hf_nonneg : ∀ z ∈ D, 0 ≤ f z) {z : ℂ},
              z ∈ Metric.ball (x : ℂ) (r / 2) →
                f z ≤ (3 * C) * f a ∧ f a ≤ (3 * C) * f z := by
    intro x
    rcases Metric.isOpen_iff.mp hD_open x (hKD x.property) with ⟨r, hr, hball⟩
    rcases hcompare_to_base x (hKD x.property) with ⟨C, hC, hCprop⟩
    refine ⟨r, hr, hball, C, hC, ?_⟩
    intro f hf hf_nonneg z hz
    -- Reuse the half-disc Harnack bound on the local ball centered at `x`.
    have hf_ball : HarmonicOnNhd f (Metric.ball (x : ℂ) r) := hf.mono hball
    have hf_nonneg_ball : ∀ w ∈ Metric.ball (x : ℂ) r, 0 ≤ f w := fun w hw ↦ hf_nonneg w
      (hball hw)
    obtain ⟨hlower, hupper⟩ :=
      harmonic_nonneg_half_disc_bound (a := (x : ℂ)) hr hf_ball hf_nonneg_ball hz
    have hxz : f (x : ℂ) ≤ 3 * f z := by
      have hfx_nonneg : 0 ≤ f (x : ℂ) := hf_nonneg x (hKD x.property)
      nlinarith
    have hzx : f z ≤ 3 * f (x : ℂ) := hupper
    obtain ⟨hxa, hax⟩ := hCprop hf hf_nonneg
    have hfa_nonneg : 0 ≤ f a := hf_nonneg a haD
    constructor
    · calc
        f z ≤ 3 * f x := hzx
        _ ≤ 3 * (C * f a) := by
              exact mul_le_mul_of_nonneg_left hxa (by norm_num)
        _ = (3 * C) * f a := by ring
    · calc
        f a ≤ C * f x := hax
        _ ≤ C * (3 * f z) := by
              exact mul_le_mul_of_nonneg_left hxz hC.le
        _ = (3 * C) * f z := by ring
  choose r hr_pos hball C hC_pos hbound using hlocal_cover
  rcases hK.elim_finite_subcover (fun x : K ↦ Metric.ball (x : ℂ) (r x / 2))
      (fun _ ↦ isOpen_ball) (fun z hz ↦ by
        refine Set.mem_iUnion.2 ?_
        refine ⟨⟨z, hz⟩, ?_⟩
        exact Metric.mem_ball_self (by linarith [hr_pos ⟨z, hz⟩])) with ⟨t, htcover⟩
  have ht_nonempty : t.Nonempty := by
    rcases Set.mem_iUnion₂.1 (htcover haK) with ⟨x, hx, hz⟩
    exact ⟨x, hx⟩
  let M₁ : ℝ := t.sup' ht_nonempty C
  have hM₁_pos : 0 < M₁ := by
    rcases ht_nonempty with ⟨x, hx⟩
    refine lt_of_lt_of_le (by nlinarith [hC_pos x]) ?_
    simpa [M₁] using (Finset.le_sup' (s := t) (f := C) (h := hx))
  refine ⟨(3 * M₁) ^ 2, ?_⟩
  intro f hf hf_nonneg z₁ z₂ hz₁ hz₂
  have hz₁_bound : f z₁ ≤ (3 * M₁) * f a := by
    rcases Set.mem_iUnion₂.1 (htcover hz₁) with ⟨x, hxt, hz₁x⟩
    obtain ⟨hz₁a, haa⟩ := hbound x hf hf_nonneg hz₁x
    have hMx : C x ≤ M₁ := by
      simpa [M₁] using (Finset.le_sup' (s := t) (f := C) (h := hxt))
    have h3Mx : 3 * C x ≤ 3 * M₁ := mul_le_mul_of_nonneg_left hMx (by norm_num)
    exact hz₁a.trans <| mul_le_mul_of_nonneg_right h3Mx (hf_nonneg a haD)
  have ha_bound : f a ≤ (3 * M₁) * f z₂ := by
    rcases Set.mem_iUnion₂.1 (htcover hz₂) with ⟨x, hxt, hz₂x⟩
    obtain ⟨hz₂a, haa⟩ := hbound x hf hf_nonneg hz₂x
    have hMx : C x ≤ M₁ := by
      simpa [M₁] using (Finset.le_sup' (s := t) (f := C) (h := hxt))
    have h3Mx : 3 * C x ≤ 3 * M₁ := mul_le_mul_of_nonneg_left hMx (by norm_num)
    exact haa.trans <| mul_le_mul_of_nonneg_right h3Mx (hf_nonneg z₂ (hKD hz₂))
  -- Compare both points to the common base point and compose the two bounds.
  calc
    f z₁ ≤ (3 * M₁) * f a := hz₁_bound
    _ ≤ (3 * M₁) * ((3 * M₁) * f z₂) := by
          exact mul_le_mul_of_nonneg_left ha_bound (by positivity)
    _ = (3 * M₁) ^ 2 * f z₂ := by ring

/-- Helper for Exercise 3: the compact Harnack comparison from part (iii) bounds every monotone
harmonic value `u n z` above once the base-point sequence `u n a` is bounded above. -/
lemma monotone_harmonic_pointwise_bddAbove {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) {u : ℕ → ℂ → ℝ}
    (hu_harmonic : ∀ n, HarmonicOnNhd (u n) D) (hu_mono : Monotone u) {a : ℂ} (ha : a ∈ D)
    (ha_bdd : BddAbove (Set.range fun n ↦ u n a)) :
    ∀ z ∈ D, BddAbove (Set.range fun n ↦ u n z) := by
  intro z hz
  let K : Set ℂ := insert a ({z} : Set ℂ)
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_insert isCompact_singleton
  have hKD : K ⊆ D := by
    intro w hw
    have hw' : w = a ∨ w = z := by
      simpa [K] using hw
    rcases hw' with rfl | rfl
    · exact ha
    · exact hz
  rcases harmonic_nonneg_compact_comparable hD_open hD_connected hK_compact hKD with
    ⟨M, hM⟩
  have hM_ge_one : 1 ≤ M := by
    simpa [K] using
      (hM (f := fun _ : ℂ ↦ (1 : ℝ)) (harmonicOnNhd_const (1 : ℝ))
        (fun _ _ ↦ by positivity) (z₁ := a) (z₂ := a) (by simp [K]) (by simp [K]))
  have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM_ge_one
  rcases ha_bdd with ⟨A, hA⟩
  refine ⟨M * (A - u 0 a) + u 0 z, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hcompare_increment : u n z - u 0 z ≤ M * (u n a - u 0 a) := by
    let v : ℂ → ℝ := fun w ↦ u n w - u 0 w
    have hv_harmonic : HarmonicOnNhd v D := (hu_harmonic n).sub (hu_harmonic 0)
    have hv_nonneg : ∀ w ∈ D, 0 ≤ v w := by
      intro w hw
      exact sub_nonneg.mpr (hu_mono (Nat.zero_le n) w)
    simpa [v, K] using
      (hM (f := v) hv_harmonic hv_nonneg (z₁ := z) (z₂ := a) (by simp [K]) (by simp [K]))
  have hna : u n a ≤ A := hA ⟨n, rfl⟩
  have hstep₁ : (u n z - u 0 z) + u 0 z ≤ M * (u n a - u 0 a) + u 0 z := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hcompare_increment (u 0 z)
  have hstep₂ : M * (u n a - u 0 a) + u 0 z ≤ M * (A - u 0 a) + u 0 z := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hna _) hM_nonneg) (u 0 z)
  -- Compare `u n z` to the bounded base-point sequence through the fixed compact-comparison
  -- constant obtained from part (iii).
  calc
    u n z = (u n z - u 0 z) + u 0 z := by ring
    _ ≤ M * (u n a - u 0 a) + u 0 z := hstep₁
    _ ≤ M * (A - u 0 a) + u 0 z := hstep₂

/-- Helper for Exercise 3: uniform convergence on a boundary circle lets the circle averages pass
to the limit after parametrizing by `circleMap`. -/
lemma tendsto_circleAverage_of_tendstoUniformlyOn_sphere {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    {c : ℂ} {R : ℝ}
    (hcont : ∀ᶠ n in atTop, ContinuousOn (F n) (Metric.sphere c |R|))
    (hlimit : TendstoUniformlyOn F f atTop (Metric.sphere c |R|)) :
    Tendsto (fun n ↦ Real.circleAverage (F n) c R) atTop (𝓝 (Real.circleAverage f c R)) := by
  have hpreimage :
      (circleMap c R) ⁻¹' Metric.sphere c |R| = Set.univ := by
    ext θ
    simp
  have hlimit_comp_univ :
      TendstoUniformlyOn (fun n θ ↦ F n (circleMap c R θ))
        (fun θ ↦ f (circleMap c R θ)) atTop Set.univ := by
    simpa [hpreimage] using hlimit.comp (circleMap c R)
  have hlimit_comp :
      TendstoUniformlyOn (fun n θ ↦ F n (circleMap c R θ))
        (fun θ ↦ f (circleMap c R θ)) atTop (Set.uIcc 0 (2 * π)) :=
    hlimit_comp_univ.mono (by intro θ hθ; simp)
  have hcont_comp :
      ∀ᶠ n in atTop,
        ContinuousOn (fun θ : ℝ ↦ F n (circleMap c R θ)) (Set.uIcc 0 (2 * π)) := by
    refine hcont.mono ?_
    intro n hn
    have hcont_univ : ContinuousOn (fun θ : ℝ ↦ F n (circleMap c R θ)) Set.univ := by
      exact (hn.comp_continuous (continuous_circleMap c R) (circleMap_mem_sphere' c R)).continuousOn
    exact hcont_univ.mono (by intro θ hθ; simp)
  have hint :
      Tendsto (fun n ↦ ∫ θ in 0..2 * π, F n (circleMap c R θ)) atTop
        (𝓝 (∫ θ in 0..2 * π, f (circleMap c R θ))) :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn hcont_comp hlimit_comp
  have hsmul :
      Tendsto
        (fun n ↦ ((2 * π)⁻¹ : ℝ) • ∫ θ in 0..2 * π, F n (circleMap c R θ))
        atTop
        (𝓝 (((2 * π)⁻¹ : ℝ) • ∫ θ in 0..2 * π, f (circleMap c R θ))) := by
    exact tendsto_const_nhds.smul hint
  -- Re-express both circle averages as the same scalar multiple of the parametrized interval
  -- integral, then transport the integral limit through that fixed scalar.
  simpa [Real.circleAverage_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsmul

/-- Helper for Exercise 3: once the monotone harmonic sequence has a locally uniform limit, the
mean-value characterization from the source proof packages that limit as harmonic. -/
lemma monotone_harmonic_limit_hasMeanValueProperty {D : Set ℂ} (hD_open : IsOpen D)
    {u : ℕ → ℂ → ℝ} {f : ℂ → ℝ} (hu_harmonic : ∀ n, HarmonicOnNhd (u n) D)
    (hlimit : TendstoLocallyUniformlyOn u f atTop D) :
    HasMeanValuePropertyOn f D := by
  refine ⟨?_, ?_⟩
  · -- Local uniform convergence preserves continuity on the whole open domain.
    exact hlimit.continuousOn <|
      Filter.Frequently.of_forall fun n ↦ (hu_harmonic n).continuousOn
  · intro c R hclosed
    have hclosedBall_limit :
        TendstoUniformlyOn u f atTop (Metric.closedBall c |R|) := by
      exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).mp hlimit
        (Metric.closedBall c |R|) hclosed (isCompact_closedBall c |R|)
    have hsphere_limit :
        TendstoUniformlyOn u f atTop (Metric.sphere c |R|) :=
      hclosedBall_limit.mono Metric.sphere_subset_closedBall
    have hsphere_cont :
        ∀ᶠ n in atTop, ContinuousOn (u n) (Metric.sphere c |R|) := by
      exact Filter.Eventually.of_forall fun n ↦
        (hu_harmonic n).continuousOn.mono (Metric.sphere_subset_closedBall.trans hclosed)
    have hcircle_tendsto :
        Tendsto (fun n ↦ Real.circleAverage (u n) c R) atTop
          (𝓝 (Real.circleAverage f c R)) :=
      tendsto_circleAverage_of_tendstoUniformlyOn_sphere hsphere_cont hsphere_limit
    have hc_mem : c ∈ Metric.closedBall c |R| := Metric.mem_closedBall_self (abs_nonneg R)
    have hcenter_tendsto : Tendsto (fun n ↦ u n c) atTop (𝓝 (f c)) :=
      hclosedBall_limit.tendsto_at hc_mem
    have hmean_seq :
        (fun n ↦ Real.circleAverage (u n) c R) = fun n ↦ u n c := by
      funext n
      have hun_closed : HarmonicOnNhd (u n) (Metric.closedBall c |R|) :=
        (hu_harmonic n).mono hclosed
      simpa using (HarmonicOnNhd.circleAverage_eq hun_closed)
    have hcircle_as_center : Tendsto (fun n ↦ u n c) atTop (𝓝 (Real.circleAverage f c R)) := by
      simpa [hmean_seq] using hcircle_tendsto
    -- The source proof closes by sending the center identity `circleAverage (u n) = u n c` to the
    -- limit and identifying the two resulting pointwise limits.
    exact tendsto_nhds_unique hcircle_as_center hcenter_tendsto

/-- Helper for Exercise 3: the compact comparison constant from part (iii) controls every
nonnegative harmonic increment `u (m + n) - u n` on the same compact set. -/
lemma monotone_harmonic_increment_compare_on_compact {D K : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) {u : ℕ → ℂ → ℝ}
    (hu_harmonic : ∀ n, HarmonicOnNhd (u n) D) (hu_mono : Monotone u) {a : ℂ} (ha : a ∈ D)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ n m z, z ∈ K →
      u (m + n) z - u n z ≤ M * (u (m + n) a - u n a) := by
  let K' : Set ℂ := insert a K
  have hK'_compact : IsCompact K' := by
    simpa [K'] using hK.insert a
  have hK'D : K' ⊆ D := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hzK
    · exact ha
    · exact hKD hzK
  rcases harmonic_nonneg_compact_comparable hD_open hD_connected hK'_compact hK'D with
    ⟨M, hM⟩
  have hM_ge_one : 1 ≤ M := by
    -- The same comparison applied to the constant harmonic function `1` forces `M ≥ 1`.
    simpa [K'] using
      (hM (f := fun _ : ℂ ↦ (1 : ℝ)) (harmonicOnNhd_const (1 : ℝ))
        (fun _ _ ↦ by positivity) (z₁ := a) (z₂ := a) (by simp [K']) (by simp [K']))
  refine ⟨M, hM_ge_one, ?_⟩
  intro n m z hzK
  let v : ℂ → ℝ := fun w ↦ u (m + n) w - u n w
  have hv_harmonic : HarmonicOnNhd v D := (hu_harmonic (m + n)).sub (hu_harmonic n)
  have hv_nonneg : ∀ w ∈ D, 0 ≤ v w := by
    intro w hw
    exact sub_nonneg.mpr (hu_mono (Nat.le_add_left n m) w)
  -- Apply the compact comparison to the increment `v` on `insert a K`.
  simpa [v, K'] using
    (hM (f := v) hv_harmonic hv_nonneg (z₁ := z) (z₂ := a) (by simp [K', hzK]) (by simp [K']))

/-- Helper for Exercise 3: on the domain, subtracting one term of the monotone sequence from the
pointwise supremum rewrites the tail as an indexed supremum of scalar differences. -/
lemma monotone_harmonic_pointwise_tail_eq_ciSup {D : Set ℂ} {u : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hf_bdd : ∀ z ∈ D, BddAbove (Set.range fun n ↦ u n z))
    (hf_eq : ∀ z ∈ D, f z = ⨆ n, u n z) {z : ℂ} (hz : z ∈ D) (n : ℕ) :
    f z - u n z = ⨆ m, (u m z - u n z) := by
  have hsub_mono : Monotone (fun t : ℝ ↦ t - u n z) := by
    intro x y hxy
    exact sub_le_sub_right hxy _
  -- Push the fixed subtraction through the pointwise supremum using order continuity on `ℝ`.
  calc
    f z - u n z = (fun t : ℝ ↦ t - u n z) (⨆ m, u m z) := by rw [hf_eq z hz]
    _ = ⨆ m, (fun t : ℝ ↦ t - u n z) (u m z) := by
      exact Monotone.map_ciSup_of_continuousAt
        (g := fun m ↦ u m z) ((continuous_id'.sub continuous_const).continuousAt) hsub_mono
        (hf_bdd z hz)
    _ = ⨆ m, (u m z - u n z) := rfl

/-- Canonical locally-uniform form of Exercise 3 (4), using the owner abstraction
`TendstoLocallyUniformlyOn` on the open domain `D`. -/
theorem monotone_harmonic_tendstoLocallyUniformlyOn {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) {u : ℕ → ℂ → ℝ}
    (hu_harmonic : ∀ n, HarmonicOnNhd (u n) D)
    (hu_mono : Monotone u) {a : ℂ} (ha : a ∈ D)
    (ha_bdd : BddAbove (Set.range fun n ↦ u n a)) :
    ∃ f : ℂ → ℝ, HarmonicOnNhd f D ∧ TendstoLocallyUniformlyOn u f atTop D := by
  classical
  -- Route correction: the source proof first builds the pointwise monotone supremum, then uses the
  -- compact comparison theorem from part (iii) on the nonnegative increments `u m - u n` to turn
  -- boundedness at the base point into compact-uniform tail control.
  let f : ℂ → ℝ := fun z ↦ if hz : z ∈ D then ⨆ n, u n z else 0
  have hf_bdd : ∀ z ∈ D, BddAbove (Set.range fun n ↦ u n z) :=
    monotone_harmonic_pointwise_bddAbove hD_open hD_connected hu_harmonic hu_mono ha ha_bdd
  have hf_harmonic_of_limit :
      TendstoLocallyUniformlyOn u f atTop D → HarmonicOnNhd f D := by
    intro hlimit
    exact HasMeanValuePropertyOn.harmonicOnNhd
      (monotone_harmonic_limit_hasMeanValueProperty hD_open hu_harmonic hlimit) hD_open
  have hf_eq : ∀ z ∈ D, f z = ⨆ n, u n z := by
    intro z hz
    simp [f, hz]
  have hlimit : TendstoLocallyUniformlyOn u f atTop D := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open]
    intro K hKD hK
    rcases monotone_harmonic_increment_compare_on_compact hD_open hD_connected hu_harmonic
        hu_mono ha hK hKD with ⟨M, hM_ge_one, hcompare⟩
    let A : ℝ := ⨆ n, u n a
    have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM_ge_one
    have hA_ge : ∀ n, u n a ≤ A := fun n ↦ le_ciSup ha_bdd n
    have hbase_tendsto : Tendsto (fun n ↦ u n a) atTop (𝓝 A) := by
      simpa [A] using tendsto_atTop_ciSup (fun i j hij ↦ hu_mono hij a) ha_bdd
    have htail_tendsto : Tendsto (fun n ↦ A - u n a) atTop (𝓝 (0 : ℝ)) := by
      -- The scalar tail at the base point converges to zero by monotone convergence.
      have htail_tendsto' : Tendsto (fun n ↦ A - u n a) atTop (𝓝 (A - A)) := by
        exact tendsto_const_nhds.sub hbase_tendsto
      simpa using htail_tendsto'
    have hscaled_tendsto : Tendsto (fun n ↦ M * (A - u n a)) atTop (𝓝 (0 : ℝ)) := by
      have hscaled_tendsto' : Tendsto (fun n ↦ M * (A - u n a)) atTop (𝓝 (M * 0)) := by
        exact tendsto_const_nhds.mul htail_tendsto
      simpa using hscaled_tendsto'
    refine Metric.tendstoUniformlyOn_iff.2 ?_
    intro ε hε
    have hscalar_eventually : ∀ᶠ n in atTop, dist (M * (A - u n a)) 0 < ε := by
      simpa using hscaled_tendsto (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hscalar_eventually] with n hn z hzK
    have hzD : z ∈ D := hKD hzK
    have htail_nonneg : 0 ≤ M * (A - u n a) := by
      exact mul_nonneg hM_nonneg (sub_nonneg.mpr (hA_ge n))
    have hn' : M * (A - u n a) < ε := by
      have hn_abs : |M * (A - u n a)| < ε := by
        simpa [Real.dist_eq] using hn
      simpa [abs_of_nonneg htail_nonneg] using hn_abs
    have hun_le_hf : u n z ≤ f z := by
      rw [hf_eq z hzD]
      exact le_ciSup (hf_bdd z hzD) n
    have hdist_eq : dist (f z) (u n z) = f z - u n z := by
      rw [Real.dist_eq]
      exact abs_of_nonneg (sub_nonneg.mpr hun_le_hf)
    have hsup_bound : (⨆ m, (u m z - u n z)) ≤ M * (A - u n a) := by
      refine ciSup_le ?_
      intro m
      by_cases hmn : m < n
      · have hmn_le : m ≤ n := Nat.le_of_lt hmn
        have hnonpos : u m z - u n z ≤ 0 := sub_nonpos.mpr (hu_mono hmn_le z)
        exact hnonpos.trans htail_nonneg
      · have hnm : n ≤ m := Nat.le_of_not_gt hmn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        have hincrement :
            u (n + k) z - u n z ≤ M * (u (n + k) a - u n a) := by
          simpa [Nat.add_comm] using hcompare n k z hzK
        have hbase_tail :
            u (n + k) a - u n a ≤ A - u n a := sub_le_sub_right (hA_ge (n + k)) _
        exact hincrement.trans (mul_le_mul_of_nonneg_left hbase_tail hM_nonneg)
    -- Route correction: once the compact increment estimate is in place, the remaining step is the
    -- pointwise order rewrite from `f z` to the supremum of the scalar tails.
    have hdist_bound : dist (f z) (u n z) ≤ M * (A - u n a) := by
      calc
        dist (f z) (u n z) = f z - u n z := hdist_eq
        _ = ⨆ m, (u m z - u n z) :=
          monotone_harmonic_pointwise_tail_eq_ciSup hf_bdd hf_eq hzD n
        _ ≤ M * (A - u n a) := hsup_bound
    exact lt_of_le_of_lt hdist_bound hn'
  exact ⟨f, hf_harmonic_of_limit hlimit, hlimit⟩

/-- Exercise 3 (4). An increasing sequence of real-valued harmonic functions on a connected open
set whose values at one point are bounded above, equivalently bounded there in the monotone real
case, converges uniformly on each compact subset to a harmonic function. -/
theorem monotone_harmonic_tendstoUniformlyOn_compacts {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) {u : ℕ → ℂ → ℝ}
    (hu_harmonic : ∀ n, HarmonicOnNhd (u n) D)
    (hu_mono : Monotone u) {a : ℂ} (ha : a ∈ D)
    (ha_bdd : BddAbove (Set.range fun n ↦ u n a)) :
    ∃ f : ℂ → ℝ, HarmonicOnNhd f D ∧
      ∀ {K : Set ℂ} (_ : IsCompact K) (_ : K ⊆ D), TendstoUniformlyOn u f atTop K := by
  obtain ⟨f, hf, hlimit⟩ :=
    monotone_harmonic_tendstoLocallyUniformlyOn hD_open hD_connected hu_harmonic hu_mono ha
      ha_bdd
  refine ⟨f, hf, ?_⟩
  intro K hK hKD
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).mp hlimit K hKD hK
