/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
  -/

import Mathlib

section Chap04
section Section01

/-- Definition 4.1.1: For `a ∈ ℝ`, a formal power series centered at `a` is given by a sequence of real coefficients `(c_n)_{n≥0}`, corresponding to the formal expression `∑_{n=0}^∞ c_n (x - a)^n` in the indeterminate `x`; its `n`th coefficient is `coeff n`. -/
structure FormalPowerSeriesCenteredAt (a : ℝ) where
  coeff : ℕ → ℝ

/-- Definition 4.1.2 (Radius of convergence): for a formal power series `∑_{n=0}^∞ c_n (x-a)^n`, let `L = limsup_{n→∞} |c_n|^(1/n)` (valued in `[0, +∞]`); the radius of convergence is `R = 1 / L`, with the conventions `1/0 = +∞` and `1/(+∞) = 0`. -/
noncomputable def FormalPowerSeriesCenteredAt.radiusOfConvergence {a : ℝ}
    (f : FormalPowerSeriesCenteredAt a) : ENNReal :=
  (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius

/-- Helper for Theorem 4.1.1: `radiusOfConvergence` is the radius of the associated scalar formal multilinear series. -/
lemma FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius {a : ℝ}
    (f : FormalPowerSeriesCenteredAt a) :
    f.radiusOfConvergence = (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius := by
  rfl

/-- Definition 4.1.3: Define the function `f : ℝ \ {1} → ℝ` by `f(x) = 1 / (1 - x)`. -/
noncomputable def reciprocalOneSub (x : {x : ℝ // x ≠ 1}) : ℝ :=
  1 / (1 - (x : ℝ))

/-- Points of `(-1, 1)` are distinct from `1`. -/
lemma ne_one_of_mem_Ioo_neg_one_one {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : x ≠ 1 :=
  ne_of_lt hx.2

/-- The total real extension of `x ↦ 1 / (1 - x)`. -/
noncomputable def reciprocalOneSub_ext : ℝ → ℝ :=
  fun y => 1 / (1 - y)

/-- The total extension agrees with `reciprocalOneSub` away from `1`. -/
lemma reciprocalOneSub_ext_eq (x : ℝ) (hx : x ≠ 1) :
    reciprocalOneSub_ext x = reciprocalOneSub ⟨x, hx⟩ :=
  rfl

/-- Lemma 4.1.1: For every `x ∈ (-1, 1)`, one has `∑' n, x^n = 1/(1-x) = f(x)` (with `f = reciprocalOneSub`), and in particular `f` is real analytic at `0`. -/
lemma geometric_series_eq_reciprocalOneSub_and_analyticAt_zero :
    (∀ x : ℝ, ∀ hx : x ∈ Set.Ioo (-1 : ℝ) 1,
      (∑' n : ℕ, x ^ n) = 1 / (1 - x)
      ∧ 1 / (1 - x) = reciprocalOneSub_ext x)
    ∧ AnalyticAt ℝ reciprocalOneSub_ext 0 :=
  by
    constructor
    · intro x hx
      have hAbs : |x| < 1 := abs_lt.mpr ⟨hx.1, hx.2⟩
      constructor
      · simpa [one_div] using (tsum_geometric_of_abs_lt_one hAbs)
      · simp [reciprocalOneSub_ext]
    · change AnalyticAt ℝ (fun y : ℝ => 1 / (1 - y)) 0
      simpa [one_div] using
        (analyticAt_inv_one_sub (𝕜 := ℝ) (𝕝 := ℝ))

/-- Points of `(1, 3)` are distinct from `1`. -/
lemma ne_one_of_mem_Ioo_one_three {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 3) : x ≠ 1 :=
  by
    linarith [hx.1]

/-- Helper for Lemma 4.1.2: for `x ∈ (1,3)`, the shifted variable satisfies `|x-2| < 1`. -/
lemma helperForLemma_4_1_2_abs_shift_lt_one {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 3) :
    |x - 2| < 1 := by
  have hxLower : -1 < x - 2 := by linarith [hx.1]
  have hxUpper : x - 2 < 1 := by linarith [hx.2]
  exact abs_lt.mpr ⟨hxLower, hxUpper⟩

/-- Helper for Lemma 4.1.2: rewrite each shifted alternating term as a negated geometric term. -/
lemma helperForLemma_4_1_2_alternating_term_as_neg_geometric (x : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ (n + 1) * (x - 2) ^ n = -((((-1 : ℝ) * (x - 2)) ^ n)) := by
  calc
    (-1 : ℝ) ^ (n + 1) * (x - 2) ^ n
        = ((-1 : ℝ) ^ n * (-1 : ℝ)) * (x - 2) ^ n := by rw [pow_succ]
    _ = (-1 : ℝ) * (((-1 : ℝ) ^ n) * (x - 2) ^ n) := by ring
    _ = (-1 : ℝ) * ((((-1 : ℝ) * (x - 2)) ^ n)) := by rw [← mul_pow]
    _ = -((((-1 : ℝ) * (x - 2)) ^ n)) := by ring

/-- Helper for Lemma 4.1.2: the shifted alternating geometric series sums to `1/(1-x)` on `(1,3)`. -/
lemma helperForLemma_4_1_2_tsum_identity {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 3) :
    (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * (x - 2) ^ n) = 1 / (1 - x) := by
  have hAbs' : |x - 2| < 1 := helperForLemma_4_1_2_abs_shift_lt_one hx
  have hAbs : |(-1 : ℝ) * (x - 2)| < 1 := by
    simpa [abs_sub_comm] using hAbs'
  calc
    (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * (x - 2) ^ n)
        = ∑' n : ℕ, -((((-1 : ℝ) * (x - 2)) ^ n)) := by
            congr with n
            exact helperForLemma_4_1_2_alternating_term_as_neg_geometric x n
    _ = -(∑' n : ℕ, (((-1 : ℝ) * (x - 2)) ^ n)) := by
          simpa using (tsum_neg (f := fun n : ℕ => (((-1 : ℝ) * (x - 2)) ^ n)))
    _ = -((1 : ℝ) / (1 - ((-1 : ℝ) * (x - 2)))) := by
          simpa [one_div] using congrArg (fun t : ℝ => -t) (tsum_geometric_of_abs_lt_one hAbs)
    _ = 1 / (1 - x) := by
          have hshift : x - 1 = -(1 - x) := by ring
          calc
            -((1 : ℝ) / (1 - ((-1 : ℝ) * (x - 2)))) = -(x - 1)⁻¹ := by ring_nf
            _ = -((-(1 - x))⁻¹) := by rw [hshift]
            _ = -(-((1 - x)⁻¹)) := by rw [inv_neg]
            _ = (1 - x)⁻¹ := by ring
            _ = 1 / (1 - x) := by rw [one_div]

/-- Helper for Lemma 4.1.2: the extension `reciprocalOneSub_ext` is real-analytic at `2`. -/
lemma helperForLemma_4_1_2_analyticAt_two : AnalyticAt ℝ reciprocalOneSub_ext 2 := by
  change AnalyticAt ℝ (fun y : ℝ => 1 / (1 - y)) 2
  have hsub : AnalyticAt ℝ (fun y : ℝ => 1 - y) 2 :=
    analyticAt_const.sub analyticAt_id
  have hne : (1 - (2 : ℝ)) ≠ 0 := by norm_num
  simpa [one_div] using hsub.inv hne

/-- Lemma 4.1.2: For every `x ∈ (1, 3)`, one has `∑' n, (-1)^(n+1) (x-2)^n = 1/(1-x) = f(x)` (with `f = reciprocalOneSub`); in particular, `f` is real analytic at `2`. -/
lemma shifted_geometric_series_eq_reciprocalOneSub_and_analyticAt_two :
    (∀ x : ℝ, ∀ hx : x ∈ Set.Ioo (1 : ℝ) 3,
      (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * (x - 2) ^ n) = 1 / (1 - x)
      ∧ 1 / (1 - x) = reciprocalOneSub ⟨x, ne_one_of_mem_Ioo_one_three hx⟩)
    ∧ AnalyticAt ℝ reciprocalOneSub_ext 2 :=
  by
    constructor
    · intro x hx
      constructor
      · exact helperForLemma_4_1_2_tsum_identity hx
      · simp [reciprocalOneSub]
    · exact helperForLemma_4_1_2_analyticAt_two

/-- Helper for Theorem 4.1.3: translate a scalar formal multilinear series to a ball expansion centered at `a` by composition with subtraction. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_shiftedHasFPowerSeriesOnBall
    {a : ℝ} (p : FormalMultilinearSeries ℝ ℝ ℝ) (hpos : 0 < p.radius) :
    HasFPowerSeriesOnBall (fun x : ℝ => p.sum (x - a)) p a p.radius := by
  simpa [zero_add] using (p.hasFPowerSeriesOnBall hpos).comp_sub a

/-- Helper for Theorem 4.1.3: pick an intermediate `NNReal` radius strictly between `r` and the convergence radius. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_existsStrictIntermediateRadius
    {a r : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hrR : ENNReal.ofReal r < f.radiusOfConvergence) :
    ∃ ρ : NNReal, ENNReal.ofReal r < (ρ : ENNReal) ∧ (ρ : ENNReal) < f.radiusOfConvergence := by
  exact ENNReal.lt_iff_exists_nnreal_btwn.mp hrR

/-- Helper for Theorem 4.1.3: if `r < ρ`, then `[a-r, a+r]` lies in the open ball `Metric.ball a ρ`. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_Icc_subset_ball
    {a r ρ : ℝ} (hrρ : r < ρ) :
    Set.Icc (a - r) (a + r) ⊆ Metric.ball a ρ := by
  intro x hx
  have hleft : -r ≤ x - a := by linarith [hx.1]
  have hright : x - a ≤ r := by linarith [hx.2]
  have habs : |x - a| ≤ r := abs_le.mpr ⟨hleft, hright⟩
  have hlt : |x - a| < ρ := lt_of_le_of_lt habs hrρ
  change dist x a < ρ
  simpa [Real.dist_eq] using hlt

/-- Helper for Theorem 4.1.3: rewrite both partial sums and total sums in textbook coefficient form. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_rewriteSeriesForms
    {a : ℝ} (f : FormalPowerSeriesCenteredAt a) :
    ((fun N x => (FormalMultilinearSeries.ofScalars ℝ f.coeff).partialSum N (x - a)) =
      (fun N x => (Finset.range N).sum (fun n => f.coeff n * (x - a) ^ n)))
    ∧
    ((fun x => (FormalMultilinearSeries.ofScalars ℝ f.coeff).sum (x - a)) =
      (fun x => ∑' n, f.coeff n * (x - a) ^ n)) := by
  constructor
  · funext N x
    simp [FormalMultilinearSeries.partialSum, smul_eq_mul, mul_comm]
  · funext x
    simpa [FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
      (FormalMultilinearSeries.ofScalars_sum_eq (E := ℝ) f.coeff (x - a))

/-- Helper for Theorem 4.1.3: inside the convergence radius, the scalar-series sum function is continuous. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_continuousAt_inside_radius
    {a x : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hx : ENNReal.ofReal |x - a| < f.radiusOfConvergence) :
    ContinuousAt (fun y => ∑' n, f.coeff n * (y - a) ^ n) x := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ f.coeff
  have hRadiusEq : f.radiusOfConvergence = p.radius := by
    simpa [p] using FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius f
  have hRpos : 0 < f.radiusOfConvergence :=
    lt_of_le_of_lt (by simp) hx
  have hpPos : 0 < p.radius := by
    simpa [hRadiusEq] using hRpos
  have hShifted : HasFPowerSeriesOnBall (fun y : ℝ => p.sum (y - a)) p a p.radius :=
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_shiftedHasFPowerSeriesOnBall p hpPos
  have hxRadius : ENNReal.ofReal |x - a| < p.radius := by
    simpa [hRadiusEq] using hx
  have hxBall : x ∈ EMetric.ball a p.radius := by
    have hxDist : ENNReal.ofReal (dist x a) < p.radius := by
      simpa [Real.dist_eq] using hxRadius
    simpa [EMetric.mem_ball, edist_dist] using hxDist
  have hAnalytic : AnalyticAt ℝ (fun y : ℝ => p.sum (y - a)) x :=
    hShifted.analyticAt_of_mem hxBall
  have hCont : ContinuousAt (fun y : ℝ => p.sum (y - a)) x :=
    hAnalytic.continuousAt
  have hRewrite := FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_rewriteSeriesForms f
  rw [← hRewrite.2]
  exact hCont

/-- Helper for Theorem 4.1.1: identify the textbook radius with the formal multilinear-series radius. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_1_radius_eq_ofScalarsRadius {a : ℝ}
    (f : FormalPowerSeriesCenteredAt a) :
    f.radiusOfConvergence = (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius :=
  FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius f

/-- Helper for Theorem 4.1.1: summability of scalar terms forces weighted norms to tend to `0`. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_1_tendsto_weightedNorm_zero_of_summable
    {a x : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hs : Summable (fun n : ℕ => f.coeff n * (x - a) ^ n)) :
    Filter.Tendsto (fun n : ℕ => ‖f.coeff n‖ * ‖x - a‖ ^ n) Filter.atTop (nhds 0) := by
  have hzero : Filter.Tendsto (fun n : ℕ => f.coeff n * (x - a) ^ n) Filter.atTop (nhds (0 : ℝ)) :=
    hs.tendsto_atTop_zero
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖f.coeff n * (x - a) ^ n‖) Filter.atTop
      (nhds ‖(0 : ℝ)‖) :=
    hzero.norm
  simpa [norm_mul, norm_pow] using hnorm

/-- Helper for Theorem 4.1.1: if the scalar series at `x` is summable, then `|x-a|` lies within the radius. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_1_ofRealAbs_le_radius_of_summable
    {a x : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hs : Summable (fun n : ℕ => f.coeff n * (x - a) ^ n)) :
    ENNReal.ofReal |x - a| ≤ f.radiusOfConvergence := by
  have hAbsNonneg : 0 ≤ |x - a| := abs_nonneg (x - a)
  let r : NNReal := ⟨|x - a|, hAbsNonneg⟩
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ f.coeff
  have hsNorm : Summable (fun n : ℕ => ‖f.coeff n‖ * ‖x - a‖ ^ n) := by
    have hsNormMul : Summable (fun n : ℕ => ‖f.coeff n * (x - a) ^ n‖) := hs.norm
    simpa [norm_mul, norm_pow] using hsNormMul
  have hsRadius : Summable (fun n : ℕ => ‖p n‖ * (r : ℝ) ^ n) := by
    simpa [p, r, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using hsNorm
  have hleRadius : (r : ENNReal) ≤ p.radius := p.le_radius_of_summable_norm (r := r) hsRadius
  have hcoer : ENNReal.ofReal |x - a| = (r : ENNReal) := by
    simpa [r] using (ENNReal.ofReal_eq_coe_nnreal hAbsNonneg)
  have hleRadius' : ENNReal.ofReal |x - a| ≤ p.radius := by
    rw [hcoer]
    exact hleRadius
  have hRadiusEq : f.radiusOfConvergence = p.radius :=
    FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius f
  calc
    ENNReal.ofReal |x - a| ≤ p.radius := hleRadius'
    _ = f.radiusOfConvergence := hRadiusEq.symm

/-- Theorem 4.1.1: (Divergence outside the radius of convergence) for a power series with center `a` and coefficients `c_n`, if `|x - a| > R` where `R` is the radius of convergence, then `∑ n, c_n * (x - a)^n` diverges at `x`. -/
theorem FormalPowerSeriesCenteredAt.diverges_outside_radius {a x : ℝ}
    (f : FormalPowerSeriesCenteredAt a)
    (hx : f.radiusOfConvergence < ENNReal.ofReal |x - a|) :
    ¬Summable (fun n : ℕ => f.coeff n * (x - a) ^ n) :=
  by
    intro hs
    have hle : ENNReal.ofReal |x - a| ≤ f.radiusOfConvergence :=
      FormalPowerSeriesCenteredAt.helperForTheorem_4_1_1_ofRealAbs_le_radius_of_summable f hs
    exact (not_le_of_gt hx) hle

/-- Theorem 4.1.2: If `|x - a| < R` for a power series `∑ n, c_n (x-a)^n` with radius of convergence `R`, then `∑ n, c_n (x-a)^n` converges absolutely at `x`. -/
theorem FormalPowerSeriesCenteredAt.converges_absolutely_inside_radius {a x : ℝ}
    (f : FormalPowerSeriesCenteredAt a)
    (hx : ENNReal.ofReal |x - a| < f.radiusOfConvergence) :
    Summable (fun n : ℕ => |f.coeff n * (x - a) ^ n|) :=
  by
    let r : NNReal := ⟨|x - a|, abs_nonneg (x - a)⟩
    let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ f.coeff
    have hcoer : ENNReal.ofReal |x - a| = (r : ENNReal) := by
      simpa [r] using (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg (x - a)))
    have hRadiusEq : f.radiusOfConvergence = p.radius := by
      simpa [p] using FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius f
    have hr : (r : ENNReal) < p.radius := by
      have hx' : ENNReal.ofReal |x - a| < p.radius := by
        simpa [hRadiusEq] using hx
      rw [hcoer] at hx'
      exact hx'
    have hsNorm : Summable (fun n : ℕ => ‖p n‖ * (r : ℝ) ^ n) :=
      p.summable_norm_mul_pow hr
    have hsNorm' : Summable (fun n : ℕ => ‖f.coeff n‖ * ‖x - a‖ ^ n) := by
      simpa [p, r, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using hsNorm
    simpa [Real.norm_eq_abs, abs_mul, abs_pow] using hsNorm'

/-- Theorem 4.1.3: (Uniform convergence on compact subintervals) for a power series centered at `a`, if `0 < r < R` (with `R` the radius of convergence), then the partial sums converge uniformly on `[a-r, a+r]` to the series sum; in particular, the sum function is continuous at every point where `|x-a| < R`. -/
theorem FormalPowerSeriesCenteredAt.uniformly_converges_on_compact_subintervals {a r : ℝ}
    (f : FormalPowerSeriesCenteredAt a)
    (hr0 : 0 < r)
    (hrR : ENNReal.ofReal r < f.radiusOfConvergence) :
    TendstoUniformlyOn
        (fun N x => (Finset.range N).sum (fun n => f.coeff n * (x - a) ^ n))
        (fun x => ∑' n, f.coeff n * (x - a) ^ n)
        Filter.atTop
        (Set.Icc (a - r) (a + r))
      ∧
      ∀ x : ℝ,
        ENNReal.ofReal |x - a| < f.radiusOfConvergence →
          ContinuousAt (fun y => ∑' n, f.coeff n * (y - a) ^ n) x := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ f.coeff
  have hRadiusEq : f.radiusOfConvergence = p.radius := by
    simpa [p] using FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius f
  have hRpos : 0 < f.radiusOfConvergence :=
    lt_trans (ENNReal.ofReal_pos.mpr hr0) hrR
  have hpPos : 0 < p.radius := by
    simpa [hRadiusEq] using hRpos
  have hShifted : HasFPowerSeriesOnBall (fun x : ℝ => p.sum (x - a)) p a p.radius :=
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_shiftedHasFPowerSeriesOnBall p hpPos
  rcases FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_existsStrictIntermediateRadius f hrR with
      ⟨ρ, hρleft, hρright⟩
  have hrρ : r < (ρ : ℝ) :=
    (ENNReal.ofReal_lt_coe_iff (le_of_lt hr0)).1 hρleft
  have hρlt : (ρ : ENNReal) < p.radius := by
    simpa [hRadiusEq] using hρright
  have hUniformBall : TendstoUniformlyOn
      (fun N x => p.partialSum N (x - a))
      (fun x => p.sum (x - a))
      Filter.atTop
      (Metric.ball a (ρ : ℝ)) :=
    hShifted.tendstoUniformlyOn' hρlt
  have hSubset : Set.Icc (a - r) (a + r) ⊆ Metric.ball a (ρ : ℝ) :=
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_Icc_subset_ball hrρ
  have hUniformIcc : TendstoUniformlyOn
      (fun N x => p.partialSum N (x - a))
      (fun x => p.sum (x - a))
      Filter.atTop
      (Set.Icc (a - r) (a + r)) :=
    hUniformBall.mono hSubset
  have hRewrite := FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_rewriteSeriesForms f
  have hUniformTarget : TendstoUniformlyOn
      (fun N x => (Finset.range N).sum (fun n => f.coeff n * (x - a) ^ n))
      (fun x => ∑' n, f.coeff n * (x - a) ^ n)
      Filter.atTop
      (Set.Icc (a - r) (a + r)) := by
    rw [← hRewrite.1, ← hRewrite.2]
    exact hUniformIcc
  refine ⟨hUniformTarget, ?_⟩
  intro x hx
  exact FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_continuousAt_inside_radius f hx

/-- Helper for Theorem 4.1.4: identify the convergence-radius set with the corresponding emetric ball. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_ball_eq_insideRadiusSet
    {a : ℝ} (f : FormalPowerSeriesCenteredAt a) :
    EMetric.ball a (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius =
      {x : ℝ | ENNReal.ofReal |x - a| < f.radiusOfConvergence} := by
  ext x
  constructor
  · intro hx
    have hxDist : ENNReal.ofReal (dist x a) < (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius := by
      simpa [EMetric.mem_ball, edist_dist] using hx
    have hxAbs : ENNReal.ofReal |x - a| < (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius := by
      simpa [Real.dist_eq] using hxDist
    simpa [FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius] using hxAbs
  · intro hx
    have hxAbs : ENNReal.ofReal |x - a| < (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius := by
      simpa [FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius] using hx
    have hxDist : ENNReal.ofReal (dist x a) < (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius := by
      simpa [Real.dist_eq] using hxAbs
    simpa [EMetric.mem_ball, edist_dist] using hxDist

/-- Helper for Theorem 4.1.4: derivative power-series expansion on the convergence ball. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_derivHasFPowerSeriesOnBall
    {a : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hRpos : 0 < f.radiusOfConvergence) :
    HasFPowerSeriesOnBall
      (fun x => deriv (fun y => (FormalMultilinearSeries.ofScalars ℝ f.coeff).sum (y - a)) x)
      ((((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).compFormalMultilinearSeries
        ((FormalMultilinearSeries.ofScalars ℝ f.coeff).derivSeries)))
      a
      (FormalMultilinearSeries.ofScalars ℝ f.coeff).radius := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ f.coeff
  have hpPos : 0 < p.radius := by
    simpa [FormalPowerSeriesCenteredAt.radiusOfConvergence, p] using hRpos
  have hShifted : HasFPowerSeriesOnBall (fun x : ℝ => p.sum (x - a)) p a p.radius :=
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_shiftedHasFPowerSeriesOnBall p hpPos
  have hFDeriv : HasFPowerSeriesOnBall (fderiv ℝ (fun y : ℝ => p.sum (y - a))) p.derivSeries a p.radius :=
    hShifted.fderiv
  have hComp : HasFPowerSeriesOnBall
      (fun x => ((fderiv ℝ (fun y : ℝ => p.sum (y - a)) x) : ℝ →L[ℝ] ℝ) 1)
      ((((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).compFormalMultilinearSeries p.derivSeries))
      a p.radius :=
    ((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).comp_hasFPowerSeriesOnBall hFDeriv
  refine hComp.congr ?_
  intro x hx
  simpa [fderiv_deriv, p]

/-- Helper for Theorem 4.1.4: rewrite derivative-series partial sums in textbook coefficient form. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_rewriteDerivedPartialSums
    {a : ℝ} (f : FormalPowerSeriesCenteredAt a) :
    (fun N x =>
      ((((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).compFormalMultilinearSeries
        ((FormalMultilinearSeries.ofScalars ℝ f.coeff).derivSeries)).partialSum N (x - a)))
      =
    (fun N x =>
      (Finset.range N).sum (fun n => ((n + 1 : ℝ) * f.coeff (n + 1) * (x - a) ^ n)) ) := by
  funext N x
  simp [FormalMultilinearSeries.partialSum, smul_eq_mul, mul_comm]

/-- Helper for Theorem 4.1.4: differentiability of the power-series sum on its open convergence interval. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_differentiableOn_insideRadius
    {a : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hRpos : 0 < f.radiusOfConvergence) :
    DifferentiableOn ℝ
      (fun x => ∑' n, f.coeff n * (x - a) ^ n)
      {x : ℝ | ENNReal.ofReal |x - a| < f.radiusOfConvergence} := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ f.coeff
  have hpPos : 0 < p.radius := by
    simpa [p] using hRpos
  have hShifted : HasFPowerSeriesOnBall (fun x : ℝ => p.sum (x - a)) p a p.radius :=
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_shiftedHasFPowerSeriesOnBall p hpPos
  have hDiffOnBall : DifferentiableOn ℝ (fun x : ℝ => p.sum (x - a)) (EMetric.ball a p.radius) :=
    hShifted.differentiableOn
  have hRewrite := FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_rewriteSeriesForms f
  have hRewriteP : (fun x : ℝ => p.sum (x - a)) = (fun x => ∑' n, f.coeff n * (x - a) ^ n) := by
    simpa [p] using hRewrite.2
  have hBallEq : EMetric.ball a p.radius =
      {x : ℝ | ENNReal.ofReal |x - a| < f.radiusOfConvergence} := by
    simpa [p] using
      FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_ball_eq_insideRadiusSet (a := a) f
  rw [hRewriteP, hBallEq] at hDiffOnBall
  exact hDiffOnBall

/-- Theorem 4.1.4: (Term-by-term differentiation of a power series): if a power series centered at `a` has positive radius of convergence `R`, then its sum function is differentiable at every point `x` with `|x - a| < R`; moreover, for every `r` with `0 < r < R`, the derived series converges uniformly to the derivative on `[a - r, a + r]`. -/
theorem FormalPowerSeriesCenteredAt.term_by_term_differentiation_of_power_series {a : ℝ}
    (f : FormalPowerSeriesCenteredAt a)
    (hRpos : 0 < f.radiusOfConvergence) :
    DifferentiableOn ℝ
      (fun x => ∑' n, f.coeff n * (x - a) ^ n)
      {x : ℝ | ENNReal.ofReal |x - a| < f.radiusOfConvergence}
    ∧
      ∀ r : ℝ,
        0 < r →
          ENNReal.ofReal r < f.radiusOfConvergence →
            TendstoUniformlyOn
              (fun N x => (Finset.range N).sum (fun n => ((n + 1 : ℝ) * f.coeff (n + 1) * (x - a) ^ n))
              )
              (fun x => deriv (fun y => ∑' n, f.coeff n * (y - a) ^ n) x)
              Filter.atTop
              (Set.Icc (a - r) (a + r)) :=
by
  refine ⟨
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_differentiableOn_insideRadius
      (a := a) f hRpos,
    ?_⟩
  intro r hr0 hrR
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ f.coeff
  have hRadiusEq : f.radiusOfConvergence = p.radius := by
    simpa [p] using FormalPowerSeriesCenteredAt.radiusOfConvergence_eq_ofScalarsRadius f
  have hDerivSeriesBall : HasFPowerSeriesOnBall
      (fun x => deriv (fun y => p.sum (y - a)) x)
      ((((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).compFormalMultilinearSeries p.derivSeries))
      a
      p.radius := by
    simpa [p] using
      FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_derivHasFPowerSeriesOnBall
        (a := a) f hRpos
  rcases FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_existsStrictIntermediateRadius f hrR with
      ⟨ρ, hρleft, hρright⟩
  have hrρ : r < (ρ : ℝ) :=
    (ENNReal.ofReal_lt_coe_iff (le_of_lt hr0)).1 hρleft
  have hρlt : (ρ : ENNReal) < p.radius := by
    simpa [hRadiusEq] using hρright
  have hUniformBall : TendstoUniformlyOn
      (fun N x => ((((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).compFormalMultilinearSeries
        p.derivSeries).partialSum N (x - a)))
      (fun x => deriv (fun y => p.sum (y - a)) x)
      Filter.atTop
      (Metric.ball a (ρ : ℝ)) := by
    simpa using hDerivSeriesBall.tendstoUniformlyOn' hρlt
  have hSubset : Set.Icc (a - r) (a + r) ⊆ Metric.ball a (ρ : ℝ) :=
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_Icc_subset_ball hrρ
  have hUniformIcc : TendstoUniformlyOn
      (fun N x => ((((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).compFormalMultilinearSeries
        p.derivSeries).partialSum N (x - a)))
      (fun x => deriv (fun y => p.sum (y - a)) x)
      Filter.atTop
      (Set.Icc (a - r) (a + r)) :=
    hUniformBall.mono hSubset
  have hRewriteDerived :
      (fun N x => ((((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).compFormalMultilinearSeries
        p.derivSeries).partialSum N (x - a)))
      =
      (fun N x => (Finset.range N).sum
        (fun n => ((n + 1 : ℝ) * f.coeff (n + 1) * (x - a) ^ n))) := by
    simpa [p] using
      FormalPowerSeriesCenteredAt.helperForTheorem_4_1_4_rewriteDerivedPartialSums
        (a := a) f
  have hUniformIcc' : TendstoUniformlyOn
      (fun N x => (Finset.range N).sum (fun n => ((n + 1 : ℝ) * f.coeff (n + 1) * (x - a) ^ n)))
      (fun x => deriv (fun y => p.sum (y - a)) x)
      Filter.atTop
      (Set.Icc (a - r) (a + r)) := by
    rw [← hRewriteDerived]
    exact hUniformIcc
  have hRewrite := FormalPowerSeriesCenteredAt.helperForTheorem_4_1_3_rewriteSeriesForms f
  have hRewriteP : (fun x : ℝ => p.sum (x - a)) = (fun x => ∑' n, f.coeff n * (x - a) ^ n) := by
    simpa [p] using hRewrite.2
  have hDerivEq :
      (fun x => deriv (fun y => p.sum (y - a)) x)
      =
      (fun x => deriv (fun y => ∑' n, f.coeff n * (y - a) ^ n) x) := by
    funext x
    simpa [hRewriteP]
  rw [hDerivEq] at hUniformIcc'
  change TendstoUniformlyOn
      (fun N x => (Finset.range N).sum (fun n => ((n + 1 : ℝ) * f.coeff (n + 1) * (x - a) ^ n)))
      (fun x => deriv (fun y => ∑' n, f.coeff n * (y - a) ^ n) x)
      Filter.atTop
      (Set.Icc (a - r) (a + r))
  exact hUniformIcc'

/-- Helper for Theorem 4.1.5: endpoints of `Set.uIcc y z` satisfy the same radius bound inherited from the interval hypothesis. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_endpoint_radius_bounds
    {a y z : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hsub : Set.uIcc y z ⊆ {x : ℝ | ENNReal.ofReal |x - a| < f.radiusOfConvergence}) :
    ENNReal.ofReal |y - a| < f.radiusOfConvergence
      ∧ ENNReal.ofReal |z - a| < f.radiusOfConvergence := by
  exact ⟨hsub Set.left_mem_uIcc, hsub Set.right_mem_uIcc⟩

/-- Helper for Theorem 4.1.5: every point of `Set.uIcc y z` has distance to `a` bounded by the maximum endpoint distance. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_abs_sub_le_maxEndpoint
    {a y z x : ℝ} (hx : x ∈ Set.uIcc y z) :
    |x - a| ≤ max |y - a| |z - a| := by
  rcases Set.mem_uIcc.mp hx with hxy | hxy
  · have hbase : |x - a| ≤ max (z - a) (a - y) :=
      abs_sub_le_max_sub hxy.1 hxy.2 a
    have hz : z - a ≤ |z - a| := le_abs_self (z - a)
    have hy : a - y ≤ |y - a| := by
      have hy' : -(y - a) ≤ |y - a| := neg_le_abs (y - a)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy'
    have hmax : max (z - a) (a - y) ≤ max |y - a| |z - a| := by
      exact max_le_iff.mpr
        ⟨le_trans hz (le_max_right |y - a| |z - a|),
          le_trans hy (le_max_left |y - a| |z - a|)⟩
    exact le_trans hbase hmax
  · have hbase : |x - a| ≤ max (y - a) (a - z) :=
      abs_sub_le_max_sub hxy.1 hxy.2 a
    have hy : y - a ≤ |y - a| := le_abs_self (y - a)
    have hz : a - z ≤ |z - a| := by
      have hz' : -(z - a) ≤ |z - a| := neg_le_abs (z - a)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz'
    have hmax : max (y - a) (a - z) ≤ max |y - a| |z - a| := by
      exact max_le_iff.mpr
        ⟨le_trans hy (le_max_left |y - a| |z - a|),
          le_trans hz (le_max_right |y - a| |z - a|)⟩
    exact le_trans hbase hmax

/-- Helper for Theorem 4.1.5: each monomial term `x ↦ c_n (x-a)^n` is continuous. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_term_continuous
    {a : ℝ} (f : FormalPowerSeriesCenteredAt a) (n : ℕ) :
    Continuous (fun x : ℝ => f.coeff n * (x - a) ^ n) := by
  continuity

/-- Helper for Theorem 4.1.5: package the `n`th term as a continuous map on `ℝ`. -/
noncomputable def FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap
    {a : ℝ} (f : FormalPowerSeriesCenteredAt a) (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun x => f.coeff n * (x - a) ^ n,
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_term_continuous (a := a) f n⟩

/-- Helper for Theorem 4.1.5: the supremum norms of restricted terms on `Set.uIcc y z` form a summable series. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_summable_restrictedTermNorms
    {a y z : ℝ} (f : FormalPowerSeriesCenteredAt a)
    (hsub : Set.uIcc y z ⊆ {x : ℝ | ENNReal.ofReal |x - a| < f.radiusOfConvergence}) :
    Summable (fun n : ℕ =>
      ‖(FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap (a := a) f n).restrict
        (⟨Set.uIcc y z, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
  let r : ℝ := max |y - a| |z - a|
  have hr_nonneg : 0 ≤ r :=
    le_trans (abs_nonneg (y - a)) (le_max_left |y - a| |z - a|)
  have hEndpoints :=
    FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_endpoint_radius_bounds
      (a := a) (y := y) (z := z) f hsub
  have hr_lt_radius : ENNReal.ofReal r < f.radiusOfConvergence := by
    have hmaxENN : max (ENNReal.ofReal |y - a|) (ENNReal.ofReal |z - a|) < f.radiusOfConvergence :=
      max_lt_iff.mpr hEndpoints
    simpa [r, ENNReal.ofReal_max] using hmaxENN
  have hx_at_r : ENNReal.ofReal |(a + r) - a| < f.radiusOfConvergence := by
    have hSub : (a + r) - a = r := by ring
    calc
      ENNReal.ofReal |(a + r) - a| = ENNReal.ofReal |r| := by simp [hSub]
      _ = ENNReal.ofReal r := by simp [abs_of_nonneg hr_nonneg]
      _ < f.radiusOfConvergence := hr_lt_radius
  have hsAbs : Summable (fun n : ℕ => |f.coeff n * ((a + r) - a) ^ n|) :=
    FormalPowerSeriesCenteredAt.converges_absolutely_inside_radius (a := a) (x := a + r) f hx_at_r
  have hsMajorant : Summable (fun n : ℕ => |f.coeff n| * r ^ n) := by
    have hsAbs' : Summable (fun n : ℕ => |f.coeff n * r ^ n|) := by
      have hEqSeries : (fun n : ℕ => |f.coeff n * ((a + r) - a) ^ n|)
          = (fun n : ℕ => |f.coeff n * r ^ n|) := by
        funext n
        have hSub : (a + r) - a = r := by ring
        rw [hSub]
      rw [← hEqSeries]
      exact hsAbs
    have hEqSeries' : (fun n : ℕ => |f.coeff n * r ^ n|) = (fun n : ℕ => |f.coeff n| * r ^ n) := by
      funext n
      have hrpow_nonneg : 0 ≤ r ^ n := pow_nonneg hr_nonneg n
      simp [abs_mul, abs_of_nonneg hrpow_nonneg]
    rw [← hEqSeries']
    exact hsAbs'
  let K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc y z, isCompact_uIcc⟩
  have hbound : ∀ n : ℕ,
      ‖(FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap (a := a) f n).restrict K‖
        ≤ |f.coeff n| * r ^ n := by
    intro n
    refine (ContinuousMap.norm_le
      (f := (FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap (a := a) f n).restrict K)
      (C0 := mul_nonneg (abs_nonneg _) (pow_nonneg hr_nonneg _))).2 ?_
    intro x
    have hxK : (x : ℝ) ∈ Set.uIcc y z := x.2
    have hx_le : |(x : ℝ) - a| ≤ r := by
      simpa [r] using
        FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_abs_sub_le_maxEndpoint
          (a := a) (y := y) (z := z) hxK
    have hpow : |(x : ℝ) - a| ^ n ≤ r ^ n :=
      pow_le_pow_left₀ (abs_nonneg ((x : ℝ) - a)) hx_le n
    have hmul : |f.coeff n| * |(x : ℝ) - a| ^ n ≤ |f.coeff n| * r ^ n :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg (f.coeff n))
    calc
      ‖(FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap (a := a) f n).restrict K x‖
        = |f.coeff n * ((x : ℝ) - a) ^ n| := by
          rfl
      _ = |f.coeff n| * |(x : ℝ) - a| ^ n := by
          simp [abs_mul, abs_pow]
      _ ≤ |f.coeff n| * r ^ n := hmul
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsMajorant

/-- Helper for Theorem 4.1.5: the interval integral of each term has the textbook antiderivative form. -/
lemma FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_intervalIntegral_term_formula
    {a y z : ℝ} (f : FormalPowerSeriesCenteredAt a) (n : ℕ) :
    (∫ x in y..z, f.coeff n * (x - a) ^ n)
      = f.coeff n * (((z - a) ^ (n + 1) - (y - a) ^ (n + 1)) / (n + 1 : ℝ)) := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => t ^ n) a]
  simp [integral_pow, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Theorem 4.1.5: (Term-by-term integration of a power series) let `f(x) = ∑' n, c_n (x-a)^n` be a power series with positive radius of convergence; for any closed interval `[y, z]` contained in the convergence region, `∫ x in y..z, f x` equals the term-by-term antiderivative series evaluated at `z` and `y`. -/
theorem FormalPowerSeriesCenteredAt.term_by_term_integration_of_power_series {a y z : ℝ}
    (f : FormalPowerSeriesCenteredAt a)
    (hRpos : 0 < f.radiusOfConvergence)
    (hsub : Set.uIcc y z ⊆ {x : ℝ | ENNReal.ofReal |x - a| < f.radiusOfConvergence}) :
    (∫ x in y..z, (∑' n : ℕ, f.coeff n * (x - a) ^ n)) =
      ∑' n : ℕ,
        f.coeff n * (((z - a) ^ (n + 1) - (y - a) ^ (n + 1)) / (n + 1 : ℝ)) :=
by
  have _ : 0 < f.radiusOfConvergence := hRpos
  let g : ℕ → C(ℝ, ℝ) :=
    fun n => FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap (a := a) f n
  have hsumEq :
      (fun x : ℝ => ∑' n : ℕ, f.coeff n * (x - a) ^ n) =
        (fun x : ℝ => ∑' n : ℕ, g n x) := by
    funext x
    simp [g, FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap]
  have hSummableNorm : Summable (fun n : ℕ =>
      ‖(g n).restrict (⟨Set.uIcc y z, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
    simpa [g] using
      FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_summable_restrictedTermNorms
        (a := a) (y := y) (z := z) f hsub
  have hInterchange :
      (∫ x in y..z, (∑' n : ℕ, g n x)) = (∑' n : ℕ, ∫ x in y..z, g n x) := by
    have hEq : (∑' n : ℕ, ∫ x in y..z, g n x) = ∫ x in y..z, ∑' n : ℕ, g n x :=
      intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (a := y) (b := z)
        (f := g) hSummableNorm
    exact hEq.symm
  calc
    (∫ x in y..z, (∑' n : ℕ, f.coeff n * (x - a) ^ n))
      = (∫ x in y..z, (∑' n : ℕ, g n x)) := by simpa [hsumEq]
    _ = (∑' n : ℕ, ∫ x in y..z, g n x) := hInterchange
    _ = ∑' n : ℕ,
          f.coeff n * (((z - a) ^ (n + 1) - (y - a) ^ (n + 1)) / (n + 1 : ℝ)) := by
        refine tsum_congr ?_
        intro n
        simpa [g, FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_termContinuousMap] using
          FormalPowerSeriesCenteredAt.helperForTheorem_4_1_5_intervalIntegral_term_formula
            (a := a) (y := y) (z := z) f n

end Section01
end Chap04
