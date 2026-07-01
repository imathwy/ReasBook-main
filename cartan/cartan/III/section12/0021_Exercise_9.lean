import Mathlib
import cartan.III.section12.CircleSupNorm
import cartan.II.section06.«0010_Theorem_3»
import cartan.III.section07.«0001_Remark_III_1_extra_1»

-- Semantic recall tool `lean_leansearch` was unavailable in this environment; I used local
-- Mathlib source inspection instead for `Real.circleAverage`, `ContinuousOn.circleAverage`,
-- `AnalyticOnNhd`, and `HasFPowerSeriesOnBall`.

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Metric Real Set Filter
open scoped Topology BigOperators

variable {F : Type*} [NormedAddCommGroup F]

/-- The mean square of `f` on the centered circle of radius `r`. -/
noncomputable def circle_mean_sq (f : ℂ → F) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ ↦ ‖f z‖ ^ (2 : ℕ)) 0 r

/-- Helper for Exercise 9: the mean square is always nonnegative. -/
lemma circle_mean_sq_nonneg (f : ℂ → F) (r : ℝ) : 0 ≤ circle_mean_sq f r := by
  -- The integrand is pointwise nonnegative on every circle.
  unfold circle_mean_sq
  exact Real.circleAverage_nonneg_of_nonneg fun z _ ↦ pow_nonneg (norm_nonneg (f z)) 2

/-- Helper for Exercise 9: at radius `0`, the mean square is the squared norm of the
center value. -/
lemma circle_mean_sq_zero_radius (f : ℂ → F) : circle_mean_sq f 0 = ‖f 0‖ ^ (2 : ℕ) := by
  -- The radius-zero circle average collapses to evaluation at the center.
  simp [circle_mean_sq]

/-- Helper for Exercise 9: summing monomials over `range N` produces the expected coefficient. -/
lemma coeff_sum_range_monomial
    (c : ℕ → ℂ) (N k : ℕ) :
    (Finset.sum (Finset.range N) fun n ↦ Polynomial.monomial n (c n)).coeff k =
      if k < N then c k else 0 := by
  induction N with
  | zero =>
      -- There are no monomials in the empty truncation.
      simp
  | succ N ih =>
      have hnot : N ∉ Finset.range N := by simp
      rw [Finset.range_add_one, Finset.sum_insert hnot, Polynomial.coeff_add]
      by_cases hkN : k < N
      · -- Inside the old range, the new top monomial does not contribute.
        have hNk : N ≠ k := by
          exact Nat.ne_of_gt hkN
        rw [ih, if_pos hkN]
        have hmono : ((Polynomial.monomial N (c N)).coeff k) = 0 := by
          simp [Polynomial.coeff_monomial, hNk]
        rw [hmono]
        simp [Nat.lt_trans hkN (Nat.lt_succ_self N)]
      · by_cases hk_eq : k = N
        · -- At the new top index, only the last monomial contributes.
          subst hk_eq
          simp [ih]
        · -- Beyond the truncation, both the old sum and the new monomial vanish.
          have hNk : N ≠ k := by
            intro h
            exact hk_eq h.symm
          have hk_gt : N < k := lt_of_le_of_ne (Nat.le_of_not_lt hkN) hNk
          rw [ih, if_neg hkN]
          have hmono : ((Polynomial.monomial N (c N)).coeff k) = 0 := by
            simp [Polynomial.coeff_monomial, hNk]
          rw [hmono]
          simp [Nat.not_lt.mpr (Nat.succ_le_of_lt hk_gt)]

/-- Helper for Exercise 9: Parseval's polynomial identity can be rewritten over `Finset.range N`
when the support is already contained there. -/
lemma polynomial_sum_sq_norm_coeff_eq_circleAverage_range
    (p : Polynomial ℂ) (N : ℕ) (hsupp : p.support ⊆ Finset.range N) :
    Real.circleAverage (fun z : ℂ ↦ ‖p.eval z‖ ^ (2 : ℕ)) 0 1 =
      Finset.sum (Finset.range N) fun n ↦ ‖p.coeff n‖ ^ (2 : ℕ) := by
  have hsupport_eq :
      p.support = (Finset.range N).filter fun n ↦ p.coeff n ≠ 0 := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Polynomial.mem_support_iff]
    constructor
    · intro hn
      exact ⟨Finset.mem_range.mp (hsupp (Polynomial.mem_support_iff.mpr hn)), hn⟩
    · intro hn
      exact hn.2
  -- Start from the support-indexed Parseval identity already in mathlib.
  calc
    Real.circleAverage (fun z : ℂ ↦ ‖p.eval z‖ ^ (2 : ℕ)) 0 1 =
        ∑ n ∈ p.support, ‖p.coeff n‖ ^ (2 : ℕ) := by
          simpa using p.sum_sq_norm_coeff_eq_circleAverage.symm
    _ = Finset.sum (Finset.range N) fun n ↦ ‖p.coeff n‖ ^ (2 : ℕ) := by
          rw [hsupport_eq, Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro n hn
          by_cases hcoeff : p.coeff n = 0
          · simp [hcoeff]
          · simp [hcoeff]

/-- Helper for Exercise 9: the truncated power series already satisfies the mean-square identity. -/
lemma circle_mean_sq_partial_sum_eq_sum_sq_norm
    (a : ℕ → ℂ) (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    circle_mean_sq (fun z ↦ Finset.sum (Finset.range N) fun n ↦ a n * z ^ n) r =
      Finset.sum (Finset.range N) fun n ↦ ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := by
  let q : Polynomial ℂ :=
    Finset.sum (Finset.range N) fun n ↦ Polynomial.monomial n (a n * (r : ℂ) ^ n)
  have hq_eval :
      ∀ z : ℂ, q.eval z = Finset.sum (Finset.range N) fun n ↦ a n * (r * z) ^ n := by
    intro z
    -- Route correction: package the truncation as one scaled polynomial before applying Parseval.
    simp [q, Polynomial.eval_finsetSum, mul_pow, mul_left_comm, mul_comm]
  have hq_support : q.support ⊆ Finset.range N := by
    intro k hk
    by_contra hkN
    have hknlt : ¬ k < N := by
      simpa [Finset.mem_range] using hkN
    have hcoeff : q.coeff k = 0 := by
      rw [show q.coeff k =
          ite (k < N) (a k * (r : ℂ) ^ k) 0 by
            simpa [q] using coeff_sum_range_monomial
              (fun n ↦ a n * (r : ℂ) ^ n) N k]
      exact if_neg hknlt
    exact (Polynomial.mem_support_iff.mp hk) hcoeff
  calc
    circle_mean_sq (fun z ↦ Finset.sum (Finset.range N) fun n ↦ a n * z ^ n) r
      = Real.circleAverage (fun z : ℂ ↦ ‖q.eval z‖ ^ (2 : ℕ)) 0 1 := by
          -- Rewrite the radius-`r` average as a unit-circle average of the scaled polynomial.
          unfold circle_mean_sq
          rw [Real.circleAverage_eq_circleAverage_zero_one]
          congr with z
          simpa [hq_eval z]
    _ = Finset.sum (Finset.range N) fun n ↦ ‖q.coeff n‖ ^ (2 : ℕ) := by
          exact polynomial_sum_sq_norm_coeff_eq_circleAverage_range q N hq_support
    _ = Finset.sum (Finset.range N) fun n ↦ ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := by
          -- On `range N`, the scaled polynomial coefficients are exactly `a n * r^n`.
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [show q.coeff n =
              ite (n < N) (a n * (r : ℂ) ^ n) 0 by
                simpa [q] using coeff_sum_range_monomial
                  (fun m ↦ a m * (r : ℂ) ^ m) N n]
          rw [if_pos (Finset.mem_range.mp hn)]
          calc
            ‖a n * (r : ℂ) ^ n‖ ^ (2 : ℕ) = (‖a n‖ * r ^ n) ^ (2 : ℕ) := by
              simp [norm_mul, Complex.norm_pow, Complex.norm_real, abs_of_nonneg hr0]
            _ = ‖a n‖ ^ (2 : ℕ) * (r ^ n) ^ (2 : ℕ) := by rw [mul_pow]
            _ = ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := by
              simp [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Helper for Exercise 9: uniform convergence on a fixed circle transports to uniform convergence
of the squared norms. -/
lemma tendstoUniformlyOn_sq_norm_of_tendstoUniformlyOn_sphere
    {u : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {r : ℝ}
    (hr0 : 0 ≤ r)
    (hcontf : ContinuousOn f (sphere (0 : ℂ) r))
    (hlim : TendstoUniformlyOn u f atTop (sphere (0 : ℂ) r)) :
    TendstoUniformlyOn (fun N z ↦ ‖u N z‖ ^ (2 : ℕ)) (fun z ↦ ‖f z‖ ^ (2 : ℕ))
      atTop (sphere (0 : ℂ) r) := by
  rcases IsCompact.exists_bound_of_continuousOn (isCompact_sphere (0 : ℂ) r) hcontf.norm with
    ⟨C, hC⟩
  let B : ℝ := max C 0
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_max_right _ _
  have hB : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ B := by
    intro z hz
    have hzC : ‖‖f z‖‖ ≤ C := hC z hz
    calc
      ‖f z‖ = ‖‖f z‖‖ := by simp
      _ ≤ C := hzC
      _ ≤ B := by
        dsimp [B]
        exact le_max_left _ _
  -- Compare squared norms through the factorization `a² - b² = (a - b) (a + b)`.
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  let δ : ℝ := min 1 (ε / (2 * (2 * B + 1)))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    positivity
  have hδle_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  have hden_pos : 0 < 2 * B + 1 := by
    positivity
  have hδmul_le : δ * (2 * B + 1) ≤ ε / 2 := by
    have hδle : δ ≤ ε / (2 * (2 * B + 1)) := by
      dsimp [δ]
      exact min_le_right _ _
    calc
      δ * (2 * B + 1) ≤ (ε / (2 * (2 * B + 1))) * (2 * B + 1) := by
        gcongr
      _ = ε / 2 := by
        field_simp [hden_pos.ne']
  refine (hlim δ hδpos).mono ?_
  intro N hN z hz
  have hdist : ‖u N z - f z‖ < δ := by
    simpa [dist_eq_norm, norm_sub_rev] using hN z hz
  have hnormdiff : |‖u N z‖ - ‖f z‖| ≤ ‖u N z - f z‖ :=
    abs_norm_sub_norm_le (u N z) (f z)
  have hu_le : ‖u N z‖ ≤ ‖u N z - f z‖ + ‖f z‖ := by
    calc
      ‖u N z‖ = ‖(u N z - f z) + f z‖ := by abel_nf
      _ ≤ ‖u N z - f z‖ + ‖f z‖ := norm_add_le _ _
  have hsum_le : ‖u N z‖ + ‖f z‖ ≤ 2 * B + 1 := by
    nlinarith [hu_le, hB z hz, le_of_lt hdist, hδle_one]
  have hsq_le : |‖u N z‖ ^ (2 : ℕ) - ‖f z‖ ^ (2 : ℕ)| ≤ δ * (2 * B + 1) := by
    calc
      |‖u N z‖ ^ (2 : ℕ) - ‖f z‖ ^ (2 : ℕ)| =
          |‖u N z‖ - ‖f z‖| * (‖u N z‖ + ‖f z‖) := by
            rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
              mul_comm]
      _ ≤ ‖u N z - f z‖ * (2 * B + 1) := by
            exact (mul_le_mul_of_nonneg_right hnormdiff
              (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans
              (mul_le_mul_of_nonneg_left hsum_le (norm_nonneg _))
      _ ≤ δ * (2 * B + 1) := by
            exact mul_le_mul_of_nonneg_right (le_of_lt hdist) (by positivity)
  have hεhalf_lt : ε / 2 < ε := by
    nlinarith
  exact lt_of_le_of_lt (by simpa [Real.dist_eq, abs_sub_comm] using hsq_le)
    (lt_of_le_of_lt hδmul_le hεhalf_lt)

/-- Helper for Exercise 9: on a fixed circle strictly inside the convergence disk, the mean
squares of the Taylor partial sums converge to the mean square of the function itself. -/
lemma circle_mean_sq_partial_sums_tendsto
    {f : ℂ → ℂ} {R r : ℝ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (.ofScalars ℂ a) 0 (ENNReal.ofReal R))
    (hr0 : 0 ≤ r) (hrR : r < R) :
    Tendsto (fun N ↦ circle_mean_sq (fun z ↦ Finset.sum (Finset.range N) fun n ↦ a n * z ^ n) r)
      atTop (𝓝 (circle_mean_sq f r)) := by
  obtain ⟨ρ, hrρ, hρR⟩ := exists_between hrR
  have hρ0 : 0 ≤ ρ := le_trans hr0 hrρ.le
  have hρENN : ENNReal.ofReal ρ < ENNReal.ofReal R := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρ0).2 hρR
  have hsub : sphere (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) ρ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hz_norm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    linarith [hz_norm]
  have hball :
      TendstoUniformlyOn
        (fun N z ↦ Finset.sum (Finset.range N) fun n ↦ a n * z ^ n)
        f atTop (Metric.ball (0 : ℂ) ρ) := by
    -- The Taylor partial sums converge uniformly on every strict subdisk.
    simpa [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
      zero_sub, sub_zero, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using
        (hf.tendstoUniformlyOn' (r' := ⟨ρ, hρ0⟩)
          (by simpa [ENNReal.ofReal_eq_coe_nnreal hρ0] using hρENN))
  have hsphere :
      TendstoUniformlyOn
        (fun N z ↦ Finset.sum (Finset.range N) fun n ↦ a n * z ^ n)
        f atTop (sphere (0 : ℂ) r) :=
    hball.mono hsub
  have hcont_partial_sphere :
      ∀ᶠ N in atTop,
        ContinuousOn (fun z : ℂ ↦ Finset.sum (Finset.range N) fun n ↦ a n * z ^ n)
          (sphere (0 : ℂ) r) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    have hcont_sum :
        Continuous fun z : ℂ ↦ Finset.sum (Finset.range N) fun n ↦ a n * z ^ n := by
      refine continuous_finsetSum _ ?_
      intro n hn
      exact continuous_const.mul (continuous_id.pow n)
    exact hcont_sum.continuousOn
  have hcontf_sphere : ContinuousOn f (sphere (0 : ℂ) r) :=
    hsphere.continuousOn hcont_partial_sphere.frequently
  have hsq_sphere :
      TendstoUniformlyOn
        (fun N z ↦
          ‖(Finset.sum (Finset.range N) fun n ↦ a n * z ^ n)‖ ^ (2 : ℕ))
        (fun z ↦ ‖f z‖ ^ (2 : ℕ)) atTop (sphere (0 : ℂ) r) :=
    tendstoUniformlyOn_sq_norm_of_tendstoUniformlyOn_sphere hr0 hcontf_sphere hsphere
  let Fθ : ℕ → ℝ → ℝ :=
    fun N θ ↦ ‖(Finset.sum (Finset.range N) fun n ↦ a n * (circleMap 0 r θ) ^ n)‖ ^ (2 : ℕ)
  let Gθ : ℝ → ℝ := fun θ ↦ ‖f (circleMap 0 r θ)‖ ^ (2 : ℕ)
  have hθ :
      TendstoUniformlyOn Fθ Gθ atTop (Set.uIcc (0 : ℝ) (2 * π)) := by
    -- Restrict the boundary convergence to the angle parametrization of the circle.
    refine (hsq_sphere.comp (circleMap 0 r)).mono ?_
    intro θ hθmem
    simpa [Fθ, Gθ, abs_of_nonneg hr0] using circleMap_mem_sphere (0 : ℂ) hr0 θ
  have hcont_Fθ :
      ∀ᶠ N in atTop, ContinuousOn (Fθ N) (Set.uIcc (0 : ℝ) (2 * π)) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    have hcont_sum :
        Continuous fun θ : ℝ ↦
          Finset.sum (Finset.range N) fun n ↦ a n * (circleMap 0 r θ) ^ n := by
      refine continuous_finsetSum _ ?_
      intro n hn
      exact continuous_const.mul ((continuous_circleMap 0 r).pow n)
    exact hcont_sum.norm.pow 2 |>.continuousOn
  have hInt :
      Tendsto (fun N ↦ ∫ θ in 0..2 * π, Fθ N θ)
        atTop (𝓝 (∫ θ in 0..2 * π, Gθ θ)) :=
    hθ.tendsto_intervalIntegral_of_continuousOn hcont_Fθ
  have hAvg :
      Tendsto (fun N ↦ ((2 * π)⁻¹ : ℝ) • ∫ θ in 0..2 * π, Fθ N θ)
        atTop (𝓝 (((2 * π)⁻¹ : ℝ) • ∫ θ in 0..2 * π, Gθ θ)) :=
    tendsto_const_nhds.smul hInt
  -- Rewrite the mean square as the interval average of the boundary squared norm.
  simpa [circle_mean_sq, Fθ, Gθ, Real.circleAverage]
    using hAvg

/-- Helper for Exercise 9: an analytic function on the disc `‖z‖ < R` admits one fixed scalar
power-series expansion centered at `0` on the whole disc. -/
lemma analyticOnNhd_origin_power_series
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hR : 0 < R) :
    ∃ a : ℕ → ℂ, HasFPowerSeriesOnBall f (.ofScalars ℂ a) 0 (ENNReal.ofReal R) := by
  -- Use the disc-wide expansion theorem once so all later corollaries share the same coefficients.
  exact holomorphic_on_disc_has_power_series_expansion hR hf.differentiableOn

/-- Helper for Exercise 9: the coefficient formula from Exercise 9 is naturally packaged as a
`HasSum` statement. -/
lemma circle_mean_sq_hasSum_sq_norm_taylor_coeff
    {f : ℂ → ℂ} {R r : ℝ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (.ofScalars ℂ a) 0 (ENNReal.ofReal R))
    (hr0 : 0 ≤ r) (hrR : r < R) :
    HasSum (fun n : ℕ ↦ ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n)) (circle_mean_sq f r) := by
  -- The source route is: finite Parseval on each truncation, then identify the limit of those
  -- finite sums with the target mean square.
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · refine Filter.Tendsto.congr' ?_ (circle_mean_sq_partial_sums_tendsto hf hr0 hrR)
    refine Filter.Eventually.of_forall ?_
    intro N
    simpa using circle_mean_sq_partial_sum_eq_sum_sq_norm a N hr0
  · intro n
    positivity

/-- Exercise 9 (1): if `f` has Taylor coefficients `a n` at `0` on the disc `‖z‖ < R`, then its
mean square on the centered circle of radius `r` is the sum of `‖a n‖² r^(2 n)`. -/
theorem circle_mean_sq_eq_tsum_sq_norm_taylor_coeff
    {f : ℂ → ℂ} {R r : ℝ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (.ofScalars ℂ a) 0 (ENNReal.ofReal R))
    (hr0 : 0 ≤ r) (hrR : r < R) :
    circle_mean_sq f r = ∑' n : ℕ, ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := by
  -- Rewrite the established `HasSum` package as the usual infinite-sum identity.
  simpa using (circle_mean_sq_hasSum_sq_norm_taylor_coeff hf hr0 hrR).tsum_eq.symm

/-- Exercise 9 (2): on `0 ≤ r < R`, the mean-square function `I₂(r)` is continuous in `r`. -/
theorem circle_mean_sq_continuousOn
    {f : ℂ → F} {R : ℝ}
    (hf : ContinuousOn f (ball (0 : ℂ) R)) :
    ContinuousOn (circle_mean_sq f) (Set.Ico (0 : ℝ) R) := by
  have hcont : ContinuousOn (fun z : ℂ ↦ ‖f z‖ ^ (2 : ℕ)) {z : ℂ | ‖z - 0‖ ∈ Ico (0 : ℝ) R} := by
    simpa [ball, Set.mem_setOf_eq] using hf.norm.pow 2
  simpa [circle_mean_sq] using hcont.circleAverage fun _ hr ↦ hr.1

/-- Analytic functions on `‖z‖ < R` satisfy the continuity hypothesis for
`circle_mean_sq_continuousOn`. -/
theorem circle_mean_sq_continuousOn_of_analyticOnNhd
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R)) :
    ContinuousOn (circle_mean_sq f) (Set.Ico (0 : ℝ) R) :=
  circle_mean_sq_continuousOn hf.continuousOn

/-- Exercise 9 (3): on `0 ≤ r < R`, the mean-square function `I₂(r)` is monotone increasing. -/
theorem circle_mean_sq_monotoneOn
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R)) :
    MonotoneOn (circle_mean_sq f) (Set.Ico (0 : ℝ) R) := by
  intro r hr s hs hrs
  have hR : 0 < R := lt_of_le_of_lt hs.1 hs.2
  rcases analyticOnNhd_origin_power_series hf hR with ⟨a, ha⟩
  have hsum_r := circle_mean_sq_hasSum_sq_norm_taylor_coeff ha hr.1 hr.2
  have hsum_s := circle_mean_sq_hasSum_sq_norm_taylor_coeff ha hs.1 hs.2
  -- Compare the two radii termwise after rewriting both means with the same coefficient family.
  rw [← hsum_r.tsum_eq, ← hsum_s.tsum_eq]
  exact Summable.tsum_le_tsum
    (fun n ↦
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hr.1 hrs (2 * n))
        (by positivity : 0 ≤ ‖a n‖ ^ (2 : ℕ)))
    hsum_r.summable hsum_s.summable

/-- Helper for Exercise 9: a nonzero analytic function on the disc has some nonzero Taylor
coefficient in the fixed expansion at `0`. -/
lemma exists_taylor_coeff_ne_zero_of_not_eqOn_zero
    {f : ℂ → ℂ} {R : ℝ} {a : ℕ → ℂ}
    (ha : HasFPowerSeriesOnBall f (.ofScalars ℂ a) 0 (ENNReal.ofReal R))
    (hfnz : ¬ EqOn f 0 (ball (0 : ℂ) R)) :
    ∃ n : ℕ, a n ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  apply hfnz
  intro z hz
  have hz' : z ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal R) := by
    simpa [Metric.eball_ofReal] using hz
  have hseries_z : HasSum (fun n : ℕ ↦ z ^ n * a n) (f z) := by
    -- Evaluate the fixed scalar power series at the point `z` inside the disc.
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, mul_comm] using ha.hasSum hz'
  have hsum_z : HasSum (fun n : ℕ ↦ (0 : ℂ)) (f z) := by
    -- Every coefficient vanishes, so the scalar series on the disc collapses termwise to zero.
    convert hseries_z using 1
    funext n
    simp [hzero n]
  exact hsum_z.unique hasSum_zero

/-- Helper for Exercise 9: a nontrivial nonnegative coefficient series has strictly positive sum
once one term is strictly positive. -/
lemma tsum_sq_norm_mul_pow_pos
    {a : ℕ → ℂ} {r : ℝ}
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n)))
    (hnz : ∃ n : ℕ, a n ≠ 0)
    (hr : 0 < r) :
    0 < ∑' n : ℕ, ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := by
  rcases hnz with ⟨n₀, hn₀⟩
  have hnonneg : ∀ n : ℕ, 0 ≤ ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := by
    intro n
    positivity
  have hterm_pos : 0 < ‖a n₀‖ ^ (2 : ℕ) * r ^ (2 * n₀) := by
    -- The chosen nonzero coefficient and the positive radius force one strictly positive term.
    exact mul_pos (pow_pos (norm_pos_iff.mpr hn₀) _) (pow_pos hr _)
  exact hsum.tsum_pos hnonneg n₀ hterm_pos

/-- Helper for Exercise 9: if `f` is not identically zero on `‖z‖ < R`, then every logarithmic
radius `s < log R` has strictly positive mean square `I₂(e^s)`. -/
lemma circle_mean_sq_comp_exp_pos_of_not_eqOn_zero
    {f : ℂ → ℂ} {R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hR : 0 < R)
    (hfnz : ¬ EqOn f 0 (ball (0 : ℂ) R))
    (hs : s < Real.log R) :
    0 < circle_mean_sq f (Real.exp s) := by
  rcases analyticOnNhd_origin_power_series hf hR with ⟨a, ha⟩
  have hanz : ∃ n : ℕ, a n ≠ 0 :=
    exists_taylor_coeff_ne_zero_of_not_eqOn_zero ha hfnz
  have hrR : Real.exp s < R := by
    calc
      Real.exp s < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hs
      _ = R := Real.exp_log hR
  have hsum :=
    circle_mean_sq_hasSum_sq_norm_taylor_coeff ha (Real.exp_pos s).le hrR
  -- Rewrite the mean square by the coefficient series and apply positivity of one term.
  rw [circle_mean_sq_eq_tsum_sq_norm_taylor_coeff ha (Real.exp_pos s).le hrR]
  exact tsum_sq_norm_mul_pow_pos hsum.summable hanz (Real.exp_pos s)

/-- Exercise 9 (4): on `0 ≤ r < R`, the mean square dominates `‖f 0‖²`. -/
theorem sq_norm_apply_zero_le_circle_mean_sq
    {f : ℂ → ℂ} {R r : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hr0 : 0 ≤ r) (hrR : r < R) :
    ‖f 0‖ ^ (2 : ℕ) ≤ circle_mean_sq f r := by
  have hR : 0 < R := lt_of_le_of_lt hr0 hrR
  have hmono := circle_mean_sq_monotoneOn hf
  have hzero_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) R := by
    exact ⟨le_rfl, hR⟩
  have hr_mem : r ∈ Set.Ico (0 : ℝ) R := ⟨hr0, hrR⟩
  -- Evaluate monotonicity between the left endpoint `0` and the target radius `r`.
  have hle : circle_mean_sq f 0 ≤ circle_mean_sq f r := hmono hzero_mem hr_mem hr0
  simpa [circle_mean_sq_zero_radius] using hle

/-- Exercise 9 (5): for `0 ≤ r`, the mean square of a function continuous on `‖z‖ = r` is bounded
above by the square of the circle supremum norm `M(r)`. -/
theorem circle_mean_sq_le_circleSupNorm_sq
    {f : ℂ → F} {r : ℝ}
    (hr0 : 0 ≤ r)
    (hcont : ContinuousOn f (sphere (0 : ℂ) r)) :
    circle_mean_sq f r ≤ circleSupNorm f r ^ (2 : ℕ) := by
  have hInt : CircleIntegrable (fun z : ℂ ↦ ‖f z‖ ^ (2 : ℕ)) 0 r := by
    exact (hcont.norm.pow 2).circleIntegrable hr0
  have hsup_nonneg : 0 ≤ circleSupNorm f r := by
    have hz : (r : ℂ) ∈ sphere (0 : ℂ) r := by
      simp [sub_zero, Complex.norm_real, abs_of_nonneg hr0]
    exact le_trans (norm_nonneg (f (r : ℂ))) (hcont.norm_le_circleSupNorm hz)
  -- The pointwise bound `‖f z‖ ≤ M(r)` on the circle can be squared and averaged.
  refine circleAverage_mono_on_of_le_circle hInt ?_
  intro z hz
  have hz' : z ∈ sphere (0 : ℂ) r := by
    simpa [abs_of_nonneg hr0] using hz
  have hnorm : ‖f z‖ ≤ circleSupNorm f r := hcont.norm_le_circleSupNorm hz'
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Helper for Exercise 9: a convex combination of two points below `z` stays below `z`. -/
lemma weighted_average_lt_of_lt_of_lt
    {x y z a b : ℝ}
    (hx : x < z) (hy : y < z)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    a * x + b * y < z := by
  -- Compare the weighted average to `max x y`, which is already below `z`.
  have hle : a * x + b * y ≤ max x y := by
    calc
      a * x + b * y ≤ a * max x y + b * max x y := by
        gcongr
        · exact le_max_left x y
        · exact le_max_right x y
      _ = (a + b) * max x y := by ring
      _ = max x y := by rw [hab, one_mul]
  exact lt_of_le_of_lt hle (max_lt_iff.mpr ⟨hx, hy⟩)

/-- Helper for Exercise 9: rewriting `I₂(e^s)` in logarithmic coordinates gives the exponential
coefficient series. -/
lemma circle_mean_sq_exp_eq_tsum_exp
    {f : ℂ → ℂ} {R s : ℝ} {a : ℕ → ℂ}
    (ha : HasFPowerSeriesOnBall f (.ofScalars ℂ a) 0 (ENNReal.ofReal R))
    (hR : 0 < R)
    (hs : s < Real.log R) :
    circle_mean_sq f (Real.exp s) =
      ∑' n : ℕ, ‖a n‖ ^ (2 : ℕ) * Real.exp ((2 * n : ℝ) * s) := by
  have hsR : Real.exp s < R := by
    calc
      Real.exp s < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hs
      _ = R := Real.exp_log hR
  -- Rewrite the radius power `exp s ^ (2 n)` as the exponential `exp ((2 n) s)`.
  rw [circle_mean_sq_eq_tsum_sq_norm_taylor_coeff ha (Real.exp_pos s).le hsR]
  congr with n
  rw [show ((2 * n : ℝ) * s) = s * (2 * n : ℝ) by ring, Real.exp_mul]
  rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by norm_num [Nat.cast_mul]]
  rw [Real.rpow_natCast]

/-- Helper for Exercise 9: Hölder interpolation on the coefficient series yields the multiplicative
log-convexity bound for `I₂(e^s)`. -/
lemma circle_mean_sq_comp_exp_le_rpow_mul_rpow
    {f : ℂ → ℂ} {R α β x y : ℝ} {a : ℕ → ℂ}
    (ha : HasFPowerSeriesOnBall f (.ofScalars ℂ a) 0 (ENNReal.ofReal R))
    (hR : 0 < R)
    (hx : x < Real.log R) (hy : y < Real.log R)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1) :
    circle_mean_sq f (Real.exp (α * x + β * y)) ≤
      circle_mean_sq f (Real.exp x) ^ α *
        circle_mean_sq f (Real.exp y) ^ β := by
  let term : ℝ → ℕ → ℝ := fun s n ↦ ‖a n‖ ^ (2 : ℕ) * Real.exp ((2 * n : ℝ) * s)
  let u : ℕ → ℝ := fun n ↦ Real.rpow (term x n) α
  let v : ℕ → ℝ := fun n ↦ Real.rpow (term y n) β
  have hterm_nonneg : ∀ s n, 0 ≤ term s n := by
    intro s n
    dsimp [term]
    positivity
  have hmid : α * x + β * y < Real.log R :=
    weighted_average_lt_of_lt_of_lt hx hy hα.le hβ.le hαβ
  have hsum_x : Summable (term x) := by
    have hxR : Real.exp x < R := by
      calc
        Real.exp x < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hx
        _ = R := Real.exp_log hR
    -- The source series is summable because it equals `I₂(e^x)`.
    convert
      (circle_mean_sq_hasSum_sq_norm_taylor_coeff ha (Real.exp_pos x).le hxR).summable using 1
    ext n
    dsimp [term]
    rw [show ((2 * n : ℝ) * x) = x * (2 * n : ℝ) by ring, Real.exp_mul]
    rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by norm_num [Nat.cast_mul]]
    rw [Real.rpow_natCast]
  have hsum_y : Summable (term y) := by
    have hyR : Real.exp y < R := by
      calc
        Real.exp y < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hy
        _ = R := Real.exp_log hR
    -- The same coefficient expansion controls the series at `y`.
    convert
      (circle_mean_sq_hasSum_sq_norm_taylor_coeff ha (Real.exp_pos y).le hyR).summable using 1
    ext n
    dsimp [term]
    rw [show ((2 * n : ℝ) * y) = y * (2 * n : ℝ) by ring, Real.exp_mul]
    rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by norm_num [Nat.cast_mul]]
    rw [Real.rpow_natCast]
  have hu_pow_eq : (fun n ↦ u n ^ (1 / α)) = term x := by
    funext n
    dsimp [u]
    -- Raise `term x n` to `α` and then back to exponent `1 / α`.
    simpa [one_div] using (Real.rpow_rpow_inv (hterm_nonneg x n) hα.ne')
  have hv_pow_eq : (fun n ↦ v n ^ (1 / β)) = term y := by
    funext n
    dsimp [v]
    -- The same exponent cancellation holds for the `y`-series.
    simpa [one_div] using (Real.rpow_rpow_inv (hterm_nonneg y n) hβ.ne')
  have huv_eq : (fun n ↦ u n * v n) = term (α * x + β * y) := by
    funext n
    dsimp [u, v, term]
    have hcoeff_nonneg : 0 ≤ ‖a n‖ ^ (2 : ℕ) := by positivity
    -- Split the mixed term into the `x`-piece and `y`-piece, then recombine the exponents.
    calc
      (‖a n‖ ^ (2 : ℕ) * Real.exp ((2 * n : ℝ) * x)) ^ α *
          (‖a n‖ ^ (2 : ℕ) * Real.exp ((2 * n : ℝ) * y)) ^ β
        = ((‖a n‖ ^ (2 : ℕ)) ^ α * (Real.exp ((2 * n : ℝ) * x)) ^ α) *
            (((‖a n‖ ^ (2 : ℕ)) ^ β) * (Real.exp ((2 * n : ℝ) * y)) ^ β) := by
              rw [Real.mul_rpow hcoeff_nonneg (Real.exp_pos _).le,
                Real.mul_rpow hcoeff_nonneg (Real.exp_pos _).le]
      _ = ((‖a n‖ ^ (2 : ℕ)) ^ α * (‖a n‖ ^ (2 : ℕ)) ^ β) *
            ((Real.exp ((2 * n : ℝ) * x)) ^ α * (Real.exp ((2 * n : ℝ) * y)) ^ β) := by
              ring
      _ = (‖a n‖ ^ (2 : ℕ)) ^ (α + β) *
            (Real.exp (((2 * n : ℝ) * x) * α) *
              Real.exp (((2 * n : ℝ) * y) * β)) := by
              rw [← Real.rpow_add' hcoeff_nonneg (by rw [hαβ]; norm_num),
                ← Real.exp_mul, ← Real.exp_mul]
      _ = ‖a n‖ ^ (2 : ℕ) * Real.exp ((2 * n : ℝ) * (α * x + β * y)) := by
              rw [hαβ, Real.rpow_one, ← Real.exp_add]
              congr 1
              ring
  have hu_sum : Summable (fun n ↦ u n ^ (1 / α)) := by
    rw [hu_pow_eq]
    exact hsum_x
  have hv_sum : Summable (fun n ↦ v n ^ (1 / β)) := by
    rw [hv_pow_eq]
    exact hsum_y
  have hholder :=
    inner_le_Lp_mul_Lq_tsum_of_nonneg
      (p := 1 / α) (q := 1 / β)
      (f := u) (g := v)
      (Real.holderConjugate_one_div hα hβ hαβ)
      (fun n ↦ Real.rpow_nonneg (hterm_nonneg x n) α)
      (fun n ↦ Real.rpow_nonneg (hterm_nonneg y n) β)
      hu_sum hv_sum
  -- Rewrite Hölder's inequality back in terms of the original coefficient series.
  calc
    circle_mean_sq f (Real.exp (α * x + β * y)) = ∑' n : ℕ, term (α * x + β * y) n := by
      simpa [term] using circle_mean_sq_exp_eq_tsum_exp ha hR hmid
    _ = ∑' n : ℕ, u n * v n := by rw [huv_eq]
    _ ≤ (∑' n : ℕ, u n ^ (1 / α)) ^ (1 / (1 / α)) *
          (∑' n : ℕ, v n ^ (1 / β)) ^ (1 / (1 / β)) := hholder
    _ = (∑' n : ℕ, term x n) ^ α * (∑' n : ℕ, term y n) ^ β := by
      rw [hu_pow_eq, hv_pow_eq]
      simp [one_div, hα.ne', hβ.ne']
    _ = circle_mean_sq f (Real.exp x) ^ α *
          circle_mean_sq f (Real.exp y) ^ β := by
      rw [← circle_mean_sq_exp_eq_tsum_exp ha hR hx, ← circle_mean_sq_exp_eq_tsum_exp ha hR hy]

/-- Exercise 9 (6): if `0 < R` and `f` is not identically zero on `‖z‖ < R`, then `log I₂(r)` is
convex as a function of `log r`; equivalently, `s ↦ log (I₂(e^s))` is convex on `s < log R`. -/
theorem log_circle_mean_sq_comp_exp_convex_of_not_eqOn_zero
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hR : 0 < R)
    (hfnz : ¬ EqOn f 0 (ball (0 : ℂ) R)) :
    ConvexOn ℝ (Set.Iio (Real.log R))
      (fun s ↦ Real.log (circle_mean_sq f (Real.exp s))) := by
  -- Route correction: keep the source's fixed coefficient series `J(s) = Σ ‖aₙ‖² e^{2ns}`, but
  -- package the Cauchy-Schwarz/Hölder endgame directly as a multiplicative interpolation bound.
  rcases analyticOnNhd_origin_power_series hf hR with ⟨a, ha⟩
  have hpos :
      ∀ ⦃s : ℝ⦄, s < Real.log R → 0 < circle_mean_sq f (Real.exp s) := by
    intro s hs
    exact circle_mean_sq_comp_exp_pos_of_not_eqOn_zero hf hR hfnz hs
  refine convexOn_iff_forall_pos.mpr ?_
  refine ⟨convex_Iio _, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  simp_rw [smul_eq_mul]
  have hmid : α * x + β * y < Real.log R :=
    weighted_average_lt_of_lt_of_lt hx hy hα.le hβ.le hαβ
  have hbound :=
    circle_mean_sq_comp_exp_le_rpow_mul_rpow ha hR hx hy hα hβ hαβ
  have hlog :
      Real.log (circle_mean_sq f (Real.exp (α * x + β * y))) ≤
        Real.log
          (Real.rpow (circle_mean_sq f (Real.exp x)) α *
            Real.rpow (circle_mean_sq f (Real.exp y)) β) := by
    exact Real.log_le_log (hpos hmid) hbound
  have hlog_rhs :
      Real.log
          (Real.rpow (circle_mean_sq f (Real.exp x)) α *
            Real.rpow (circle_mean_sq f (Real.exp y)) β) =
        α * Real.log (circle_mean_sq f (Real.exp x)) +
          β * Real.log (circle_mean_sq f (Real.exp y)) := by
    have hx_rpow :
        Real.log (Real.rpow (circle_mean_sq f (Real.exp x)) α) =
          α * Real.log (circle_mean_sq f (Real.exp x)) := by
      simpa [Real.rpow_eq_pow] using Real.log_rpow (hpos hx) α
    have hy_rpow :
        Real.log (Real.rpow (circle_mean_sq f (Real.exp y)) β) =
          β * Real.log (circle_mean_sq f (Real.exp y)) := by
      simpa [Real.rpow_eq_pow] using Real.log_rpow (hpos hy) β
    calc
      Real.log
          (Real.rpow (circle_mean_sq f (Real.exp x)) α *
            Real.rpow (circle_mean_sq f (Real.exp y)) β)
        =
          Real.log (Real.rpow (circle_mean_sq f (Real.exp x)) α) +
            Real.log (Real.rpow (circle_mean_sq f (Real.exp y)) β) := by
              exact Real.log_mul
                (Real.rpow_pos_of_pos (hpos hx) _).ne'
                (Real.rpow_pos_of_pos (hpos hy) _).ne'
      _ =
          α * Real.log (circle_mean_sq f (Real.exp x)) +
            β * Real.log (circle_mean_sq f (Real.exp y)) := by
              rw [hx_rpow, hy_rpow]
  -- Expand the logarithm of the multiplicative Hölder bound into the affine target inequality.
  rw [hlog_rhs] at hlog
  simpa using hlog
