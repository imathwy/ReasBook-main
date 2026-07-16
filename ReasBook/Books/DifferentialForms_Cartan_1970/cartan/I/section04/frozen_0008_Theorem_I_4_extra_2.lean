import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section04.«0004_Proposition_2_2»
import DifferentialForms_Cartan_1970.cartan.I.section04.«frozen_0006_Remark_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal NNReal
open Filter

variable {D : Set ℝ} {f : ℝ → ℝ}

/-- Helper for Theorem I.4-extra-2: on the unordered interval `uIcc x₀ x`, the Taylor polynomial
centered at `x₀` rewrites using the ordinary iterated derivatives at `x₀`. -/
lemma taylorWithinEval_uIcc_eq_finset_sum_iteratedDeriv
    {x₀ x : ℝ} (hfx₀ : ContDiffAt ℝ ⊤ f x₀) (n : ℕ) :
    taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
      ∑ k ∈ Finset.range (n + 1),
        (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k := by
  by_cases hxx₀ : x = x₀
  · -- At the center, the Taylor polynomial collapses to the constant term.
    subst hxx₀
    rw [taylorWithinEval_self]
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp
  · -- Away from the center, the unordered interval is a genuine interval.
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hu : UniqueDiffOn ℝ (Set.uIcc x₀ x) := by
      by_cases hlt : x₀ < x
      · simpa [Set.uIcc, min_eq_left hlt.le, max_eq_right hlt.le] using uniqueDiffOn_Icc hlt
      · have hgt : x < x₀ := by
          refine lt_of_not_ge ?_
          intro hx₀x
          exact hxx₀ (le_antisymm (not_lt.mp hlt) hx₀x)
        simpa [Set.uIcc, min_eq_right hgt.le, max_eq_left hgt.le] using uniqueDiffOn_Icc hgt
    have hwithin :
        iteratedDerivWithin k f (Set.uIcc x₀ x) x₀ = iteratedDeriv k f x₀ := by
      simpa using iteratedDerivWithin_eq_iteratedDeriv hu (hfx₀.of_le (by simp))
    -- The remaining step is scalar-algebra normalization.
    rw [hwithin]
    ring_nf

/-- Helper for Theorem I.4-extra-2: a local geometric derivative bound should control the
Lagrange remainder of the Taylor polynomial. -/
lemma lagrange_remainder_le_geometric_pow
    {x₀ r M t : ℝ} (hr : 0 < r) (hM : 0 < M) (ht : 0 < t)
    (hball : Metric.ball x₀ r ⊆ D) (hf : ContDiffOn ℝ ⊤ f D)
    (hbound :
      ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
        |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρr : ρ < r) :
    ∀ {x : ℝ}, x ∈ Metric.ball x₀ ρ → ∀ n : ℕ,
      |f x - ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k|
        ≤ M * (t * |x - x₀|) ^ (n + 1) := by
  let _ := hM
  let _ := ht
  let _ := hρ_pos
  intro x hx n
  by_cases hxx₀ : x = x₀
  · -- At the center, the Taylor remainder vanishes term-by-term.
    subst hxx₀
    have hx_nhds : D ∈ nhds x := by
      refine mem_of_superset (Metric.ball_mem_nhds _ hr) ?_
      intro y hy
      exact hball hy
    have hfx : ContDiffAt ℝ ⊤ f x := (hf.of_le le_top).contDiffAt hx_nhds
    have hsum :
        ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x / (k.factorial : ℝ)) * (x - x) ^ k = f x := by
      simpa [taylorWithinEval_self] using
        (taylorWithinEval_uIcc_eq_finset_sum_iteratedDeriv (x₀ := x) (x := x) hfx n).symm
    rw [hsum]
    simp
  · have hx_abs : |x - x₀| < ρ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hinterval_subset_D : Set.uIcc x₀ x ⊆ D := by
      intro y hy
      have hy_dist : dist y x₀ ≤ dist x x₀ := by
        simpa [dist_comm] using (Real.dist_left_le_of_mem_uIcc hy)
      have hy_ball : y ∈ Metric.ball x₀ r := by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt hy_dist (lt_of_lt_of_le hx (le_of_lt hρr))
      exact hball hy_ball
    have hcont_interval : ContDiffOn ℝ (n + 1) f (Set.uIcc x₀ x) := by
      exact (hf.of_le (by simp)).mono hinterval_subset_D
    have hx₀x : x₀ ≠ x := fun hx' ↦ hxx₀ hx'.symm
    obtain ⟨x', hx', hTaylor⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (x := x) (x₀ := x₀) hx₀x hcont_interval
    have hx'_ball : x' ∈ Metric.ball x₀ r := by
      have hx'_dist : dist x' x₀ ≤ dist x x₀ := by
        simpa [dist_comm] using
          (Real.dist_left_le_of_mem_uIcc (Set.uIoo_subset_uIcc_self hx'))
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hx'_dist (lt_of_lt_of_le hx (le_of_lt hρr))
    have hderiv_bound := hbound x' hx'_ball (n + 1)
    have hfactorial_rewrite :
        iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / ((n + 1).factorial : ℝ) =
          (iteratedDeriv (n + 1) f x' / ((n + 1).factorial : ℝ)) * (x - x₀) ^ (n + 1) := by
      field_simp
    have hx₀_nhds : D ∈ nhds x₀ := by
      refine mem_of_superset (Metric.ball_mem_nhds _ hr) ?_
      intro y hy
      exact hball hy
    have hfx₀ : ContDiffAt ℝ ⊤ f x₀ := (hf.of_le le_top).contDiffAt hx₀_nhds
    have hTaylorPoly :
        ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k =
            taylorWithinEval f n (Set.uIcc x₀ x) x₀ x := by
      symm
      exact taylorWithinEval_uIcc_eq_finset_sum_iteratedDeriv hfx₀ n
    -- Rewrite the remainder into the normalized derivative times the geometric factor.
    calc
      |f x - ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k|
          = |f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x| := by
              rw [hTaylorPoly]
      _ = |iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / ((n + 1).factorial : ℝ)| := by
            rw [hTaylor]
      _ = |iteratedDeriv (n + 1) f x' / ((n + 1).factorial : ℝ)| * |x - x₀| ^ (n + 1) := by
            rw [hfactorial_rewrite, abs_mul, abs_pow]
      _ ≤ (M * t ^ (n + 1)) * |x - x₀| ^ (n + 1) := by
            gcongr
      _ = M * (t * |x - x₀|) ^ (n + 1) := by
            rw [mul_assoc, ← mul_pow]

/-- Helper for Theorem I.4-extra-2: analyticity at `x₀` should imply a uniform local geometric
bound for the normalized iterated derivatives. -/
lemma analyticAt_has_local_uniform_geometric_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) {x₀ : ℝ} (hx₀ : x₀ ∈ D)
    (ha : AnalyticAt ℝ f x₀) :
    ∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
      ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
        |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p := by
  let _ := hf
  let a : ℕ → ℝ := fun n ↦ iteratedDeriv n f x₀ / n.factorial
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ a
  obtain ⟨rD, hrD_pos, hrD_sub⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx₀)
  have hpAt : HasFPowerSeriesAt f p x₀ := by
    -- Repackage analyticity using the canonical scalar Taylor series at the center.
    simpa [p, a] using ha.hasFPowerSeriesAt
  have hp_radius_pos : 0 < p.radius := hpAt.radius_pos
  obtain ⟨ρ, hρ⟩ := hpAt.comp_sub (-x₀)
  obtain ⟨R, _, hR_pos_ball, hR_lt_ρ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hρ.r_pos
  have hR_pos : 0 < R := ENNReal.ofReal_pos.mp hR_pos_ball
  have hR_lt_radius : ENNReal.ofReal R < p.radius := lt_of_lt_of_le hR_lt_ρ hρ.r_le
  let r : ℝ := min rD (R / 2)
  let A : ℝ := FormalMultilinearSeries.ofScalarsSum (fun n ↦ ‖a n‖) R
  let M : ℝ := max 1 A
  let t : ℝ := (R - r)⁻¹
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min hrD_pos (half_pos hR_pos)
  have hr_le_rD : r ≤ rD := by
    dsimp [r]
    exact min_le_left _ _
  have hr_lt_R : r < R := by
    calc
      r ≤ R / 2 := by
        dsimp [r]
        exact min_le_right _ _
      _ < R := by
        nlinarith
  have ht_pos : 0 < t := by
    dsimp [t]
    exact inv_pos.mpr (sub_pos.mpr hr_lt_R)
  have hsum_full : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum a) p 0 p.radius := by
    -- The formal series `p` sums to the scalar power series on its full convergence ball.
    simpa [p, a] using p.hasFPowerSeriesOnBall hp_radius_pos
  have hsum_R :
      HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum a) p 0 (ENNReal.ofReal R) := by
    -- Restrict to the explicit smaller radius `R`.
    exact hsum_full.mono hR_pos_ball hR_lt_radius.le
  have hshift_R : HasFPowerSeriesOnBall (fun z ↦ f (z + x₀)) p 0 (ENNReal.ofReal R) := by
    -- Shift the original germ to the origin so the coefficient majorant applies directly.
    simpa [sub_eq_add_neg] using hρ.mono hR_pos_ball hR_lt_ρ.le
  have hEqOn :
      Set.EqOn (fun z ↦ f (z + x₀)) (FormalMultilinearSeries.ofScalarsSum a)
        (Metric.eball 0 (ENNReal.ofReal R)) := by
    exact hshift_R.unique hsum_R
  refine ⟨r, hr_pos, ?_, ⟨M, by positivity, t, ht_pos, ?_⟩⟩
  · -- The working ball stays inside the original open set neighborhood.
    intro x hx
    exact hrD_sub (by
      simpa [Metric.mem_ball] using lt_of_lt_of_le hx hr_le_rD)
  · intro x hx q
    let y : ℝ := x - x₀
    have hy_lt_r : |y| < r := by
      simpa [y, Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hy_le_r : |y| ≤ r := le_of_lt hy_lt_r
    have hy_lt_R : |y| < R := lt_of_lt_of_le hy_lt_r hr_lt_R.le
    have hy_mem : y ∈ Metric.eball (0 : ℝ) (ENNReal.ofReal R) := by
      simpa [Metric.mem_eball, edist_dist, Real.dist_eq, y, hR_pos] using hy_lt_R
    have hiter_eq :
        iteratedDeriv q (fun z ↦ f (z + x₀)) y =
          iteratedDeriv q (FormalMultilinearSeries.ofScalarsSum a) y := by
      exact Set.EqOn.iteratedDeriv_of_isOpen hEqOn Metric.isOpen_eball q hy_mem
    have hshift_iter :
        iteratedDeriv q (fun z ↦ f (z + x₀)) y = iteratedDeriv q f x := by
      -- Shifting by a constant commutes with iterated derivatives.
      simpa [y, sub_eq_add_neg, add_assoc, sub_add_cancel] using
        congrArg (fun g : ℝ → ℝ ↦ g y) (iteratedDeriv_comp_add_const (f := f) (n := q) (s := x₀))
    have hbound_sum :
        |iteratedDeriv q (FormalMultilinearSeries.ofScalarsSum a) y / (q.factorial : ℝ)| ≤
          A / (R - r) ^ q := by
      -- Remark 2 gives the uniform bound for the shifted scalar power series.
      have hbound_sum' :
          |iteratedDeriv q (FormalMultilinearSeries.ofScalarsSum a) y| / (q.factorial : ℝ) ≤
            A / (R - r) ^ q := by
        simpa [A, p, a] using
          norm_iteratedDeriv_ofScalarsSum_div_factorial_le_powerSeriesAbsSum
            a q hR_lt_radius hy_le_r hr_lt_R
      simpa [abs_div, abs_of_nonneg (show 0 ≤ (q.factorial : ℝ) by positivity)] using hbound_sum'
    calc
      |iteratedDeriv q f x / (q.factorial : ℝ)|
          = |iteratedDeriv q (fun z ↦ f (z + x₀)) y / (q.factorial : ℝ)| := by
              rw [← hshift_iter]
      _ = |iteratedDeriv q (FormalMultilinearSeries.ofScalarsSum a) y / (q.factorial : ℝ)| := by
            rw [hiter_eq]
      _ ≤ A / (R - r) ^ q := hbound_sum
      _ ≤ M / (R - r) ^ q := by
            have hA_le_M : A ≤ M := by
              dsimp [M]
              exact le_max_right _ _
            have hpow_nonneg : 0 ≤ (R - r) ^ q := pow_nonneg (sub_nonneg.mpr hr_lt_R.le) q
            exact div_le_div_of_nonneg_right hA_le_M hpow_nonneg
      _ = M * t ^ q := by
            rw [div_eq_mul_inv, inv_pow]

/-- Helper for Cartan section04 frozen_0008_Theorem_I_4_extra_2: a geometric bound on the centered
Taylor coefficients forces the reciprocal growth rate inside the convergence radius. -/
lemma formalSeriesRadiusGeInvOfCenterGrowthBound
    {x₀ M t : ℝ}
    (hM : 0 < M) (ht : 0 < t)
    (hbound : ∀ n : ℕ, |iteratedDeriv n f x₀ / (n.factorial : ℝ)| ≤ M * t ^ n) :
    ENNReal.ofReal t⁻¹ ≤
      (FormalMultilinearSeries.ofScalars ℝ
          (fun n ↦ iteratedDeriv n f x₀ / (n.factorial : ℝ))).radius := by
  let _ := hM
  let a : ℕ → ℝ := fun n ↦ iteratedDeriv n f x₀ / n.factorial
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ a
  let r : NNReal := ⟨t⁻¹, inv_nonneg.mpr ht.le⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hbound' :
      ∀ n : ℕ, |iteratedDeriv n f x₀| / (n.factorial : ℝ) ≤ M * t ^ n := by
    intro n
    simpa [abs_div, abs_of_nonneg (show 0 ≤ (n.factorial : ℝ) by positivity)] using hbound n
  have hr_le : (r : ENNReal) ≤ p.radius := by
    -- Bound the normalized coefficients by the same geometric majorant at radius `t⁻¹`.
    refine p.le_radius_of_bound M fun n ↦ ?_
    have hcoeff : ‖p n‖ = ‖a n‖ := by
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, FormalMultilinearSeries.coeff_ofScalars]
    rw [hcoeff]
    calc
      ‖a n‖ * (r : ℝ) ^ n = ‖a n‖ * t⁻¹ ^ n := by rfl
      _ ≤ (M * t ^ n) * t⁻¹ ^ n := by
            exact mul_le_mul_of_nonneg_right (by simpa [a] using hbound' n)
              (pow_nonneg (inv_nonneg.mpr ht.le) _)
      _ = M * (t ^ n * t⁻¹ ^ n) := by rw [mul_assoc]
      _ = M * ((t * t⁻¹) ^ n) := by rw [← mul_pow]
      _ = M := by rw [mul_inv_cancel₀ ht_ne, one_pow, mul_one]
  have hr_eq : (r : ENNReal) = ENNReal.ofReal t⁻¹ := by
    exact (ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr ht.le)).symm
  exact hr_eq ▸ hr_le

/-- Helper for Cartan section04 frozen_0008_Theorem_I_4_extra_2: if the shifted partial sums of a
centered scalar series converge on a smaller ball, then the limit agrees with the summed series
there by uniqueness of limits. -/
lemma centeredSeriesEqOnSubballOfShiftedPartialSumLimit
    {g : ℝ → ℝ} {x₀ ρ : ℝ}
    (hρpos : 0 < ρ) (p : FormalMultilinearSeries ℝ ℝ ℝ)
    (hρradius : ENNReal.ofReal ρ < p.radius)
    (hlim : ∀ x ∈ Metric.ball x₀ ρ,
      Tendsto (fun n : ℕ ↦ p.partialSum (n + 1) (x - x₀)) atTop (nhds (g x))) :
    Set.EqOn g (fun x ↦ p.sum (x - x₀)) (Metric.ball x₀ ρ) := by
  intro x hx
  have hxnorm : |x - x₀| < ρ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
  have hy_radius : ENNReal.ofReal |x - x₀| < p.radius := by
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hρpos).2 hxnorm) hρradius.le
  have hy : x - x₀ ∈ Metric.eball (0 : ℝ) p.radius := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hy_radius
  have hpRadiusPos : 0 < p.radius :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρpos) hρradius.le
  have hsum :
      Tendsto (fun n : ℕ ↦ p.partialSum (n + 1) (x - x₀)) atTop (nhds (p.sum (x - x₀))) := by
    -- The centered scalar series has its own canonical partial-sum limit on the smaller ball.
    simpa using ((p.hasFPowerSeriesOnBall hpRadiusPos).tendsto_partialSum hy).comp
      (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique (hlim x hx) hsum

/-- Helper for Theorem I.4-extra-2: a local geometric bound on the normalized iterated
derivatives should force analyticity at the center. -/
lemma analyticAt_of_locally_geometric_factorial_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) {x₀ : ℝ} (hx₀ : x₀ ∈ D) :
    (∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
      ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
        |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p) →
    AnalyticAt ℝ f x₀ := by
  let _ := hD
  let _ := hx₀
  intro h
  rcases h with ⟨r, hr, hball, M, hM, t, ht, hbound⟩
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (fun n ↦ iteratedDeriv n f x₀ / (n.factorial : ℝ))
  let ρ : ℝ := min (r / 2) ((2 * t)⁻¹)
  have hradius_ge : ENNReal.ofReal t⁻¹ ≤ p.radius :=
    formalSeriesRadiusGeInvOfCenterGrowthBound (f := f) (x₀ := x₀) hM ht
      (fun n ↦ by simpa [p] using hbound x₀ (by simpa [Metric.mem_ball] using hr) n)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    refine lt_min ?_ ?_
    · exact half_pos hr
    · exact inv_pos.mpr (by positivity)
  have hρle_r : ρ ≤ r := by
    dsimp [ρ]
    calc
      min (r / 2) ((2 * t)⁻¹) ≤ r / 2 := min_le_left _ _
      _ ≤ r := by nlinarith
  have hρlt_r : ρ < r := by
    calc
      ρ ≤ r / 2 := by
        dsimp [ρ]
        exact min_le_left _ _
      _ < r := by
        nlinarith
  have htρ_lt_one : t * ρ < 1 := by
    have hρle : ρ ≤ (2 * t)⁻¹ := by
      dsimp [ρ]
      exact min_le_right _ _
    have ht_ne : t ≠ 0 := ne_of_gt ht
    have hhalf : t * ((2 * t)⁻¹) = (1 : ℝ) / 2 := by
      field_simp [ht_ne]
    calc
      t * ρ ≤ t * ((2 * t)⁻¹) := by gcongr
      _ = (1 : ℝ) / 2 := hhalf
      _ < 1 := by norm_num
  have hρlt_tinv : ρ < t⁻¹ := by
    have hρle : ρ ≤ (2 * t)⁻¹ := by
      dsimp [ρ]
      exact min_le_right _ _
    have ht_ne : t ≠ 0 := ne_of_gt ht
    calc
      ρ ≤ (2 * t)⁻¹ := hρle
      _ < t⁻¹ := by
            field_simp [ht_ne]
            nlinarith
  have hρradius : ENNReal.ofReal ρ < p.radius := by
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr ht)).2 hρlt_tinv) hradius_ge
  have hshifted_limit :
      ∀ x ∈ Metric.ball x₀ ρ,
        Tendsto (fun n : ℕ ↦ p.partialSum (n + 1) (x - x₀)) atTop (nhds (f x)) := by
    intro x hx
    have hxnorm : |x - x₀| < ρ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hq_lt_one : t * |x - x₀| < 1 := by
      have htx_le : t * |x - x₀| ≤ t * ρ :=
        mul_le_mul_of_nonneg_left (le_of_lt hxnorm) ht.le
      exact lt_of_le_of_lt htx_le htρ_lt_one
    have hq_nonneg : 0 ≤ t * |x - x₀| := by positivity
    have hgeom :
        Tendsto (fun n : ℕ ↦ M * (t * |x - x₀|) ^ (n + 1)) atTop (nhds 0) := by
      have hpow :
          Tendsto (fun n : ℕ ↦ (t * |x - x₀|) ^ (n + 1)) atTop (nhds 0) := by
        exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one).comp
          (tendsto_add_atTop_nat 1)
      simpa using tendsto_const_nhds.mul hpow
    have hnorm :
        Tendsto
          (fun n : ℕ ↦ ‖p.partialSum (n + 1) (x - x₀) - f x‖)
          atTop (nhds 0) := by
      -- The Taylor remainder is trapped by a geometric sequence with ratio `< 1`.
      refine squeeze_zero (fun _ ↦ norm_nonneg _) ?_ hgeom
      intro n
      have hpartial_eq :
          p.partialSum (n + 1) (x - x₀) =
            ∑ k ∈ Finset.range (n + 1),
              (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k := by
        simp [p, FormalMultilinearSeries.partialSum, smul_eq_mul, mul_comm]
      calc
        ‖p.partialSum (n + 1) (x - x₀) - f x‖
            = |f x - ∑ k ∈ Finset.range (n + 1),
                (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k| := by
                  rw [Real.norm_eq_abs, abs_sub_comm, ← hpartial_eq]
        _ ≤ M * (t * |x - x₀|) ^ (n + 1) := by
              exact lagrange_remainder_le_geometric_pow hr hM ht hball hf hbound hρpos hρlt_r hx n
    exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm
  have hEqOn :
      Set.EqOn f (fun x ↦ p.sum (x - x₀)) (Metric.ball x₀ ρ) :=
    centeredSeriesEqOnSubballOfShiftedPartialSumLimit (g := f) hρpos p hρradius hshifted_limit
  have hpRadiusPos : 0 < p.radius :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr ht)) hradius_ge
  have hpAnalytic : AnalyticAt ℝ (fun x ↦ p.sum (x - x₀)) x₀ := by
    -- The centered formal series is analytic on its convergence ball.
    simpa using ((p.hasFPowerSeriesOnBall hpRadiusPos).analyticAt.comp_sub x₀)
  have hEventually : (fun x ↦ p.sum (x - x₀)) =ᶠ[nhds x₀] f := by
    -- On the smaller ball, the shifted series and `f` agree pointwise.
    filter_upwards [Metric.ball_mem_nhds x₀ hρpos] with x hx
    exact (hEqOn hx).symm
  exact hpAnalytic.congr hEventually

/-- Pointwise form of Theorem I.4-extra-2 in the ambient open set `D`: at `x₀ ∈ D`, analyticity is
equivalent to the existence of a ball contained in `D` and positive constants `M` and `t` such that
`|iteratedDeriv p f x / p!| ≤ M * t ^ p` throughout that ball. -/
theorem analyticAt_iff_locally_geometric_factorial_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) {x₀ : ℝ} (hx₀ : x₀ ∈ D) :
    AnalyticAt ℝ f x₀ ↔
      ∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
        ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
          |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p := by
  constructor
  · intro ha
    -- This is the coefficient-estimate half of the textbook argument.
    exact analyticAt_has_local_uniform_geometric_iteratedDeriv_bound hD hf hx₀ ha
  · intro hbound
    -- This is the Taylor-Lagrange half of the textbook argument.
    exact analyticAt_of_locally_geometric_factorial_iteratedDeriv_bound hD hf hx₀ hbound

/-- Cartan section04 frozen_0008_Theorem_I_4_extra_2: for a smooth real function on an open set,
analyticity is equivalent to the local existence of a ball contained in the domain and positive
constants `M` and `t` such that `|iteratedDeriv p f x / p!| ≤ M * t ^ p` throughout that ball. -/
theorem analyticOnNhd_iff_locally_geometric_factorial_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) :
    AnalyticOnNhd ℝ f D ↔
      ∀ x₀ ∈ D, ∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
        ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
          |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p := by
  constructor
  · intro h x₀ hx₀
    exact
      (analyticAt_iff_locally_geometric_factorial_iteratedDeriv_bound hD hf hx₀).1 (h x₀ hx₀)
  · intro h x₀ hx₀
    exact
      (analyticAt_iff_locally_geometric_factorial_iteratedDeriv_bound hD hf hx₀).2 (h x₀ hx₀)
