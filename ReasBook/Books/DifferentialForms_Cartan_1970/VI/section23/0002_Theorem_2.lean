import Mathlib
import DifferentialForms_Cartan_1970.III.section12.«0028_Exercise_16»
import DifferentialForms_Cartan_1970.VI.section22.«0005_Corollary_VI_1_extra_3»
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

noncomputable section

-- Semantic search was unavailable in this workspace; the statement uses the repo's standard
-- source-facing biholomorphic owner `HolomorphicIsomorph Set.univ Set.univ` for complex-plane
-- automorphisms, while keeping the explicit affine normal form on `ℂ`.

/-- Helper for Theorem 2: a holomorphic automorphism of `ℂ` is injective on the whole plane,
because the source of the underlying open partial homeomorphism is `univ`. -/
lemma holomorphic_isomorph_injective_univ
    (e : HolomorphicIsomorph Set.univ Set.univ) :
    Function.Injective (e : ℂ → ℂ) := by
  -- Upgrade injectivity on the source of the partial homeomorphism to global injectivity.
  have hinj : Set.InjOn (e : ℂ → ℂ) Set.univ := by
    simpa [HolomorphicIsomorph.source_eq] using (e : OpenPartialHomeomorph ℂ ℂ).injOn
  intro z w hzw
  exact hinj (by simp) (by simp) hzw

/-- Helper for Theorem 2: the inversion chart `w ↦ e (w⁻¹)` is analytic on the punctured
neighborhood of `0`. -/
lemma inverse_chart_eventually_analytic_at_zero
    (e : HolomorphicIsomorph Set.univ Set.univ) :
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (fun u : ℂ ↦ (e : ℂ → ℂ) u⁻¹) w := by
  -- Away from `0`, inversion is analytic and `e` is entire, so their composition is analytic.
  filter_upwards [self_mem_nhdsWithin] with w hw0
  have he : AnalyticAt ℂ (e : ℂ → ℂ) (w⁻¹) := by
    simpa using e.analyticOn_toFun (w⁻¹) (by simp)
  exact he.comp (analyticAt_inv hw0)

/-- Helper for Theorem 2: the inversion chart `w ↦ e (w⁻¹)` has an isolated singularity at `0`,
because it is analytic at every nearby nonzero point. -/
lemma inverse_chart_isolated_singularity_at_zero
    (e : HolomorphicIsomorph Set.univ Set.univ) :
    HasIsolatedSingularityAt (fun w : ℂ ↦ (e : ℂ → ℂ) w⁻¹) 0 := by
  -- Package the punctured-neighborhood analyticity into the isolated-singularity owner predicate.
  simpa [HasIsolatedSingularityAt] using inverse_chart_eventually_analytic_at_zero e

/-- Helper for Theorem 2: on every punctured ball around `0`, the inversion chart remains injective
because inversion and the automorphism itself are both injective away from `0`. -/
lemma inverse_chart_injOn_punctured_ball
    (e : HolomorphicIsomorph Set.univ Set.univ) {r : ℝ} :
    Set.InjOn (fun w : ℂ ↦ (e : ℂ → ℂ) w⁻¹) (Metric.ball 0 r \ ({0} : Set ℂ)) := by
  -- Reduce injectivity of the chart to global injectivity of `e`, then invert once more.
  intro w₁ hw₁ w₂ hw₂ hw
  have he_inj : Function.Injective (e : ℂ → ℂ) := holomorphic_isomorph_injective_univ e
  have hpre : w₁⁻¹ = w₂⁻¹ := he_inj hw
  have hinv := congrArg Inv.inv hpre
  simpa [hw₁.2, hw₂.2] using hinv

/-- Helper for Theorem 2: the inversion chart is meromorphic at `0`; otherwise it would be an
essential singularity and Exercise 16 would contradict its punctured-disc injectivity. -/
lemma inverse_chart_meromorphic_at_zero
    (e : HolomorphicIsomorph Set.univ Set.univ) :
    MeromorphicAt (fun w : ℂ ↦ (e : ℂ → ℂ) w⁻¹) 0 := by
  -- Exclude the essential-singularity branch using punctured-disc noninjectivity from Exercise 16.
  by_contra hnot_meromorphic
  have hess : HasEssentialSingularityAt (fun w : ℂ ↦ (e : ℂ → ℂ) w⁻¹) 0 := by
    exact ⟨inverse_chart_isolated_singularity_at_zero e, hnot_meromorphic⟩
  have hnot_inj :
      ¬ Set.InjOn (fun w : ℂ ↦ (e : ℂ → ℂ) w⁻¹) (Metric.ball 0 1 \ ({0} : Set ℂ)) := by
    exact not_injOn_on_any_smaller_puncturedDisc_of_essentialSingularity
      (f := fun w : ℂ ↦ (e : ℂ → ℂ) w⁻¹) (c := 0) hess zero_lt_one
  exact hnot_inj (inverse_chart_injOn_punctured_ball e)

/-- Helper for Theorem 2: if the inversion chart of an entire function is meromorphic at `0`,
then the function has polynomial growth outside a large ball. -/
lemma exterior_norm_le_mul_zpow_of_meromorphic_inversion_chart
    {f : ℂ → ℂ} (hinv : MeromorphicAt (fun w : ℂ ↦ f w⁻¹) 0) :
    ∃ n : ℤ, ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n := by
  let chart : ℂ → ℂ := fun w ↦ f w⁻¹
  by_cases htop : meromorphicOrderAt chart 0 = ⊤
  · have hzero : ∀ᶠ w in 𝓝[≠] (0 : ℂ), chart w = 0 := by
      exact (meromorphicOrderAt_eq_top_iff).1 htop
    have hzero' : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → chart w = 0 := by
      simpa [chart] using (eventually_nhdsWithin_iff.1 hzero)
    rcases Metric.mem_nhds_iff.1 hzero' with ⟨ε, hεpos, hε⟩
    refine ⟨0, ε⁻¹ + 1, 0, by positivity, le_rfl, ?_⟩
    intro z hz
    have hzlarge : ε⁻¹ < ‖z‖ := by
      exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hz
    have hznorm_pos : 0 < ‖z‖ := lt_trans (inv_pos.mpr hεpos) hzlarge
    have hz0 : z ≠ 0 := norm_ne_zero_iff.1 hznorm_pos.ne'
    have hinv_norm : ‖z⁻¹‖ < ε := by
      rw [norm_inv]
      simpa [one_div] using (one_div_lt hεpos hznorm_pos).1 (by simpa [one_div] using hzlarge)
    have hball : z⁻¹ ∈ Metric.ball (0 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hinv_norm
    have hchart : chart (z⁻¹) = 0 := hε hball (inv_ne_zero hz0)
    have hfz : f z = 0 := by
      simpa [chart] using hchart
    simp [hfz]
  · lift meromorphicOrderAt chart 0 to ℤ using htop with m hm
    obtain ⟨g, hg_an, -, hchart_eq⟩ := (meromorphicOrderAt_eq_int_iff hinv).1 hm.symm
    have hchart_eq' : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → chart w = w ^ m * g w := by
      simpa [chart] using (eventually_nhdsWithin_iff.1 hchart_eq)
    rcases Metric.mem_nhds_iff.1 hchart_eq' with ⟨ε₁, hε₁pos, hε₁⟩
    have hgbounded : ∀ᶠ w in 𝓝 (0 : ℂ), ‖g w‖ ≤ ‖g 0‖ + 1 := by
      have hball : ∀ᶠ w in 𝓝 (0 : ℂ), g w ∈ Metric.ball (g 0) 1 :=
        hg_an.continuousAt (Metric.ball_mem_nhds _ zero_lt_one)
      filter_upwards [hball] with w hw
      have hw' : ‖g w - g 0‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      calc
        ‖g w‖ = ‖(g w - g 0) + g 0‖ := by ring_nf
        _ ≤ ‖g w - g 0‖ + ‖g 0‖ := norm_add_le _ _
        _ ≤ ‖g 0‖ + 1 := by linarith
    rcases Metric.mem_nhds_iff.1 hgbounded with ⟨ε₂, hε₂pos, hε₂⟩
    let ε : ℝ := min ε₁ ε₂
    let R : ℝ := max 1 (ε⁻¹ + 1)
    let M : ℝ := ‖g 0‖ + 1
    refine ⟨-m, R, M, ?_, ?_, ?_⟩
    · dsimp [R, ε]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    · dsimp [M]
      positivity
    · intro z hz
      have hz_one : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz
      have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz_one
      have hz0 : z ≠ 0 := norm_ne_zero_iff.1 hz_pos.ne'
      have hz_inv : ε⁻¹ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
      have hεpos : 0 < ε := lt_min hε₁pos hε₂pos
      have hinv_norm : ‖z⁻¹‖ < ε := by
        rw [norm_inv]
        have hzlarge : ε⁻¹ < ‖z‖ := by
          exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hz_inv
        simpa [one_div] using (one_div_lt hεpos hz_pos).1 (by simpa [one_div] using hzlarge)
      have hball₁ : z⁻¹ ∈ Metric.ball (0 : ℂ) ε₁ := by
        have : ‖z⁻¹‖ < ε₁ := lt_of_lt_of_le hinv_norm (min_le_left _ _)
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hball₂ : z⁻¹ ∈ Metric.ball (0 : ℂ) ε₂ := by
        have : ‖z⁻¹‖ < ε₂ := lt_of_lt_of_le hinv_norm (min_le_right _ _)
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hchart_val : f z = (z⁻¹) ^ m * g (z⁻¹) := by
        simpa [chart] using hε₁ hball₁ (inv_ne_zero hz0)
      have hg_bound : ‖g (z⁻¹)‖ ≤ M := by
        simpa [M] using hε₂ hball₂
      have hnorm_pow : ‖(z⁻¹ : ℂ) ^ m‖ = ‖z‖ ^ (-m) := by
        calc
          ‖(z⁻¹ : ℂ) ^ m‖ = ‖z⁻¹‖ ^ m := norm_zpow _ _
          _ = (1 / ‖z‖) ^ m := by simp [norm_inv, one_div]
          _ = ‖z‖ ^ (-m) := by
            rw [one_div_zpow]
            simpa [one_div] using (zpow_neg hz_pos.ne' (n := m) (a := ‖z‖)).symm
      calc
        ‖f z‖ = ‖(z⁻¹ : ℂ) ^ m * g (z⁻¹)‖ := by rw [hchart_val]
        _ = ‖(z⁻¹ : ℂ) ^ m‖ * ‖g (z⁻¹)‖ := norm_mul _ _
        _ ≤ ‖(z⁻¹ : ℂ) ^ m‖ * M := by gcongr
        _ = M * ‖z‖ ^ (-m) := by rw [hnorm_pow, mul_comm]

/-- Helper for Theorem 2: the normalized Taylor coefficient at the origin for an entire function. -/
def entire_growth_coeff (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k f 0 / k.factorial

/-- Helper for Theorem 2: an exterior bound by `M * ‖z‖ ^ n` controls the normalized Taylor
coefficients of an entire function at the origin. -/
lemma entire_growth_coeff_norm_le_of_exterior_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M r : ℝ} (hr0 : 0 < r) (hR : R ≤ r)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) (k : ℕ) :
    ‖entire_growth_coeff f k‖ ≤ max M 0 * r ^ (n - (k : ℤ)) := by
  have hcircle : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ max M 0 * r ^ n := by
    intro z hz
    have hznorm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, sub_zero] using hz
    have hzR : R ≤ ‖z‖ := by
      rw [hznorm]
      exact hR
    calc
      ‖f z‖ ≤ M * ‖z‖ ^ n := hbound z hzR
      _ = M * r ^ n := by rw [hznorm]
      _ ≤ max M 0 * r ^ n := by
        exact mul_le_mul_of_nonneg_right (le_max_left M 0) (by positivity)
  have hiter :
      ‖iteratedDeriv k f 0‖ ≤ k.factorial * (max M 0 * r ^ n) / r ^ k := by
    simpa using
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
        (c := 0) (R := r) (C := max M 0 * r ^ n) (f := f) k hr0 hf.diffContOnCl hcircle
  have hkfac_nonneg : 0 ≤ (k.factorial : ℝ) := by positivity
  have hkfac_ne : (k.factorial : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  calc
    ‖entire_growth_coeff f k‖ = ‖iteratedDeriv k f 0‖ / k.factorial := by
      simp [entire_growth_coeff, norm_div]
    _ ≤ (k.factorial * (max M 0 * r ^ n) / r ^ k) / k.factorial := by
      exact div_le_div_of_nonneg_right hiter hkfac_nonneg
    _ = (max M 0 * r ^ n) / r ^ k := by
      field_simp [hkfac_ne]
    _ = max M 0 * r ^ (n - (k : ℤ)) := by
      calc
        (max M 0 * r ^ n) / r ^ k = max M 0 * (r ^ n / r ^ (k : ℤ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
          simp [zpow_natCast]
        _ = max M 0 * r ^ (n - (k : ℤ)) := by rw [zpow_sub₀ hr_ne]

/-- Helper for Theorem 2: if the growth exponent is strictly smaller than the index `k`, then the
`k`-th normalized Taylor coefficient vanishes. -/
lemma entire_growth_coeff_eq_zero_of_int_lt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M : ℝ}
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) {k : ℕ} (hk : n < (k : ℤ)) :
    entire_growth_coeff f k = 0 := by
  by_contra hk0
  let B : ℝ := max M 0
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_max_right M 0
  have hk_norm_pos : 0 < ‖entire_growth_coeff f k‖ := norm_pos_iff.mpr hk0
  obtain ⟨m, hm⟩ := exists_nat_gt (max R 2 + B / ‖entire_growth_coeff f k‖)
  have hm_one : (1 : ℝ) < m := by
    have haux : (2 : ℝ) < m := by
      have hdiv_nonneg : 0 ≤ B / ‖entire_growth_coeff f k‖ := by positivity
      linarith [show (2 : ℝ) ≤ max R 2 by exact le_max_right _ _]
    linarith
  have hm_pos : 0 < (m : ℝ) := by linarith
  have hR : R ≤ (m : ℝ) := by
    have hdiv_nonneg : 0 ≤ B / ‖entire_growth_coeff f k‖ := by positivity
    linarith [show R ≤ max R 2 by exact le_max_left _ _]
  have hcoeff := entire_growth_coeff_norm_le_of_exterior_growth
    hf (n := n) (R := R) (M := M) hm_pos hR hbound k
  have hsub : n - (k : ℤ) ≤ (-1 : ℤ) := by linarith
  have hpow : (m : ℝ) ^ (n - (k : ℤ)) ≤ (m : ℝ) ^ (-1 : ℤ) := by
    exact (zpow_le_zpow_iff_right₀ hm_one).2 hsub
  have hnorm_le : ‖entire_growth_coeff f k‖ ≤ B / (m : ℝ) := by
    calc
      ‖entire_growth_coeff f k‖ ≤ B * (m : ℝ) ^ (n - (k : ℤ)) := by simpa [B] using hcoeff
      _ ≤ B * (m : ℝ) ^ (-1 : ℤ) := mul_le_mul_of_nonneg_left hpow hB_nonneg
      _ = B / (m : ℝ) := by simp [B, div_eq_mul_inv]
  have hdiv_lt_m : B / ‖entire_growth_coeff f k‖ < (m : ℝ) := by
    have hmax_nonneg : 0 ≤ max R 2 := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right R 2)
    linarith
  have hmul_lt : B < ‖entire_growth_coeff f k‖ * (m : ℝ) := by
    have := (div_lt_iff₀ hk_norm_pos).mp hdiv_lt_m
    simpa [mul_comm] using this
  have hnorm_lt : B / (m : ℝ) < ‖entire_growth_coeff f k‖ := by
    exact (div_lt_iff₀ hm_pos).2 hmul_lt
  exact (not_lt_of_ge hnorm_le) hnorm_lt

/-- Helper for Theorem 2: evaluating a finite monomial sum gives the corresponding finite Taylor
sum. -/
lemma polynomial_eval_eq_growth_coeff_sum_range (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    Polynomial.eval z
      (Finset.sum (Finset.range N) fun m : ℕ ↦ Polynomial.monomial m (c m)) =
      Finset.sum (Finset.range N) fun m : ℕ ↦ c m * z ^ m := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Polynomial.eval_add]
      simp [Finset.sum_range_succ, ih, add_comm]

/-- Helper for Theorem 2: once the normalized Taylor coefficients vanish above `N`, the entire
Taylor series collapses to a polynomial evaluation. -/
lemma scalar_tsum_eq_polynomial_eval_of_growth_coeff_eventually_zero
    {c : ℕ → ℂ} {N : ℕ} (hc : ∀ m > N, c m = 0) (z : ℂ) :
    ∑' m : ℕ, c m * z ^ m =
      Polynomial.eval z
        (Finset.sum (Finset.range (N + 1)) fun m : ℕ ↦ Polynomial.monomial m (c m)) := by
  have hzero : ∀ m ∉ Finset.range (N + 1), c m * z ^ m = 0 := by
    intro m hm
    have hm' : N < m := by
      exact Nat.lt_of_not_ge fun hge ↦ hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hge))
    simp [hc m hm']
  rw [tsum_eq_sum (s := Finset.range (N + 1)) hzero]
  -- Rewrite the finite Taylor sum as a polynomial evaluation.
  exact (polynomial_eval_eq_growth_coeff_sum_range c (N + 1) z).symm

/-- Helper for Theorem 2: an entire function with polynomial growth on the exterior of a large ball
agrees everywhere with a complex polynomial. -/
lemma exists_polynomial_of_entire_exterior_zpow_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M : ℝ}
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  let c : ℕ → ℂ := entire_growth_coeff f
  have hc : ∀ m : ℕ, n < (m : ℤ) → c m = 0 := by
    intro m hm
    exact entire_growth_coeff_eq_zero_of_int_lt hf hbound hm
  by_cases hn : 0 ≤ n
  · let N : ℕ := Int.toNat n
    let p : Polynomial ℂ :=
      Finset.sum (Finset.range (N + 1)) fun m : ℕ ↦ Polynomial.monomial m (c m)
    refine ⟨p, ?_⟩
    intro z
    have hsum : HasSum (fun m : ℕ ↦ c m * z ^ m) (f z) := by
      -- The global Taylor series of an entire function is its power-series expansion at `0`.
      simpa [c, entire_growth_coeff, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
    have hcollapse : ∑' m : ℕ, c m * z ^ m = p.eval z := by
      apply scalar_tsum_eq_polynomial_eval_of_growth_coeff_eventually_zero
      intro m hm
      have hm' : ((N : ℕ) : ℤ) < (m : ℤ) := by
        exact_mod_cast hm
      exact hc m (by simpa [N, Int.toNat_of_nonneg hn] using hm')
    calc
      f z = ∑' m : ℕ, c m * z ^ m := hsum.tsum_eq.symm
      _ = p.eval z := hcollapse
  · have hnneg : n < 0 := lt_of_not_ge hn
    refine ⟨0, ?_⟩
    intro z
    have hsum : HasSum (fun m : ℕ ↦ c m * z ^ m) (f z) := by
      -- The entire Taylor series still represents `f`; if every coefficient vanishes, so does `f`.
      simpa [c, entire_growth_coeff, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
    have hzero : HasSum (fun m : ℕ ↦ c m * z ^ m) 0 := by
      have hfun : (fun m : ℕ ↦ c m * z ^ m) = fun _ : ℕ ↦ 0 := by
        funext m
        have hm : n < (m : ℤ) := lt_of_lt_of_le hnneg (by exact_mod_cast (Nat.zero_le m))
        simp [c, hc m hm]
      rw [hfun]
      exact hasSum_zero
    simpa using hsum.unique hzero

/-- Helper for Theorem 2: the derivative of a biholomorphic automorphism of `ℂ` never vanishes. -/
lemma deriv_ne_zero_of_holomorphic_isomorph_univ
    (e : HolomorphicIsomorph Set.univ Set.univ) (z : ℂ) :
    deriv (e : ℂ → ℂ) z ≠ 0 := by
  -- A zero derivative would contradict differentiability of the analytic inverse branch.
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [HolomorphicIsomorph.source_eq]
  have he_analytic : AnalyticAt ℂ (e : ℂ → ℂ) z := by
    simpa using e.analyticOn_toFun z (by simp)
  have hsymm_analytic :
      AnalyticAt ℂ ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) ((e : ℂ → ℂ) z) := by
    simpa using e.analyticOn_invFun ((e : ℂ → ℂ) z) (by simp)
  intro hzero
  have he_zero : HasDerivAt (e : ℂ → ℂ) 0 z := by
    exact he_analytic.differentiableAt.hasDerivAt.congr_deriv hzero
  have hleft : ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) ((e : ℂ → ℂ) z) = z :=
    (e : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source
  have he_zero_at_preimage :
      HasDerivAt (e : ℂ → ℂ) 0 (((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) ((e : ℂ → ℂ) z)) := by
    simpa [hleft] using he_zero
  have hnot_diff :
      ¬ DifferentiableAt ℂ ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) ((e : ℂ → ℂ) z) := by
    -- The local right-inverse relation from the partial homeomorphism forces the contradiction.
    exact not_differentiableAt_of_local_left_inverse_hasDerivAt_zero
      (f := (e : ℂ → ℂ))
      (g := ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ))
      he_zero_at_preimage
      ((e : OpenPartialHomeomorph ℂ ℂ).eventually_right_inverse' hz_source)
  exact hnot_diff hsymm_analytic.differentiableAt

/-- Helper for Theorem 2: a biholomorphic automorphism of `ℂ` is represented by a polynomial.

This follows the source proof: analyze the inversion chart at `0`, rule out an essential
singularity by injectivity, and then apply the polynomial-growth theorem at infinity. -/
lemma complex_plane_automorphism_eq_polynomial
    (e : HolomorphicIsomorph Set.univ Set.univ) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, (e : ℂ → ℂ) z = p.eval z := by
  -- Route correction: prove meromorphy at infinity from the inversion chart, then invoke the
  -- entire-function growth theorem from Exercise 4 rather than introducing a quotient model.
  have hinv : MeromorphicAt (fun w : ℂ ↦ (e : ℂ → ℂ) w⁻¹) 0 :=
    inverse_chart_meromorphic_at_zero e
  have he_analytic : AnalyticOnNhd ℂ (e : ℂ → ℂ) Set.univ := by
    -- The automorphism is entire because its source is all of `ℂ`.
    simpa using e.analyticOn_toFun
  have he_diff : Differentiable ℂ (e : ℂ → ℂ) := by
    -- Entire analyticity is exactly global complex differentiability on `ℂ`.
    simpa using (Complex.analyticOnNhd_univ_iff_differentiable.mp he_analytic)
  obtain ⟨n, R, M, -, -, hbound⟩ :=
    exterior_norm_le_mul_zpow_of_meromorphic_inversion_chart hinv
  -- The local Taylor-coefficient argument upgrades the exterior growth bound to a polynomial
  -- identity on all of `ℂ`.
  exact exists_polynomial_of_entire_exterior_zpow_bound
    he_diff (n := n) (R := R) (M := M) hbound

/-- Theorem 2 (1): a biholomorphic automorphism of the complex plane is an affine map
`z ↦ a * z + b` with nonzero linear coefficient. -/
theorem complex_plane_automorphism_affine
    (e : HolomorphicIsomorph Set.univ Set.univ) :
    ∃ a : ℂˣ, ∃ b : ℂ, ∀ z : ℂ, (e : OpenPartialHomeomorph ℂ ℂ) z = (a : ℂ) * z + b := by
  obtain ⟨p, hp⟩ := complex_plane_automorphism_eq_polynomial e
  have hderiv_eq_eval (z : ℂ) : deriv (e : ℂ → ℂ) z = p.derivative.eval z := by
    -- Replace the automorphism by its polynomial model before differentiating.
    rw [show (e : ℂ → ℂ) = fun w : ℂ ↦ p.eval w by
      funext w
      exact hp w]
    simpa using p.deriv z
  have hp_natDegree_le_one : p.natDegree ≤ 1 := by
    by_contra hdeg
    have hdeg' : 1 < p.natDegree := Nat.lt_of_not_ge hdeg
    have hp_pos : 0 < p.natDegree := lt_trans zero_lt_one hdeg'
    have hderiv_degree_pos : 0 < p.derivative.degree := by
      have hsub_pos : 0 < p.natDegree - 1 := Nat.sub_pos_of_lt hdeg'
      have hsub_pos' : (0 : WithBot ℕ) < (p.natDegree - 1 : ℕ) := by
        exact_mod_cast hsub_pos
      simpa [Polynomial.degree_derivative_eq p hp_pos] using hsub_pos'
    obtain ⟨z₀, hz₀⟩ := Complex.exists_root hderiv_degree_pos
    have hzero : deriv (e : ℂ → ℂ) z₀ = 0 := by
      calc
        deriv (e : ℂ → ℂ) z₀ = p.derivative.eval z₀ := hderiv_eq_eval z₀
        _ = 0 := by
          simpa [Polynomial.IsRoot] using hz₀
    exact deriv_ne_zero_of_holomorphic_isomorph_univ e z₀ hzero
  have hp_linear : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
    exact Polynomial.eq_X_add_C_of_natDegree_le_one hp_natDegree_le_one
  have hcoeff1_ne : p.coeff 1 ≠ 0 := by
    intro hcoeff1_zero
    have hzero : deriv (e : ℂ → ℂ) 0 = 0 := by
      calc
        deriv (e : ℂ → ℂ) 0 = p.derivative.eval 0 := hderiv_eq_eval 0
        _ = 0 := by
          rw [hp_linear]
          simp [hcoeff1_zero]
    exact deriv_ne_zero_of_holomorphic_isomorph_univ e 0 hzero
  -- The polynomial now has degree at most one with nonzero linear coefficient, so it is affine.
  refine ⟨Units.mk0 (p.coeff 1) hcoeff1_ne, p.coeff 0, ?_⟩
  intro z
  calc
    (e : OpenPartialHomeomorph ℂ ℂ) z = p.eval z := hp z
    _ = p.coeff 1 * z + p.coeff 0 := by
      rw [hp_linear]
      simp
    _ = ((Units.mk0 (p.coeff 1) hcoeff1_ne : ℂˣ) : ℂ) * z + p.coeff 0 := rfl

/-- Theorem 2 (2): the affine map `z ↦ a * z + b` with nonzero linear coefficient and its inverse
are entire on `ℂ`. -/
theorem affine_complex_plane_automorphism
    (a : ℂˣ) (b : ℂ) :
    AnalyticOnNhd ℂ (fun z ↦ (a : ℂ) * z + b) Set.univ ∧
      AnalyticOnNhd ℂ (fun z ↦ ((↑a⁻¹ : ℂ) * (z - b))) Set.univ := by
  constructor
  · -- The forward affine map is the evaluation of a linear polynomial.
    have hmul : AnalyticOnNhd ℂ (fun z : ℂ ↦ (a : ℂ) * z) Set.univ := by
      simpa [one_smul] using
        ((analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ ↦ z) Set.univ).const_smul
          (c := (a : ℂ)))
    exact hmul.add analyticOnNhd_const
  · -- The inverse affine map is the evaluation of another linear polynomial.
    have hsub : AnalyticOnNhd ℂ (fun z : ℂ ↦ z - b) Set.univ := by
      exact (analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ ↦ z) Set.univ).sub
        analyticOnNhd_const
    simpa [Pi.smul_apply, sub_eq_add_neg] using
      (hsub.const_smul (c := (↑a⁻¹ : ℂ)))
