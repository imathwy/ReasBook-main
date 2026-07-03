import Mathlib
import cartan.III.section11.«0008_Proposition_4_1»
import cartan.III.section12.«0031_Exercise_19»
import cartan.IV.section17.«0012_Exercise_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeromorphicOn Metric
open scoped BigOperators Topology

noncomputable section

-- Domain sampling: these declarations are source-facing one-variable complex-analysis consequences
-- of the canonical convergence owner `TendstoLocallyUniformlyOn`, the oriented-boundary zero-count
-- theorem `rouche_theorem_on_oriented_boundary`, the zero-count owner `MeromorphicOn.divisor`, and
-- the local analytic owners `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` and
-- `AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`. Primitive data for part (3) is the
-- local nontriviality of `f` near the fixed zero `a`, not a global preconnected-domain hypothesis.
-- The file therefore keeps only the textbook theorem surfaces, with no parallel local zero-count
-- or compact-convergence wrapper API.

universe u

section

variable {D K : Set ℂ}
variable {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}

/-- Helper for Exercise 2: on the compact boundary of `K`, the holomorphic limit `f` stays
uniformly away from `0`, so locally uniform convergence forces `F n - f` to be strictly smaller
than `f` there for all large `n`. -/
lemma eventually_boundary_error_lt_limit_norm
    (hD_open : IsOpen D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f atTop D)
    (hKD : K ⊆ D)
    (hK : IsCompact K)
    (hboundary : ∀ z ∈ frontier K, f z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ frontier K, ‖F n z - f z‖ < ‖f z‖ := by
  have hf_diff : DifferentiableOn ℂ f D :=
    hconv.differentiableOn (Eventually.of_forall hF) hD_open
  have hfrontier_sub : frontier K ⊆ D := by
    intro z hz
    exact hKD (hK.isClosed.frontier_subset hz)
  have hfrontier_compact : IsCompact (frontier K) :=
    IsCompact.of_isClosed_subset hK isClosed_frontier hK.isClosed.frontier_subset
  by_cases hfrontier_nonempty : (frontier K).Nonempty
  · have hnorm_cont : ContinuousOn (fun z ↦ ‖f z‖) (frontier K) :=
      continuous_norm.comp_continuousOn (hf_diff.continuousOn.mono hfrontier_sub)
    obtain ⟨z₀, hz₀, hz₀_min⟩ :=
      hfrontier_compact.exists_isMinOn hfrontier_nonempty hnorm_cont
    let ε : ℝ := ‖f z₀‖
    have hε_pos : 0 < ε := by
      simp [ε, hboundary z₀ hz₀]
    have hfrontier_conv : TendstoUniformlyOn F f atTop (frontier K) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).mp hconv
        (frontier K) hfrontier_sub hfrontier_compact
    rw [Metric.tendstoUniformlyOn_iff] at hfrontier_conv
    rcases Filter.eventually_atTop.1 (hfrontier_conv ε hε_pos) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn z hz
    have hε_le : ε ≤ ‖f z‖ := by
      simpa [ε] using hz₀_min hz
    exact lt_of_lt_of_le
      (by simpa [dist_eq_norm, norm_sub_rev] using hN n hn z hz)
      hε_le
  · refine ⟨0, ?_⟩
    intro n hn z hz
    exact False.elim (hfrontier_nonempty ⟨z, hz⟩)

/-- Helper for Exercise 2: if an analytic function is nonvanishing on the whole compact owner,
then its divisor on that owner is identically zero, so the total divisor sum vanishes. -/
lemma divisor_sum_eq_zero_of_analytic_nonvanishing_on_compact
    {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g K)
    (hnonzero : ∀ z ∈ K, g z ≠ 0) :
    ∑ᶠ z, divisor g K z = 0 := by
  have hdiv_zero : divisor g K = 0 := by
    ext z
    by_cases hz : z ∈ K
    · simpa using
        (divisor_eq_zero_of_analyticOnNhd_nonvanishing hg hz (hnonzero z hz))
    · simp [hz]
  simpa [hdiv_zero]

/-- Helper for Exercise 2: on a closed disc where `f` vanishes only at the center `a`, the whole
divisor sum reduces to the central divisor coefficient, and that coefficient is nonzero. -/
lemma divisor_sum_eq_divisor_at_center_of_nonvanishing_off_center
    {a : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hfK : AnalyticOnNhd ℂ f (closedBall a r))
    (hfa : f a = 0)
    (hpunct : ∀ z ∈ closedBall a r, z ≠ a → f z ≠ 0) :
    ∑ᶠ z, divisor f (closedBall a r) z = divisor f (closedBall a r) a ∧
      divisor f (closedBall a r) a ≠ 0 := by
  classical
  have hsupport_singleton :
      (divisor f (closedBall a r)).support ⊆ ({a} : Set ℂ) := by
    intro z hz
    have hz_ball : z ∈ closedBall a r := by
      by_contra hz_ball
      rw [Function.mem_support] at hz
      simp [MeromorphicOn.divisor_def, hz_ball] at hz
    by_contra hza
    have hdiv_zero :
        divisor f (closedBall a r) z = 0 :=
      divisor_eq_zero_of_analyticOnNhd_nonvanishing
        hfK hz_ball (hpunct z hz_ball hza)
    rw [Function.mem_support] at hz
    exact hz hdiv_zero
  have hsum_eq :
      ∑ᶠ z, divisor f (closedBall a r) z = divisor f (closedBall a r) a := by
    rw [finsum_eq_sum_of_support_subset (s := ({a} : Finset ℂ))]
    · simp
    · intro z hz
      simpa using hsupport_singleton hz
  have ha_closed : a ∈ closedBall a r := by
    simp [Metric.mem_closedBall, le_of_lt hr]
  have hcenter_analytic : AnalyticAt ℂ f a := hfK a ha_closed
  have hcenter_order_ne_zero : analyticOrderAt f a ≠ 0 :=
    (hcenter_analytic.analyticOrderAt_ne_zero).2 hfa
  have hcenter_order_ne_top : analyticOrderAt f a ≠ ⊤ := by
    intro htop
    have hzero_nhds : ∀ᶠ z in 𝓝 a, f z = 0 := analyticOrderAt_eq_top.mp htop
    rcases Metric.mem_nhds_iff.mp hzero_nhds with ⟨δ, hδ_pos, hδ_zero⟩
    let t : ℝ := min (δ / 2) (r / 2)
    have ht_pos : 0 < t := by
      refine lt_min ?_ ?_
      · exact half_pos hδ_pos
      · exact half_pos hr
    have ht_lt_δ : t < δ := by
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
    have ht_le_r : t ≤ r := by
      exact le_trans (min_le_right _ _) (by nlinarith [hr])
    let z : ℂ := a + t
    have hz_zero : f z = 0 :=
      hδ_zero (by
        simp [z, Metric.mem_ball, dist_eq_norm, abs_of_nonneg (le_of_lt ht_pos), ht_lt_δ])
    have hz_closed : z ∈ closedBall a r := by
      simp [z, Metric.mem_closedBall, dist_eq_norm, abs_of_nonneg (le_of_lt ht_pos), ht_le_r]
    have hz_ne : z ≠ a := by
      have htnz : (t : ℂ) ≠ 0 := by exact_mod_cast ht_pos.ne'
      intro hza
      apply htnz
      simpa [z, sub_eq_iff_eq_add] using congrArg (fun w : ℂ ↦ w - a) hza
    exact (hpunct z hz_closed hz_ne) hz_zero
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hcenter_order_ne_top
  have hm_ne_zero : m ≠ 0 := by
    intro hm_zero
    apply hcenter_order_ne_zero
    simpa [hm_zero] using hm.symm
  have hcenter_divisor_eq : divisor f (closedBall a r) a = (m : ℤ) := by
    rw [hfK.divisor_apply ha_closed, ← hm]
    simp
  have hcenter_divisor_ne_zero : divisor f (closedBall a r) a ≠ 0 := by
    rw [hcenter_divisor_eq]
    exact_mod_cast hm_ne_zero
  exact ⟨hsum_eq, hcenter_divisor_ne_zero⟩

/-- Exercise 2 (1): if `F n` converges locally uniformly on `D` to a limit `f`, and if `f` has no
zeros on the boundary of a compact subset `K ⊆ D`, then all sufficiently large `F n` are also
nonvanishing on that boundary. -/
theorem exercise2_eventually_nonvanishing_on_boundary
    (hD_open : IsOpen D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f atTop D)
    (hKD : K ⊆ D)
    (hK : IsCompact K)
    (hboundary : ∀ z ∈ frontier K, f z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ frontier K, F n z ≠ 0 := by
  obtain ⟨N, hN⟩ :=
    eventually_boundary_error_lt_limit_norm hD_open hF hconv hKD hK hboundary
  refine ⟨N, ?_⟩
  intro n hn z hz hzero
  have hlt := hN n hn z hz
  have heq : ‖F n z - f z‖ = ‖f z‖ := by
    simp [hzero]
  exact (lt_irrefl ‖f z‖) (by simpa [heq] using hlt)

/-- Exercise 2 (2): under the same hypotheses, once `F n` is close enough to `f` on the oriented
boundary of `K`, the functions `F n` and `f` have the same number of zeros in `K`, expressed
canonically as equality of the divisor sums on `K`. -/
theorem exercise2_eventually_same_zero_count_in_compact
    {ι : Type u} [Fintype ι] {Γ : ι → ClosedPath ℂ}
    (hD_open : IsOpen D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f atTop D)
    (hKD : K ⊆ D)
    (hΓ : IsOrientedBoundaryOf K Γ)
    (hboundary : ∀ z ∈ frontier K, f z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∑ᶠ z, divisor (F n) K z = ∑ᶠ z, divisor f K z := by
  have hf_diff : DifferentiableOn ℂ f D :=
    hconv.differentiableOn (Eventually.of_forall hF) hD_open
  have hfK : AnalyticOnNhd ℂ f K :=
    (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 hf_diff |>.mono hKD
  obtain ⟨N, hN⟩ :=
    eventually_boundary_error_lt_limit_norm hD_open hF hconv hKD hΓ.isCompact hboundary
  refine ⟨N, ?_⟩
  intro n hn
  have hFnK : AnalyticOnNhd ℂ (F n) K :=
    (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 (hF n) |>.mono hKD
  have hdiffK : AnalyticOnNhd ℂ (fun z ↦ F n z - f z) K := hFnK.sub hfK
  -- Apply Rouché to `f` and the error term `F n - f` on the oriented boundary.
  have hsum :
      ∑ᶠ z, divisor (fun z ↦ f z + (F n z - f z)) K z = ∑ᶠ z, divisor f K z :=
    rouche_theorem_on_oriented_boundary Γ hΓ hfK hdiffK (hN n hn)
  have hfun : (fun z ↦ f z + (F n z - f z)) = F n := by
    funext z
    abel
  calc
    ∑ᶠ z, divisor (F n) K z
        = ∑ᶠ z, divisor (fun z ↦ f z + (F n z - f z)) K z := by
            simp [hfun]
    _ = ∑ᶠ z, divisor f K z := hsum

/-- Helper for Exercise 2: on every sufficiently small closed disc around an isolated zero `a` of
`f`, every large `F n` has at least one zero in that closed disc. -/
lemma eventually_has_zero_in_closedBall_of_isolated_limit_zero
    {a : ℂ} {r : ℝ}
    (hD_open : IsOpen D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f atTop D)
    (hr : 0 < r)
    (hclosedD : closedBall a r ⊆ D)
    (hfa : f a = 0)
    (hpunct : ∀ z ∈ closedBall a r, z ≠ a → f z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ closedBall a r, F n z = 0 := by
  have hf_diff : DifferentiableOn ℂ f D :=
    hconv.differentiableOn (Eventually.of_forall hF) hD_open
  have hfK : AnalyticOnNhd ℂ f (closedBall a r) :=
    (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 hf_diff |>.mono hclosedD
  have hboundary_nonzero : ∀ z ∈ frontier (closedBall a r), f z ≠ 0 := by
    intro z hz
    rw [frontier_closedBall a hr.ne'] at hz
    exact hpunct z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne')
  obtain ⟨Ncount, hNcount⟩ :=
    exercise2_eventually_same_zero_count_in_compact
      (D := D) (K := closedBall a r)
      (F := F) (f := f)
      (Γ := fun _ : Unit ↦ (positive_circle_path a r).toClosedPath)
      hD_open hF hconv hclosedD
      (closedBallBoundary_isOrientedBoundaryOf hr)
      hboundary_nonzero
  obtain ⟨hsum_eq_center, hcenter_ne_zero⟩ :=
    divisor_sum_eq_divisor_at_center_of_nonvanishing_off_center hr hfK hfa hpunct
  have hsumf_ne_zero : ∑ᶠ z, divisor f (closedBall a r) z ≠ 0 := by
    rw [hsum_eq_center]
    exact hcenter_ne_zero
  refine ⟨Ncount, ?_⟩
  intro n hn
  by_contra hnozero
  have hFnK : AnalyticOnNhd ℂ (F n) (closedBall a r) :=
    (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 (hF n) |>.mono hclosedD
  have hFn_nonzero : ∀ z ∈ closedBall a r, F n z ≠ 0 := by
    intro z hz
    intro hFnz
    exact hnozero ⟨z, hz, hFnz⟩
  have hsumFn_zero :
      ∑ᶠ z, divisor (F n) (closedBall a r) z = 0 :=
    divisor_sum_eq_zero_of_analytic_nonvanishing_on_compact hFnK hFn_nonzero
  have hsumf_zero : ∑ᶠ z, divisor f (closedBall a r) z = 0 := by
    calc
      ∑ᶠ z, divisor f (closedBall a r) z
          = ∑ᶠ z, divisor (F n) (closedBall a r) z := by
              symm
              exact hNcount n hn
      _ = 0 := hsumFn_zero
  exact hsumf_ne_zero hsumf_zero

/-- Exercise 2 (3): if `a` is a zero of the limit function `f` and `f` is not identically zero in
any neighborhood of `a`, then after discarding finitely many initial indices one can choose zeros
of the approximating functions `F n` in `D` that converge to `a`. This is the tail-sequence form
forced by the index-shift issue for the finitely many initial terms. -/
theorem exercise2_eventually_zero_sequence_tendsto
    {a : ℂ}
    (hD_open : IsOpen D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f atTop D)
    (hf_not_eventually_zero : ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (ha : a ∈ D) (hfa : f a = 0) :
    ∃ N : ℕ, ∃ aSeq : ℕ → D,
      Tendsto (fun n ↦ (aSeq n : ℂ)) atTop (𝓝 a) ∧
      ∀ n, F (n + N) (aSeq n) = 0 := by
  classical
  have hf_diff : DifferentiableOn ℂ f D :=
    hconv.differentiableOn (Eventually.of_forall hF) hD_open
  have hf_analytic : AnalyticOnNhd ℂ f D :=
    (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 hf_diff
  have hf_punctured_nonzero : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
    rcases (hf_analytic a ha).eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
    · exact False.elim (hf_not_eventually_zero hzero)
    · exact hnonzero
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds ha) with ⟨ρD, hρD_pos, hρD_sub⟩
  rcases Metric.mem_nhdsWithin_iff.mp hf_punctured_nonzero with ⟨δ, hδ_pos, hδ_nonzero⟩
  let ρ : ℝ := min (δ / 2) (ρD / 2)
  have hρ_pos : 0 < ρ := by
    refine lt_min ?_ ?_
    · exact half_pos hδ_pos
    · exact half_pos hρD_pos
  have hρ_lt_δ : ρ < δ := by
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
  have hρ_lt_ρD : ρ < ρD := by
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρD_pos)
  have hclosed_ρ_sub : closedBall a ρ ⊆ D := (closedBall_subset_ball hρ_lt_ρD).trans hρD_sub
  have hρ_punctured_nonzero :
      ∀ z ∈ closedBall a ρ, z ≠ a → f z ≠ 0 := by
    intro z hz hza
    exact hδ_nonzero ⟨(closedBall_subset_ball hρ_lt_δ) hz, hza⟩
  let radius : ℕ → ℝ := fun m ↦ ρ * (1 / (m + 1 : ℝ))
  have hradius_pos : ∀ m, 0 < radius m := by
    intro m
    dsimp [radius]
    positivity
  have hradius_le_ρ : ∀ m, radius m ≤ ρ := by
    intro m
    dsimp [radius]
    have hdiv_le : 1 / ((m : ℝ) + 1) ≤ 1 := by
      have hm_one : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hm_one)
    calc
      ρ * (1 / ((m : ℝ) + 1)) ≤ ρ * 1 := by
        exact mul_le_mul_of_nonneg_left hdiv_le (le_of_lt hρ_pos)
      _ = ρ := by ring
  have hradius_antitone : Antitone radius := by
    intro m n hmn
    dsimp [radius]
    have hdiv :
        1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    exact mul_le_mul_of_nonneg_left hdiv (le_of_lt hρ_pos)
  have hzero_tail :
      ∀ m, ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ closedBall a (radius m), F n z = 0 := by
    intro m
    refine eventually_has_zero_in_closedBall_of_isolated_limit_zero
      hD_open hF hconv (hradius_pos m) ?_ hfa ?_
    · exact (closedBall_subset_closedBall (hradius_le_ρ m)).trans hclosed_ρ_sub
    · intro z hz hza
      exact hρ_punctured_nonzero z ((closedBall_subset_closedBall (hradius_le_ρ m)) hz) hza
  choose threshold hthreshold using hzero_tail
  let N : ℕ := threshold 0
  let level : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun m ↦ threshold m ≤ n + N) (n + N)
  have hlevel_threshold : ∀ n, threshold (level n) ≤ n + N := by
    intro n
    unfold level
    have hzero : threshold 0 ≤ n + N := by
      simpa [N, add_comm, add_left_comm, add_assoc] using Nat.le_add_left (threshold 0) n
    exact Nat.findGreatest_spec
      (P := fun m ↦ threshold m ≤ n + N) (m := 0) (n := n + N) (Nat.zero_le _) hzero
  let zeroPoint : ℕ → ℂ :=
    fun n ↦ Classical.choose (hthreshold (level n) (n + N) (hlevel_threshold n))
  have hzeroPoint_mem : ∀ n, zeroPoint n ∈ closedBall a (radius (level n)) := by
    intro n
    exact (Classical.choose_spec (hthreshold (level n) (n + N) (hlevel_threshold n))).1
  have hzeroPoint_zero : ∀ n, F (n + N) (zeroPoint n) = 0 := by
    intro n
    exact (Classical.choose_spec (hthreshold (level n) (n + N) (hlevel_threshold n))).2
  let aSeq : ℕ → D := fun n ↦
    ⟨zeroPoint n,
      hclosed_ρ_sub ((closedBall_subset_closedBall (hradius_le_ρ (level n))) (hzeroPoint_mem n))⟩
  have haSeq_tendsto : Tendsto (fun n ↦ (aSeq n : ℂ)) atTop (𝓝 a) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / ρ by positivity)
    have hradius_lt_ε : radius m < ε := by
      have hm' := mul_lt_mul_of_pos_left hm hρ_pos
      have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
      simpa [radius, div_eq_mul_inv, hρ_ne, mul_assoc, mul_left_comm, mul_comm] using hm'
    refine Filter.eventually_atTop.2 ⟨max m (threshold m), ?_⟩
    intro n hn
    have hm_le_n : m ≤ n := le_trans (le_max_left _ _) hn
    have hthreshold_le_n : threshold m ≤ n := le_trans (le_max_right _ _) hn
    have hm_le_level : m ≤ level n := by
      unfold level
      refine Nat.le_findGreatest ?_ ?_
      · exact le_trans hm_le_n (Nat.le_add_right n N)
      · exact le_trans hthreshold_le_n (Nat.le_add_right n N)
    have hdist_le :
        dist (aSeq n : ℂ) a ≤ radius (level n) := by
      simpa [aSeq, zeroPoint, Metric.mem_closedBall, dist_comm] using hzeroPoint_mem n
    exact lt_of_le_of_lt
      (le_trans hdist_le (hradius_antitone hm_le_level))
      hradius_lt_ε
  refine ⟨N, aSeq, haSeq_tendsto, ?_⟩
  intro n
  simpa [aSeq] using hzeroPoint_zero n

end
