import Mathlib
import cartan.V.section18.«0006_Theorem_2»
import cartan.V.section21.«0001_Definition_V_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

local instance (D : Set ℂ) : CoeFun (D → ℂ) fun _ ↦ D → ℂ := ⟨fun f ↦ f⟩

/-- Helper for Lemma 2: a compact subset of the disc `Metric.ball z₀ R` is contained in some
centered closed subdisc of strictly smaller radius. -/
lemma compact_subset_ball_subset_centered_closedBall
    {z₀ : ℂ} {R : ℝ} {K : Set ℂ} (hK : IsCompact K) (hKR : K ⊆ Metric.ball z₀ R) :
    ∃ r : ℝ, r < R ∧ K ⊆ Metric.closedBall z₀ r := by
  by_cases hKe : K.Nonempty
  · -- Control the compact set by the maximum of the distance-to-center function.
    let s : Set ℝ := (fun z : ℂ ↦ ‖z - z₀‖) '' K
    have hs_compact : IsCompact s := by
      refine hK.image_of_continuousOn ?_
      exact (continuous_id.sub continuous_const).norm.continuousOn
    have hs_nonempty : s.Nonempty := by
      rcases hKe with ⟨z, hz⟩
      exact ⟨‖z - z₀‖, ⟨z, hz, rfl⟩⟩
    rcases hs_compact.exists_isGreatest hs_nonempty with ⟨r, hr_mem, hr_max⟩
    refine ⟨r, ?_, ?_⟩
    · rcases hr_mem with ⟨z, hzK, rfl⟩
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hKR hzK
    · intro z hz
      have hzle : ‖z - z₀‖ ≤ r := hr_max ⟨z, hz, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzle
  · -- The empty compact set fits in every centered closed disc.
    refine ⟨R - 1, sub_lt_self _ zero_lt_one, ?_⟩
    simp [Set.not_nonempty_iff_eq_empty.mp hKe]

/-- Helper for Lemma 2: locally uniform convergence on the disc implies convergence at the center
for every iterated derivative sequence. -/
lemma iteratedDeriv_tendsto_at_center_of_tendsto_locally_uniformly
    {z₀ : ℂ} {R : ℝ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hR : 0 < R)
    (hF_diff : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball z₀ R))
    (hconv : TendstoLocallyUniformlyOn F f atTop (Metric.ball z₀ R))
    (n : ℕ) :
    Tendsto (fun k ↦ iteratedDeriv n (F k) z₀) atTop (nhds (iteratedDeriv n f z₀)) := by
  let D : Set ℂ := Metric.ball z₀ R
  have hD_open : IsOpen D := Metric.isOpen_ball
  have hz₀ : z₀ ∈ D := by simpa [D] using hR
  induction n generalizing F f with
  | zero =>
      -- For `n = 0`, this is pointwise convergence at the center.
      simpa using hconv.tendsto_at hz₀
  | succ n ih =>
      -- Differentiate once, keep local uniform convergence, and use the induction hypothesis.
      have hconv_deriv :
          TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) atTop D :=
        tendsto_locally_uniformly_on_compacts_deriv hD_open hF_diff hconv
      have hF_diff' : ∀ k, DifferentiableOn ℂ ((deriv ∘ F) k) D := by
        intro k
        simpa [Function.comp] using (hF_diff k).deriv hD_open
      simpa [Function.comp, iteratedDeriv_succ'] using
        (ih hF_diff' hconv_deriv)

/-- Helper for Lemma 2: on a smaller centered closed disc, Cauchy's estimate gives a geometric
bound for the centered Taylor coefficients. -/
lemma centered_taylor_coefficient_norm_le
    {z₀ : ℂ} {R r₀ M : ℝ} {f : ℂ → ℂ}
    (hr₀ : 0 < r₀) (hr₀R : r₀ < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hM : ∀ z ∈ Metric.closedBall z₀ r₀, ‖f z‖ ≤ M)
    (n : ℕ) :
    ‖((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n f z₀‖ ≤ M / r₀ ^ n := by
  have hM_nonneg : 0 ≤ M := by
    have hz₀_mem : z₀ ∈ Metric.closedBall z₀ r₀ := by
      simpa [Metric.mem_closedBall] using hr₀.le
    exact (norm_nonneg _).trans (hM z₀ hz₀_mem)
  have hclosure :
      closure (Metric.ball z₀ r₀) ⊆ Metric.ball z₀ R := by
    exact Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hr₀R)
  have hdiff_closure : DifferentiableOn ℂ f (closure (Metric.ball z₀ r₀)) := hf.mono hclosure
  have hdiff_ball : DiffContOnCl ℂ f (Metric.ball z₀ r₀) := hdiff_closure.diffContOnCl
  have hSphere : ∀ z ∈ Metric.sphere z₀ r₀, ‖f z‖ ≤ M := by
    intro z hz
    exact hM z (Metric.sphere_subset_closedBall hz)
  have hCauchy :
      ‖iteratedDeriv n f z₀‖ ≤ n.factorial * M / r₀ ^ n :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr₀ hdiff_ball hSphere
  have hfac_nonzero : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  calc
    ‖((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n f z₀‖
        ≤ ‖((Nat.factorial n : ℂ)⁻¹ : ℂ)‖ * ‖iteratedDeriv n f z₀‖ := norm_mul_le _ _
    _ ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * M / r₀ ^ n) := by
      gcongr
      simpa using hCauchy
    _ = M / r₀ ^ n := by
      rw [mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hfac_nonzero, one_mul]

/-- Helper for Lemma 2: convergence of one centered derivative coordinate implies convergence of
the corresponding Taylor coefficient obtained by dividing by `n!`. -/
lemma centered_coefficient_tendsto_of_iteratedDeriv_tendsto
    {z₀ : ℂ} {F : ℕ → ℂ → ℂ} {n : ℕ} {c : ℂ}
    (h : Tendsto (fun k ↦ iteratedDeriv n (F k) z₀) atTop (nhds c)) :
    Tendsto (fun k ↦ ((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n (F k) z₀) atTop
      (nhds (((Nat.factorial n : ℂ)⁻¹) * c)) := by
  -- Multiply the convergent derivative coordinate by the fixed factorial scalar.
  exact ((continuous_const.mul continuous_id).tendsto _).comp h

/-- Helper for Lemma 2: a convergent complex sequence is eventually pairwise small in norm. -/
lemma eventually_pairwise_norm_sub_lt_of_tendsto
    {u : ℕ → ℂ} {c : ℂ} (hu : Tendsto u atTop (nhds c)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ h ≥ N, ‖u k - u h‖ < ε := by
  -- Pass from convergence to the metric Cauchy characterization.
  have hcauchy : CauchySeq u := hu.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  rcases hcauchy ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk h hh
  simpa [dist_eq_norm] using hN k hk h hh

/-- Helper for Lemma 2: finitely many convergent centered coordinates give a uniform Cauchy bound
for any fixed weighted finite head. -/
lemma finite_head_cauchy_bound_from_coordinate_limits
    {a : ℕ → ℕ → ℂ} {w : ℕ → ℝ}
    (hw_nonneg : ∀ n, 0 ≤ w n) {p : ℕ}
    (ha : ∀ n ∈ Finset.range p, ∃ c : ℂ, Tendsto (fun k ↦ a n k) atTop (nhds c))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ h ≥ N,
      ((Finset.range p).sum (fun n ↦ ‖a n k - a n h‖ * w n) ≤ ε) := by
  induction p generalizing ε with
  | zero =>
      -- The empty head contributes no error.
      refine ⟨0, ?_⟩
      intro k hk h hh
      simpa using hε.le
  | succ p ih =>
      -- Separate the finite head into the first `p` terms and the last coordinate.
      have ha_init : ∀ n ∈ Finset.range p, ∃ c : ℂ, Tendsto (fun k ↦ a n k) atTop (nhds c) := by
        intro n hn
        exact ha n (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hn) (Nat.lt_succ_self p)))
      rcases ih ha_init (show 0 < ε / 2 by positivity) with ⟨N₁, hN₁⟩
      by_cases hwp : w p = 0
      · refine ⟨N₁, ?_⟩
        intro k hk h hh
        -- When the last weight is zero, the induction bound already closes the estimate.
        calc
          (Finset.range (p + 1)).sum (fun n ↦ ‖a n k - a n h‖ * w n)
              = (Finset.range p).sum (fun n ↦ ‖a n k - a n h‖ * w n) + ‖a p k - a p h‖ * w p := by
                  rw [Finset.sum_range_succ]
          _ ≤ ε / 2 + 0 := by
            gcongr
            · exact hN₁ k hk h hh
            · simp [hwp]
          _ ≤ ε := by linarith
      · have hwp_ne : w p ≠ 0 := by
          simpa using hwp
        have hwp_pos : 0 < w p := lt_of_le_of_ne (hw_nonneg p) hwp_ne.symm
        rcases ha p (by simp) with ⟨c, hc⟩
        rcases eventually_pairwise_norm_sub_lt_of_tendsto hc
            (show 0 < (ε / 2) / w p by positivity) with ⟨N₂, hN₂⟩
        refine ⟨max N₁ N₂, ?_⟩
        intro k hk h hh
        have hk₁ : N₁ ≤ k := le_trans (le_max_left _ _) hk
        have hh₁ : N₁ ≤ h := le_trans (le_max_left _ _) hh
        have hk₂ : N₂ ≤ k := le_trans (le_max_right _ _) hk
        have hh₂ : N₂ ≤ h := le_trans (le_max_right _ _) hh
        have htail_le : ‖a p k - a p h‖ * w p ≤ ε / 2 := by
          have htail_lt :
              ‖a p k - a p h‖ * w p < ((ε / 2) / w p) * w p := by
            gcongr
            exact hN₂ k hk₂ h hh₂
          have htail_eq : ((ε / 2) / w p) * w p = ε / 2 := by
            field_simp [hwp_ne]
          exact htail_eq ▸ htail_lt.le
        -- Add the induction estimate and the last weighted coordinate.
        calc
          (Finset.range (p + 1)).sum (fun n ↦ ‖a n k - a n h‖ * w n)
              = (Finset.range p).sum (fun n ↦ ‖a n k - a n h‖ * w n) + ‖a p k - a p h‖ * w p := by
                  rw [Finset.sum_range_succ]
          _ ≤ ε / 2 + ε / 2 := add_le_add (hN₁ k hk₁ h hh₁) htail_le
          _ = ε := by ring

/-- Helper for Lemma 2: on a centered closed subdisc, the difference of two Taylor expansions is
bounded by the finite Taylor head plus the textbook geometric tail term. -/
lemma closed_form_pairwise_taylor_head_tail_bound_on_centered_closedBall
    {z₀ : ℂ} {R r r₀ M : ℝ} {f g : ℂ → ℂ}
    (hr_nonneg : 0 ≤ r) (hrr₀ : r < r₀) (hr₀ : 0 < r₀) (hr₀R : r₀ < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hg : DifferentiableOn ℂ g (Metric.ball z₀ R))
    (hM_f : ∀ z ∈ Metric.closedBall z₀ r₀, ‖f z‖ ≤ M)
    (hM_g : ∀ z ∈ Metric.closedBall z₀ r₀, ‖g z‖ ≤ M)
    (p : ℕ) {z : ℂ} (hz : z ∈ Metric.closedBall z₀ r) :
    ‖f z - g z‖ ≤
      (Finset.range (p + 1)).sum (fun n ↦
        ‖((Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n f z₀) -
            ((Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n g z₀)‖ * r ^ n)
        + 2 * M * ((r / r₀) ^ (p + 1)) * (1 - r / r₀)⁻¹ := by
  -- TODO: follow the source proof literally. Expand `f` and `g` by
  -- `Complex.taylorSeries_eq_on_ball'` on `Metric.ball z₀ R`, split each series after `p + 1`
  -- terms using `Summable.sum_add_tsum_nat_add`, and bound the two tails by the geometric majorant
  -- coming from `centered_taylor_coefficient_norm_le`.
  sorry

/-- Helper for Lemma 2: coordinate limits at the center force the sequence to be uniformly Cauchy
on each smaller centered closed disc. -/
lemma uniform_cauchy_on_centered_closedBall_of_coordinate_limits
    {z₀ : ℂ} {R : ℝ} {A : Set (ℂ → ℂ)} {F : ℕ → ℂ → ℂ}
    (hR : 0 < R)
    (hA_holo : ∀ f ∈ A, AnalyticOnNhd ℂ f (Metric.ball z₀ R))
    (hA_bounded :
      UniformlyBoundedOnCompacta (Metric.ball z₀ R) ((Metric.ball z₀ R).restrict '' A))
    (hF_mem : ∀ k, F k ∈ A)
    (hcenter : ∀ n : ℕ, ∃ c : ℂ, Tendsto (fun k ↦ iteratedDeriv n (F k) z₀) atTop (nhds c))
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hrR : r < R) :
    UniformCauchySeqOn F atTop (Metric.closedBall z₀ r) := by
  -- Route correction: the earlier limit-series-first route obscured the textbook proof.
  -- The remaining source-faithful step is the centered closed-ball Cauchy estimate obtained by
  -- splitting both Taylor expansions into a finite head and a geometric tail.
  have hF_diff : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball z₀ R) := by
    intro k
    exact (hA_holo (F k) (hF_mem k)).differentiableOn
  have hcoeff :
      ∀ n : ℕ, ∃ c : ℂ,
        Tendsto (fun k ↦ ((Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n (F k) z₀)) atTop
          (nhds c) := by
    intro n
    rcases hcenter n with ⟨c, hc⟩
    exact ⟨((Nat.factorial n : ℂ)⁻¹) * c,
      centered_coefficient_tendsto_of_iteratedDeriv_tendsto hc⟩
  have hweights_nonneg : ∀ n : ℕ, 0 ≤ r ^ n := by
    intro n
    exact pow_nonneg hr_nonneg n
  have hfinite_head :
      ∀ p : ℕ, ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ, ∀ k ≥ N, ∀ h ≥ N,
          ((Finset.range p).sum
              (fun n ↦
                ‖((Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n (F k) z₀) -
                    ((Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n (F h) z₀)‖ * r ^ n) ≤ ε) := by
    intro p ε hε
    exact finite_head_cauchy_bound_from_coordinate_limits hweights_nonneg
      (fun n hn ↦ hcoeff n) hε
  rcases exists_between hrR with ⟨r₀, hrr₀, hr₀R⟩
  have hr₀ : 0 < r₀ := lt_of_le_of_lt hr_nonneg hrr₀
  have hclosed_sub : Metric.closedBall z₀ r₀ ⊆ Metric.ball z₀ R :=
    Metric.closedBall_subset_ball hr₀R
  have hK_compact : IsCompact (Metric.closedBall z₀ r₀) := isCompact_closedBall _ _
  rcases hA_bounded.exists_bound hK_compact hclosed_sub with ⟨M, hM⟩
  have hbound :
      ∀ k : ℕ, ∀ z ∈ Metric.closedBall z₀ r₀, ‖F k z‖ ≤ M := by
    intro k z hz
    -- Evaluate the common compacta bound on the restricted representative of `F k`.
    simpa [Set.restrict_def] using
      hM ((Metric.ball z₀ R).restrict (F k)) ⟨F k, hF_mem k, rfl⟩ z hz
  have hz₀_mem : z₀ ∈ Metric.closedBall z₀ r₀ := by
    simpa [Metric.mem_closedBall] using hr₀.le
  have hM_nonneg : 0 ≤ M := by
    -- The common bound dominates a nonnegative norm value at the center.
    exact le_trans (norm_nonneg _) (hbound 0 z₀ hz₀_mem)
  have hρ_nonneg : 0 ≤ r / r₀ := div_nonneg hr_nonneg hr₀.le
  have hρ_lt_one : r / r₀ < 1 := by
    rw [div_lt_iff₀ hr₀]
    linarith
  have htail_tendsto_raw :
      Tendsto (fun n : ℕ ↦ (2 * M) * ((r / r₀) ^ n * (1 - r / r₀)⁻¹)) atTop
        (nhds ((2 * M) * (0 * (1 - r / r₀)⁻¹))) := by
    -- The textbook geometric tail tends to zero because `r / r₀ < 1`.
    exact tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nonneg hρ_lt_one).mul tendsto_const_nhds)
  have htail_tendsto :
      Tendsto (fun n : ℕ ↦ (2 * M) * ((r / r₀) ^ n * (1 - r / r₀)⁻¹)) atTop (nhds 0) := by
    simpa using htail_tendsto_raw
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨Ntail, hNtail⟩ := Metric.tendsto_atTop.1 htail_tendsto (ε / 2) (by positivity)
  let p : ℕ := Ntail
  have hp_tail_nonneg :
      0 ≤ 2 * M * (r / r₀) ^ (p + 1) * (1 - r / r₀)⁻¹ := by
    positivity
  have hp_tail :
      2 * M * (r / r₀) ^ (p + 1) * (1 - r / r₀)⁻¹ < ε / 2 := by
    have htail_dist :
        dist ((2 * M) * ((r / r₀) ^ (p + 1) * (1 - r / r₀)⁻¹)) 0 < ε / 2 :=
      hNtail (p + 1) (Nat.le_succ _)
    have hp_tail_nonneg_assoc :
        0 ≤ (2 * M) * ((r / r₀) ^ (p + 1) * (1 - r / r₀)⁻¹) := by
      positivity
    have htail_eq :
        dist ((2 * M) * ((r / r₀) ^ (p + 1) * (1 - r / r₀)⁻¹)) 0 =
          (2 * M) * ((r / r₀) ^ (p + 1) * (1 - r / r₀)⁻¹) := by
      rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg hp_tail_nonneg_assoc]
    rw [htail_eq] at htail_dist
    simpa [mul_assoc] using htail_dist
  obtain ⟨N, hN⟩ := hfinite_head (p + 1) (show 0 < ε / 2 by positivity)
  refine ⟨N, ?_⟩
  intro k hk h hh z hz
  rw [dist_eq_norm]
  -- Combine the textbook Taylor head-tail estimate with the finite-head Cauchy bound.
  have hpair_le :
      ‖F k z - F h z‖ ≤
        (Finset.range (p + 1)).sum (fun n ↦
            ‖((Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n (F k) z₀) -
                ((Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n (F h) z₀)‖ * r ^ n)
          + 2 * M * (r / r₀) ^ (p + 1) * (1 - r / r₀)⁻¹ := by
    exact closed_form_pairwise_taylor_head_tail_bound_on_centered_closedBall
      hr_nonneg hrr₀ hr₀ hr₀R (hF_diff k) (hF_diff h) (hbound k) (hbound h) p
      (show z ∈ Metric.closedBall z₀ r by exact hz)
  have htotal_lt :
      ‖F k z - F h z‖ < ε / 2 + ε / 2 := by
    exact lt_of_le_of_lt hpair_le (add_lt_add_of_le_of_lt (hN k hk h hh) hp_tail)
  simpa using htotal_lt

-- Domain sampling: this item lies in one-variable complex analysis on discs, with the compacta
-- convergence owner `TendstoLocallyUniformlyOn` and the section-21 bounded-family owner
-- `UniformlyBoundedOnCompacta`.
-- Relevant declarations checked before refinement:
-- * `UniformlyBoundedOnCompacta` for bounded families on compact subsets of a domain;
-- * `analyticFunctionSubring ℂ D` as the chapter's restriction-space carrier for holomorphic
--   functions;
-- * `TendstoLocallyUniformlyOn.deriv` for derivative stability under locally uniform convergence;
-- * `Complex.taylorSeries_eq_on_ball'` for recovery of a holomorphic function on a disc from its
--   centered iterated derivatives.
-- Primitive data here: ambient holomorphic functions `ℂ → ℂ` on the disc, needed for
-- `iteratedDeriv n f z₀`. Derived API: compacta-boundedness, which depends only on the restricted
-- family on the disc and should therefore use `UniformlyBoundedOnCompacta` instead of a bespoke
-- quantifier block.

/-- Lemma 2: let `A` be a bounded family of holomorphic functions on the open disc centered at
`z₀` with radius `R`. Then a sequence `F k` in `A` converges uniformly on compact subsets of that
disc if and only if, for every `n`, the sequence of values at `z₀` of the `n`-th derivatives
`iteratedDeriv n (F k) z₀` converges. For `n = 0`, this is the convergence of the values
`F k z₀`. -/
theorem disc_sequence_tendsto_locally_uniformly_iff_iteratedDeriv_tendsto_at_center
    {z₀ : ℂ} {R : ℝ} (hR : 0 < R) {A : Set (ℂ → ℂ)} {F : ℕ → ℂ → ℂ}
    (hA_holo : ∀ f ∈ A, AnalyticOnNhd ℂ f (Metric.ball z₀ R))
    (hA_bounded :
      UniformlyBoundedOnCompacta (Metric.ball z₀ R) ((Metric.ball z₀ R).restrict '' A))
    (hF_mem : ∀ k, F k ∈ A) :
    (∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f atTop (Metric.ball z₀ R)) ↔
      ∀ n : ℕ, ∃ c : ℂ, Tendsto (fun k ↦ iteratedDeriv n (F k) z₀) atTop (nhds c) := by
  constructor
  · rintro ⟨f, hconv⟩ n
    -- The easy direction iterates the derivative-stability theorem from section 18.
    refine ⟨iteratedDeriv n f z₀, ?_⟩
    have hF_diff : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball z₀ R) := by
      intro k
      exact (hA_holo (F k) (hF_mem k)).differentiableOn
    exact iteratedDeriv_tendsto_at_center_of_tendsto_locally_uniformly hR hF_diff hconv n
  · intro hcenter
    -- Reverse direction: use the textbook Taylor/Cauchy argument on centered closed subdiscs.
    classical
    have hF_diff : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball z₀ R) := by
      intro k
      exact (hA_holo (F k) (hF_mem k)).differentiableOn
    have hclosed_cauchy :
        ∀ {r : ℝ}, 0 ≤ r → r < R → UniformCauchySeqOn F atTop (Metric.closedBall z₀ r) := by
      intro r hr_nonneg hrR
      exact uniform_cauchy_on_centered_closedBall_of_coordinate_limits
        hR hA_holo hA_bounded hF_mem hcenter hr_nonneg hrR
    have hpoint :
        ∀ x ∈ Metric.ball z₀ R, ∃ c : ℂ, Tendsto (fun k ↦ F k x) atTop (nhds c) := by
      intro x hx
      let r : ℝ := (‖x - z₀‖ + R) / 2
      have hx_lt : ‖x - z₀‖ < R := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      have hr_nonneg : 0 ≤ r := by
        dsimp [r]
        positivity
      have hrR : r < R := by
        dsimp [r]
        linarith
      have hx_closed : x ∈ Metric.closedBall z₀ r := by
        simp [Metric.mem_closedBall, dist_eq_norm, r]
        linarith
      -- Each point belongs to some smaller centered closed disc, so uniform Cauchy there gives
      -- an ordinary Cauchy sequence of complex numbers.
      exact cauchySeq_tendsto_of_complete ((hclosed_cauchy hr_nonneg hrR).cauchySeq hx_closed)
    let f : ℂ → ℂ := fun x ↦
      if hx : x ∈ Metric.ball z₀ R then Classical.choose (hpoint x hx) else 0
    refine ⟨f, (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).2 ?_⟩
    intro K hKD hK
    by_cases hKe : K.Nonempty
    · rcases compact_subset_ball_subset_centered_closedBall hK hKD with ⟨r, hrR, hKr⟩
      have hr_nonneg : 0 ≤ r := by
        rcases hKe with ⟨x, hx⟩
        have hxle : ‖x - z₀‖ ≤ r := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hKr hx
        exact le_trans (norm_nonneg _) hxle
      have hclosed_tendsto :
          TendstoUniformlyOn F f atTop (Metric.closedBall z₀ r) := by
        -- On the containing closed disc, combine uniform Cauchy with the pointwise limits.
        refine (hclosed_cauchy hr_nonneg hrR).tendstoUniformlyOn_of_tendsto ?_
        intro x hx
        have hxD : x ∈ Metric.ball z₀ R := Metric.closedBall_subset_ball hrR hx
        have hxDist : dist x z₀ < R := by
          simpa [Metric.mem_ball] using hxD
        have hfx : f x = Classical.choose (hpoint x hxD) := by
          simp [f, Metric.mem_ball, hxDist]
        simpa [hfx] using Classical.choose_spec (hpoint x hxD)
      exact hclosed_tendsto.mono hKr
    · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKe
      simpa [hKempty] using (tendstoUniformlyOn_empty : TendstoUniformlyOn F f atTop ∅)
