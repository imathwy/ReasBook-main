import cartan.V.section18.«0004_Theorem_1»
import cartan.V.section18.«0006_Theorem_2»
import cartan.V.section19.«0001_Definition_V_2_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Metric Set
open scoped Topology

section Uniform

variable {D K : Set ℂ} {f : ℕ → ℂ → ℂ}

/-- Helper for Theorem V.2-extra-2: uniform convergence on the compact closure of an open buffer
implies locally uniform convergence on the buffer itself. -/
lemma tail_tendsto_locally_uniformly_on_of_summable_uniformly_on_closure
    {V : Set ℂ} (hV : IsOpen V) {g : ℕ → ℂ → ℂ}
    (hS : SummableUniformlyOn g (closure V)) :
    TendstoLocallyUniformlyOn
      (fun m z ↦ ∑ n ∈ Finset.range m, g n z)
      (fun z ↦ ∑' n, g n z)
      atTop V := by
  -- Restrict the uniform convergence on `closure V` to each compact subset of `V`.
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hV]
  intro K hKV hK
  have hKclosure : K ⊆ closure V := fun z hz ↦ subset_closure (hKV hz)
  exact (hS.hasSumUniformlyOn.mono hKclosure).tendstoUniformlyOn_finsetRange

/-- Helper for Theorem V.2-extra-2: if every term of a tail is analytic on the closure of an open
buffer and the tail converges uniformly there, then the tail sum is holomorphic on the buffer. -/
lemma tail_tsum_differentiable_on_buffer
    {V : Set ℂ} (hV : IsOpen V) {g : ℕ → ℂ → ℂ}
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (g n) (closure V))
    (hS : SummableUniformlyOn g (closure V)) :
    DifferentiableOn ℂ (fun z ↦ ∑' n, g n z) V := by
  -- Each term is holomorphic on `V`, so the finite partial sums are holomorphic there as well.
  have hg_diff : ∀ n, DifferentiableOn ℂ (g n) V := by
    intro n
    exact ((hanalytic n).mono subset_closure).differentiableOn
  have hpartial : ∀ m, DifferentiableOn ℂ (fun z ↦ ∑ n ∈ Finset.range m, g n z) V := by
    intro m
    exact DifferentiableOn.fun_sum fun n _ ↦ hg_diff n
  -- The chapter-18 compact-uniform limit theorem now gives holomorphy of the tail sum.
  exact
    differentiableOn_of_tendsto_locally_uniformly_on_compacts hV hpartial
      (tail_tendsto_locally_uniformly_on_of_summable_uniformly_on_closure hV hS)

/-- Helper for Theorem V.2-extra-2: inside an open buffer with compact closure, the derivative
series of an analytic tail converges uniformly on each compact subset to the derivative of the tail
sum. -/
lemma hasSumUniformlyOn_deriv_tail_on_buffer
    {K V : Set ℂ} (hKV : K ⊆ V) (hK : IsCompact K) (hV : IsOpen V)
    {g : ℕ → ℂ → ℂ}
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (g n) (closure V))
    (hS : SummableUniformlyOn g (closure V)) :
    HasSumUniformlyOn
      (fun n z ↦ deriv (g n) z)
      (deriv (fun z ↦ ∑' n, g n z))
      K := by
  -- Route correction: instead of upgrading an ordered derivative limit directly, differentiate the
  -- original partial sums on a compact thickening and only then rewrite the Cauchy derivative back
  -- to `deriv` on `K`.
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hV hKV
  -- Every tail term is holomorphic on the open buffer, hence every finite partial sum is too.
  have hg_diff : ∀ n, DifferentiableOn ℂ (g n) V := by
    intro n
    exact ((hanalytic n).mono subset_closure).differentiableOn
  have hsubset : cthickening δ K ⊆ closure V := fun z hz ↦ subset_closure (hKδ hz)
  have htail_tendsto :
      TendstoUniformlyOn
        (fun s z ↦ ∑ n ∈ s, g n z)
        (fun z ↦ ∑' n, g n z)
        atTop
        (cthickening δ K) :=
    (hS.hasSumUniformlyOn.mono hsubset).tendstoUniformlyOn
  -- The Cauchy derivative operator is continuous for uniform convergence on the thickening.
  have hpartial_cont :
      ∀ᶠ s : Finset ℕ in atTop,
        ContinuousOn (fun z ↦ ∑ n ∈ s, g n z) (cthickening δ K) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    exact (DifferentiableOn.fun_sum fun n _ ↦ (hg_diff n).mono hKδ).continuousOn
  have hcderiv_tendsto :
      TendstoUniformlyOn
        (fun s z ↦ Complex.cderiv δ (fun w ↦ ∑ n ∈ s, g n w) z)
        (fun z ↦ Complex.cderiv δ (fun z ↦ ∑' n, g n z) z)
        atTop
        K :=
    htail_tendsto.cderiv hδ hpartial_cont
  -- Rewrite each differentiated finite partial sum as the finite sum of the differentiated terms.
  have hpartial_eq :
      ∀ᶠ s : Finset ℕ in atTop,
        K.EqOn
          (fun z ↦ Complex.cderiv δ (fun w ↦ ∑ n ∈ s, g n w) z)
          (fun z ↦ ∑ n ∈ s, deriv (g n) z) := by
    refine Filter.Eventually.of_forall ?_
    intro s z hz
    calc
      Complex.cderiv δ (fun w ↦ ∑ n ∈ s, g n w) z
          = deriv (fun w ↦ ∑ n ∈ s, g n w) z := by
              exact Complex.cderiv_eq_deriv hV
                (DifferentiableOn.fun_sum fun n _ ↦ hg_diff n) hδ
                ((closedBall_subset_cthickening hz δ).trans hKδ)
      _ = ∑ n ∈ s, deriv (g n) z := by
        simpa using
          (deriv_fun_sum (u := s) (A := g) (x := z) fun n _ ↦
            (hg_diff n z (hKV hz)).differentiableAt (hV.mem_nhds (hKV hz)))
  have htsum_diff : DifferentiableOn ℂ (fun z ↦ ∑' n, g n z) V :=
    tail_tsum_differentiable_on_buffer hV hanalytic hS
  -- On `K`, the Cauchy-derivative operator agrees with the genuine derivative of the tail sum.
  have hlimit_eq :
      K.EqOn
        (fun z ↦ Complex.cderiv δ (fun z ↦ ∑' n, g n z) z)
        (deriv (fun z ↦ ∑' n, g n z)) := by
    intro z hz
    exact Complex.cderiv_eq_deriv hV htsum_diff hδ
      ((closedBall_subset_cthickening hz δ).trans hKδ)
  -- The canonical `HasSumUniformlyOn` owner is exactly the convergence of all finite partial sums.
  exact
    hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
      ((hcderiv_tendsto.congr hpartial_eq).congr_right hlimit_eq)

/-- Helper for Theorem V.2-extra-2: a normal tail bound on a closed thickening yields a uniform
majorant for the derivatives on the original compact set. -/
lemma deriv_tail_majorized_on_compact_of_normal_tail_bound
    {K : Set ℂ} {ε : ℝ} (hε : 0 < ε) {g : ℕ → ℂ → ℂ} {u : ℕ → NNReal}
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (g n) (cthickening ε K))
    (hubound : ∀ n z, z ∈ cthickening ε K → ‖g n z‖ ≤ (u n : ℝ)) :
    ∃ c : NNReal, ∀ n z, z ∈ K → ‖deriv (g n) z‖ ≤ (u n * c : NNReal) := by
  let c : NNReal := ⟨ε⁻¹, by positivity⟩
  refine ⟨c, ?_⟩
  intro n z hz
  -- Apply the Cauchy estimate on the radius-`ε` ball centered at `z`.
  have hsub : closedBall z ε ⊆ cthickening ε K := closedBall_subset_cthickening hz ε
  have hdiff : DiffContOnCl ℂ (g n) (ball z ε) := by
    have hg_diff : DifferentiableOn ℂ (g n) (cthickening ε K) := (hanalytic n).differentiableOn
    exact hg_diff.diffContOnCl_ball hsub
  have hsphere :
      ∀ w ∈ sphere z ε, ‖g n w‖ ≤ (u n : ℝ) := by
    intro w hw
    exact hubound n w (hsub (sphere_subset_closedBall hw))
  have hderiv : ‖deriv (g n) z‖ ≤ (u n : ℝ) / ε :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε hdiff hsphere
  have hc :
      ((u n * c : NNReal) : ℝ) = (u n : ℝ) / ε := by
    rw [NNReal.coe_mul, show (c : ℝ) = ε⁻¹ by rfl, div_eq_mul_inv]
  rw [hc]
  exact hderiv

/-- Theorem V.2-extra-2 (1): if a series of meromorphic functions on an open set `D` is uniformly
convergent on compact subsets of `D` in the source tail-holomorphic sense, then its sum is
meromorphic on `D`. -/
theorem meromorphicOn_tsum_of_meromorphic_series_uniformly_convergent_on_compacts
    (huniform : MeromorphicSeriesUniformlyConvergentOnCompacta f D) :
    MeromorphicOn (fun z : ℂ ↦ ∑' n : ℕ, f n z) D := by
  intro x hx
  -- Choose a relatively compact open buffer around `x`.
  obtain ⟨ε, hε, hεD⟩ :=
    (isCompact_singleton (x := x)).exists_cthickening_subset_open huniform.isOpen_domain
      (singleton_subset_iff.mpr hx)
  let V : Set ℂ := thickening ε ({x} : Set ℂ)
  have hV : IsOpen V := isOpen_thickening
  have hxV : x ∈ V := (self_subset_thickening hε ({x} : Set ℂ)) (by simp)
  have hclosure : closure V = cthickening ε ({x} : Set ℂ) := by
    simpa [V] using closure_thickening hε ({x} : Set ℂ)
  have hVcompact : IsCompact (closure V) := by
    rw [hclosure]
    exact (isCompact_singleton (x := x)).cthickening
  have hVD : closure V ⊆ D := by
    rw [hclosure]
    exact hεD
  -- On the compact closure, a tail is analytic and uniformly summable.
  rcases huniform.on_compact hVcompact hVD with ⟨N, hanalytic, hS⟩
  have htail_diff :
      DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℕ, f (n + N) z) V :=
    tail_tsum_differentiable_on_buffer hV hanalytic hS
  have htail_analytic :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' n : ℕ, f (n + N) z) V :=
    (Complex.analyticOnNhd_iff_differentiableOn hV).2 htail_diff
  have htail_meromorphic :
      MeromorphicAt (fun z : ℂ ↦ ∑' n : ℕ, f (n + N) z) x :=
    (htail_analytic x hxV).meromorphicAt
  have hprefix_meromorphic :
      MeromorphicAt (fun z : ℂ ↦ ∑ n ∈ Finset.range N, f n z) x :=
    (MeromorphicOn.fun_sum (U := D) (s := Finset.range N)
      (f := fun n z ↦ f n z) fun n ↦ huniform.meromorphic_terms n) x hx
  have hsplit :
      (fun z : ℂ ↦ ∑' n : ℕ, f n z) =ᶠ[𝓝[≠] x]
        (fun z ↦ ∑ n ∈ Finset.range N, f n z + ∑' n : ℕ, f (n + N) z) := by
    -- Split the full series into a finite meromorphic prefix and a holomorphic tail on `V`.
    refine Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV)) ?_
    intro z hz
    have hzsum : Summable (fun n : ℕ ↦ f (n + N) z) := hS.summable (subset_closure hz)
    have hfullsum : Summable (fun n : ℕ ↦ f n z) := hzsum.comp_nat_add
    simpa using (hfullsum.sum_add_tsum_nat_add N).symm
  exact (hprefix_meromorphic.add htail_meromorphic).congr hsplit.symm

/-- Theorem V.2-extra-2 (2): under the same compact-uniform convergence hypothesis, the series of
derivatives converges uniformly on each compact subset `K ⊆ D` after discarding finitely many
initial terms carrying the possible poles on `K`; equivalently, the tail derivative series sums to
the derivative of the corresponding tail sum on `K`. -/
theorem hasSumUniformlyOn_deriv_tail_of_meromorphic_series_uniformly_convergent_on_compacts
    (huniform : MeromorphicSeriesUniformlyConvergentOnCompacta f D)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ,
      HasSumUniformlyOn
        (fun n z ↦ deriv (f (n + N)) z)
        (deriv (fun z : ℂ ↦ ∑' n : ℕ, f (n + N) z))
        K := by
  -- Choose a relatively compact open buffer around `K`.
  obtain ⟨ε, hε, hεD⟩ := hK.exists_cthickening_subset_open huniform.isOpen_domain hKD
  let V : Set ℂ := thickening ε K
  have hV : IsOpen V := isOpen_thickening
  have hKV : K ⊆ V := self_subset_thickening hε K
  have hclosure : closure V = cthickening ε K := by
    simpa [V] using closure_thickening hε K
  have hVcompact : IsCompact (closure V) := by
    rw [hclosure]
    exact hK.cthickening
  have hVD : closure V ⊆ D := by
    rw [hclosure]
    exact hεD
  -- On this compact closure, the given convergence hypothesis provides a holomorphic tail.
  rcases huniform.on_compact hVcompact hVD with ⟨N, hanalytic, hS⟩
  refine ⟨N, ?_⟩
  exact hasSumUniformlyOn_deriv_tail_on_buffer hKV hK hV hanalytic hS

end Uniform

section Normal

variable {D K : Set ℂ} {f : ℕ → ℂ → ℂ}

/-- Theorem V.2-extra-2 (3): if a series of meromorphic functions on an open set `D` is normally
convergent on compact subsets of `D` in the source tail-holomorphic sense, then its sum is
meromorphic on `D`. -/
theorem meromorphicOn_tsum_of_meromorphic_series_normally_convergent_on_compacts
    (hnormal : MeromorphicSeriesNormallyConvergentOnCompacta f D) :
    MeromorphicOn (fun z : ℂ ↦ ∑' n : ℕ, f n z) D := by
  -- Reduce normal convergence to the compact-uniform case already proved above.
  exact
    meromorphicOn_tsum_of_meromorphic_series_uniformly_convergent_on_compacts
      hnormal.uniformlyConvergentOnCompacta

/-- Theorem V.2-extra-2 (4): under compact-normal convergence of a meromorphic series on `D`, the
series of derivatives is normally convergent on every compact subset of `D`. -/
theorem deriv_series_normally_convergent_on_compacts_of_meromorphic_series_normally_convergent
    (hnormal : MeromorphicSeriesNormallyConvergentOnCompacta f D) :
    MeromorphicSeriesNormallyConvergentOnCompacta (fun n z ↦ deriv (f n) z) D := by
  refine ⟨hnormal.isOpen_domain, ?_, ?_⟩
  · -- Each derivative term is meromorphic because derivatives preserve meromorphy.
    intro n
    exact (hnormal.meromorphic_terms n).deriv
  · intro K hK hKD
    -- Work on a fixed closed thickening of `K` contained in `D`.
    obtain ⟨ε, hε, hεD⟩ := hK.exists_cthickening_subset_open hnormal.isOpen_domain hKD
    have hKthick : IsCompact (cthickening ε K) := hK.cthickening
    rcases hnormal.on_compact hKthick hεD with ⟨N, hanalytic, u, hu, hubound⟩
    rcases
        deriv_tail_majorized_on_compact_of_normal_tail_bound
          (K := K) (ε := ε) hε (g := fun n z ↦ f (n + N) z) (u := u)
          hanalytic hubound with
      ⟨c, hderiv_bound⟩
    refine ⟨N, ?_, ?_⟩
    · -- The derivative tail is analytic on `K` because the original tail is analytic nearby.
      intro n
      exact ((hanalytic n).deriv).mono (self_subset_cthickening K)
    · -- Scale the original summable majorant by the Cauchy constant.
      refine ⟨fun n ↦ u n * c, ?_, ?_⟩
      · simpa [NNReal.coe_mul, mul_assoc, mul_left_comm, mul_comm] using hu.mul_right (c : ℝ)
      · intro n z hz
        simpa [NNReal.coe_mul] using hderiv_bound n z hz

/-- Theorem V.2-extra-2 (5): under the same compact-normal convergence hypothesis, the series of
derivatives converges uniformly on each compact subset `K ⊆ D` after removing finitely many
initial pole terms on `K`; equivalently, the derivative tail series sums to the derivative of the
corresponding tail sum on `K`. -/
theorem hasSumUniformlyOn_deriv_tail_of_meromorphic_series_normally_convergent_on_compacts
    (hnormal : MeromorphicSeriesNormallyConvergentOnCompacta f D)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ,
      HasSumUniformlyOn
        (fun n z ↦ deriv (f (n + N)) z)
        (deriv (fun z : ℂ ↦ ∑' n : ℕ, f (n + N) z))
        K := by
  -- Reduce normal convergence to the compact-uniform derivative theorem.
  exact
    hasSumUniformlyOn_deriv_tail_of_meromorphic_series_uniformly_convergent_on_compacts
      hnormal.uniformlyConvergentOnCompacta hK hKD

end Normal
