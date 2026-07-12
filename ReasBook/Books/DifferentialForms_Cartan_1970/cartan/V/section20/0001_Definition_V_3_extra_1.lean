import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology UniformConvergence

-- Domain sampling: this file is source-facing in the function-series / uniform-product domain.
-- The canonical owner abstractions are `HasSumUniformlyOn` / `SummableUniformlyOn` for series and
-- `HasProdUniformlyOn` / `MultipliableUniformlyOn` for products. The local “normal” notions below
-- remain the source-facing majorant conditions; the uniform-convergence owners are derived API.

/-- A series of complex-valued functions converges normally on `K` if its terms admit a summable
nonnegative real majorant on `K`. -/
def NormallySummableOn (u : ℕ → ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∃ a : ℕ → NNReal, Summable (fun n ↦ (a n : ℝ)) ∧ ∀ n z, z ∈ K → ‖u n z‖ ≤ a n

/-- Normal convergence on `K` gives the canonical uniform-summation owner for the series on
`K`. -/
theorem NormallySummableOn.hasSumUniformlyOn {u : ℕ → ℂ → ℂ} {K : Set ℂ}
    (h : NormallySummableOn u K) :
    HasSumUniformlyOn u (fun z ↦ ∑' n, u n z) K := by
  rcases h with ⟨a, ha, hbound⟩
  exact HasSumUniformlyOn.of_norm_le_summable ha fun n z hz ↦ hbound n z hz

/-- Normal convergence on `K` implies uniform summability there. -/
theorem NormallySummableOn.summableUniformlyOn {u : ℕ → ℂ → ℂ} {K : Set ℂ}
    (h : NormallySummableOn u K) :
    SummableUniformlyOn u K :=
  h.hasSumUniformlyOn.summableUniformlyOn

/-- A normally summable series on `K` has terms tending uniformly to `0` on `K`. -/
theorem NormallySummableOn.tendstoUniformlyOn_zero {u : ℕ → ℂ → ℂ} {K : Set ℂ}
    (h : NormallySummableOn u K) :
    TendstoUniformlyOn u (fun _ ↦ (0 : ℂ)) atTop K := by
  rcases h with ⟨a, ha, hbound⟩
  have haNN : Summable a := NNReal.summable_coe.1 ha
  have ha0 : Tendsto a atTop (nhds 0) := NNReal.tendsto_atTop_zero_of_summable haNN
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let ε₀ : NNReal := ⟨ε, hε.le⟩
  have hε₀ : 0 < ε₀ := hε
  filter_upwards [ha0 (Iio_mem_nhds hε₀)] with n hn z hz
  calc
    dist (0 : ℂ) (u n z) = ‖u n z‖ := by simp
    _ ≤ a n := hbound n z hz
    _ < ε := hn

/-- A normally summable series on `K` has uniformly bounded real parts of its pointwise sums on
`K`. -/
theorem NormallySummableOn.bddAbove_re_tsum {u : ℕ → ℂ → ℂ} {K : Set ℂ}
    (h : NormallySummableOn u K) :
    BddAbove ((fun z ↦ (∑' n, u n z).re) '' K) := by
  rcases h with ⟨a, ha, hbound⟩
  refine ⟨∑' n, (a n : ℝ), ?_⟩
  rintro y ⟨z, hzK, rfl⟩
  have hu_norm : Summable (fun n ↦ ‖u n z‖) :=
    ha.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ hbound n z hzK
  calc
    (∑' n, u n z).re ≤ ‖∑' n, u n z‖ := Complex.re_le_norm _
    _ ≤ ∑' n, ‖u n z‖ := norm_tsum_le_tsum_norm hu_norm
    _ ≤ ∑' n, (a n : ℝ) := hu_norm.tsum_le_tsum (fun n ↦ hbound n z hzK) ha

/-- Definition V.3-extra-1: an infinite product `∏ n, f n z` of continuous complex-valued
functions on an open set `D` converges normally on `K ⊆ D` when, for some tail where the principal
logarithm is defined termwise, the logarithmic series is normally convergent on `K`. This tail
condition implies that `f n` tends uniformly to `1` on `K`. -/
class NormallyMultipliableOn (f : ℕ → ℂ → ℂ) (D K : Set ℂ) : Prop where
  isOpen_domain : IsOpen D
  subset_domain : K ⊆ D
  continuousOn : ∀ n, ContinuousOn (f n) D
  exists_slit_log_tail :
    ∃ N : ℕ, (∀ n, Set.MapsTo (f (n + N)) K Complex.slitPlane) ∧
      NormallySummableOn (fun n z ↦ Complex.log (f (n + N) z)) K

/-- In Definition V.3-extra-1, the normally convergent logarithmic tail is in particular
uniformly summable on `K`, with the principal logarithm defined termwise on that tail. -/
theorem NormallyMultipliableOn.exists_logTail_summableUniformlyOn
    {f : ℕ → ℂ → ℂ} {D K : Set ℂ} (h : NormallyMultipliableOn f D K) :
    ∃ N : ℕ, (∀ n, Set.MapsTo (f (n + N)) K Complex.slitPlane) ∧
      SummableUniformlyOn (fun n z ↦ Complex.log (f (n + N) z)) K := by
  rcases h.exists_slit_log_tail with ⟨N, hslit, hN⟩
  exact ⟨N, hslit, hN.summableUniformlyOn⟩

/-- In Definition V.3-extra-1, the logarithmic tail forces the factors to tend uniformly to `1`
on `K`. -/
theorem NormallyMultipliableOn.tendstoUniformlyOn_one {f : ℕ → ℂ → ℂ} {D K : Set ℂ}
    (h : NormallyMultipliableOn f D K) :
    TendstoUniformlyOn f (fun _ ↦ (1 : ℂ)) atTop K := by
  rcases h.exists_slit_log_tail with ⟨N, hslit, hN⟩
  have htail_log :
      TendstoUniformlyOn (fun n z ↦ Complex.log (f (n + N) z)) (fun _ ↦ (0 : ℂ)) atTop K :=
    hN.tendstoUniformlyOn_zero
  have htail_exp :
      TendstoUniformlyOn
        (fun n z ↦ Complex.exp (Complex.log (f (n + N) z)))
        (fun _ ↦ (1 : ℂ)) atTop K := by
    refine (htail_log.comp_cexp ?_).congr_right ?_
    · refine ⟨0, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      simp
    · intro z hz
      simp
  have htail :
      TendstoUniformlyOn (fun n z ↦ f (n + N) z) (fun _ ↦ (1 : ℂ)) atTop K := by
    refine htail_exp.congr ?_
    filter_upwards with n z hz
    simpa using Complex.exp_log (Complex.slitPlane_ne_zero <| hslit n hz)
  rw [Metric.tendstoUniformlyOn_iff] at htail ⊢
  intro ε hε
  have htailε : ∀ᶠ n in atTop, ∀ x ∈ K, dist 1 (f (n + N) x) < ε := htail ε hε
  rw [Filter.eventually_atTop] at htailε ⊢
  rcases htailε with ⟨M, hM⟩
  refine ⟨M + N, ?_⟩
  intro n hn z hz
  have hNn : N ≤ n := by omega
  have hMn : n - N ≥ M := by omega
  simpa [Nat.sub_add_cancel hNn] using hM (n - N) hMn z hz

/-- Helper for Definition V.3-extra-1: a slit-plane logarithmic tail exponentiates to a uniformly
convergent tail product on `K`. -/
lemma NormallyMultipliableOn.tail_hasProdUniformlyOn_of_slit_log_tail
    {f : ℕ → ℂ → ℂ} {K : Set ℂ} {N : ℕ}
    (hslit : ∀ n, Set.MapsTo (f (n + N)) K Complex.slitPlane)
    (hlog : NormallySummableOn (fun n z ↦ Complex.log (f (n + N) z)) K) :
    HasProdUniformlyOn (fun n z ↦ f (n + N) z) (fun z ↦ ∏' n, f (n + N) z) K := by
  -- The normally summable logarithmic tail is exactly the input needed for the canonical
  -- exponential bridge from sums of logs to products.
  refine hasProdUniformlyOn_of_clog hlog.summableUniformlyOn ?_ hlog.bddAbove_re_tsum
  intro z hz n
  exact Complex.slitPlane_ne_zero (hslit n hz)

/-- Helper for Definition V.3-extra-1: on a compact set, the tail product coming from the
logarithmic tail is continuous. -/
lemma tail_tprod_continuousOn_of_slit_log_tail
    {f : ℕ → ℂ → ℂ} {D K : Set ℂ} {N : ℕ}
    (hcont : ∀ n, ContinuousOn (f n) D) (hKD : K ⊆ D)
    (hslit : ∀ n, Set.MapsTo (f (n + N)) K Complex.slitPlane)
    (hlog : NormallySummableOn (fun n z ↦ Complex.log (f (n + N) z)) K) :
    ContinuousOn (fun z ↦ ∏' n, f (n + N) z) K := by
  have htail :
      TendstoUniformlyOn (fun m z ↦ ∏ i ∈ Finset.range m, f (i + N) z)
        (fun z ↦ ∏' n, f (n + N) z) atTop K :=
    HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
      (NormallyMultipliableOn.tail_hasProdUniformlyOn_of_slit_log_tail hslit hlog)
  have hpartial :
      ∃ᶠ m in atTop, ContinuousOn (fun z ↦ ∏ i ∈ Finset.range m, f (i + N) z) K := by
    -- Every tail partial product is continuous because it is a finite product of continuous
    -- factors restricted from `D` to `K`.
    refine Filter.Frequently.of_forall ?_
    intro m
    exact continuousOn_finsetProd (Finset.range m) fun i _ ↦ (hcont (i + N)).mono hKD
  -- A compact-set uniform limit of continuous functions is continuous.
  exact htail.continuousOn hpartial

/-- Helper for Definition V.3-extra-1: on a fixed set `K`, multiplying by a bounded scalar-valued
prefix preserves uniform convergence. -/
lemma tendstoUniformlyOn_mul_left_of_boundedOn
    {ι : Type*} [Preorder ι] {a : ℂ → ℂ} {F : ι → ℂ → ℂ} {G : ℂ → ℂ} {K : Set ℂ}
    (hFG : TendstoUniformlyOn F G atTop K)
    (hbound : ∃ C : ℝ, ∀ z ∈ K, ‖a z‖ ≤ C) :
    TendstoUniformlyOn (fun n z ↦ a z * F n z) (fun z ↦ a z * G z) atTop K := by
  rcases hbound with ⟨C, hC⟩
  let R : ℝ := max C 0 + 1
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRbound : ∀ z ∈ K, ‖a z‖ ≤ R := by
    intro z hz
    calc
      ‖a z‖ ≤ C := hC z hz
      _ ≤ max C 0 := le_max_left _ _
      _ ≤ R := by
        dsimp [R]
        linarith
  -- We work directly with the metric characterization of uniform convergence.
  rw [Metric.tendstoUniformlyOn_iff] at hFG ⊢
  intro ε hε
  have hδ : 0 < ε / R := by
    exact div_pos hε hRpos
  filter_upwards [hFG (ε / R) hδ] with n hn z hz
  have ha : ‖a z‖ ≤ R := hRbound z hz
  have hdist : ‖G z - F n z‖ < ε / R := by
    simpa [dist_eq_norm] using hn z hz
  have hRne : R ≠ 0 := ne_of_gt hRpos
  calc
    dist (a z * G z) (a z * F n z) = ‖a z * (G z - F n z)‖ := by
      rw [dist_eq_norm, mul_sub_left_distrib]
    _ ≤ ‖a z‖ * ‖G z - F n z‖ := norm_mul_le _ _
    _ ≤ R * ‖G z - F n z‖ := by
      exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ < R * (ε / R) := by
      exact mul_lt_mul_of_pos_left hdist hRpos
    _ = ε := by
      field_simp [hRne]

/-- Helper for Definition V.3-extra-1: shifting a natural index by a fixed prefix length. -/
def nat_add_embedding (N : ℕ) : ℕ ↪ ℕ where
  toFun n := n + N
  inj' := fun _ _ h ↦ Nat.add_right_cancel h

/-- Helper for Definition V.3-extra-1: addition by a fixed natural number is injective on the
preimage of any finite set. -/
lemma nat_add_injOn_preimage (N : ℕ) (s : Finset ℕ) :
    Set.InjOn (fun n : ℕ ↦ n + N) ((fun n : ℕ ↦ n + N) ⁻¹' ↑s) := by
  intro a _ b _ hab
  exact Nat.add_right_cancel hab

/-- Helper for Definition V.3-extra-1: the tail indices of `s` after removing the first `N`
positions. -/
noncomputable def tail_indices (N : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.preimage (fun n : ℕ ↦ n + N) (nat_add_injOn_preimage N s)

/-- Helper for Definition V.3-extra-1: after removing the initial range, the remaining indices are
exactly the shifted image of the tail indices. -/
lemma tail_indices_map_eq_sdiff_range (N : ℕ) (s : Finset ℕ) :
    (tail_indices N s).map (nat_add_embedding N) = s \ Finset.range N := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨n, hn, rfl⟩
    refine Finset.mem_sdiff.mpr ?_
    constructor
    · simpa [tail_indices] using hn
    · have hnot : ¬ n + N < N := by
        omega
      simp [Finset.mem_range, nat_add_embedding]
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_s, hx_range⟩
    have hxN : N ≤ x := by
      have hx_range' : ¬ x < N := by
        simpa [Finset.mem_range] using hx_range
      exact Nat.not_lt.mp hx_range'
    refine Finset.mem_map.mpr ?_
    refine ⟨x - N, ?_, ?_⟩
    · simpa [tail_indices, Nat.sub_add_cancel hxN] using hx_s
    · simp [nat_add_embedding, Nat.sub_add_cancel hxN]

/-- Helper for Definition V.3-extra-1: removing the initial range from a large finite set remains
cofinal in `Finset ℕ`. -/
lemma tail_indices_tendsto_atTop (N : ℕ) :
    Tendsto (tail_indices N) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro s
  rw [Filter.eventually_atTop]
  refine ⟨Finset.range N ∪ s.map (nat_add_embedding N), ?_⟩
  intro t ht
  have ht' : Finset.range N ∪ s.map (nat_add_embedding N) ⊆ t := by
    exact ht
  have hs' : s ⊆ tail_indices N t := by
    intro n hn
    have hmem : n + N ∈ t := by
      exact ht' <| Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_map.mpr ⟨n, hn, by simp [nat_add_embedding]⟩
    simpa [tail_indices] using hmem
  simpa [Finset.le_eq_subset] using hs'

/-- Helper for Definition V.3-extra-1: once a finite set of indices contains the initial range,
its finite product splits into the fixed prefix and the shifted tail subproduct. -/
lemma finset_prod_eq_prefix_mul_tail_indices
    {f : ℕ → ℂ → ℂ} {N : ℕ} {s : Finset ℕ} (hs : Finset.range N ⊆ s) (z : ℂ) :
    ∏ i ∈ s, f i z =
      (∏ i ∈ Finset.range N, f i z) * ∏ i ∈ tail_indices N s, f (i + N) z := by
  calc
    ∏ i ∈ s, f i z = ∏ i ∈ Finset.range N ∪ (s \ Finset.range N), f i z := by
      rw [Finset.union_sdiff_of_subset hs]
    _ = (∏ i ∈ Finset.range N, f i z) * ∏ i ∈ s \ Finset.range N, f i z := by
      rw [Finset.prod_union Finset.disjoint_sdiff]
    _ = (∏ i ∈ Finset.range N, f i z) *
          ∏ i ∈ (tail_indices N s).map (nat_add_embedding N), f i z := by
      rw [tail_indices_map_eq_sdiff_range]
    _ = (∏ i ∈ Finset.range N, f i z) * ∏ i ∈ tail_indices N s, f (i + N) z := by
      rw [Finset.prod_map]
      simp [nat_add_embedding]

/-- Helper for Definition V.3-extra-1: once the partial product index passes the prefix length,
the full partial products split into the fixed prefix times the shifted tail products. -/
lemma partial_prod_eq_prefix_mul_tail_eventually
    {f : ℕ → ℂ → ℂ} {K : Set ℂ} (N : ℕ) :
    ∀ᶠ m in atTop,
      Set.EqOn
        (fun z ↦ ∏ i ∈ Finset.range m, f i z)
        (fun z ↦ (∏ i ∈ Finset.range N, f i z) * ∏ i ∈ Finset.range (m - N), f (i + N) z)
        K := by
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro m hm z hz
  have hNm : N ≤ m := hm
  -- Rewrite the full initial product as a prefix of length `N` followed by a shifted tail.
  calc
    ∏ i ∈ Finset.range m, f i z = ∏ i ∈ Finset.range (N + (m - N)), f i z := by
      have hsplit : N + (m - N) = m := by
        omega
      simp [hsplit]
    _ = (∏ i ∈ Finset.range N, f i z) * ∏ i ∈ Finset.range (m - N), f (i + N) z := by
      simpa [Nat.add_comm] using Finset.prod_range_add (fun i ↦ f i z) N (m - N)

/-- Helper for Definition V.3-extra-1: pointwise tail products extend across a finite prefix. -/
lemma hasProd_prefix_mul_tail_pointwise
    {f : ℕ → ℂ → ℂ} {N : ℕ} {z : ℂ}
    (htail : HasProd (fun n ↦ f (n + N) z) (∏' n, f (n + N) z)) :
    HasProd (fun n ↦ f n z) ((∏ i ∈ Finset.range N, f i z) * ∏' n, f (n + N) z) := by
  -- Finite-prefix insertion for the pointwise product is exactly `HasProd.prod_range_mul`.
  simpa using htail.prod_range_mul (k := N)

/-- Helper for Definition V.3-extra-1: the pointwise infinite product equals the finite prefix
times the shifted tail product on `K`. -/
lemma tprod_eqOn_prefix_mul_tail
    {f : ℕ → ℂ → ℂ} {K : Set ℂ} (N : ℕ)
    (htail : HasProdUniformlyOn (fun n z ↦ f (n + N) z) (fun z ↦ ∏' n, f (n + N) z) K) :
    Set.EqOn
      (fun z ↦ ∏' n, f n z)
      (fun z ↦ (∏ i ∈ Finset.range N, f i z) * ∏' n, f (n + N) z)
      K := by
  intro z hz
  have htailPointwise :
      HasProd (fun n ↦ f (n + N) z) (∏' n, f (n + N) z) :=
    htail.hasProd hz
  have hfull :
      HasProd (fun n ↦ f n z)
        ((∏ i ∈ Finset.range N, f i z) * ∏' n, f (n + N) z) :=
    hasProd_prefix_mul_tail_pointwise (f := f) (N := N) (z := z) htailPointwise
  -- Evaluate the pointwise full product using the standard finite-prefix / infinite-tail split.
  simpa using hfull.tprod_eq

/-- Definition V.3-extra-1 implies the canonical uniform product owner on a compact `K`. -/
theorem NormallyMultipliableOn.hasProdUniformlyOn {f : ℕ → ℂ → ℂ} {D K : Set ℂ}
    (h : NormallyMultipliableOn f D K) (hK : IsCompact K) :
    HasProdUniformlyOn f (fun z ↦ ∏' n, f n z) K := by
  rcases h.exists_slit_log_tail with ⟨N, hslit, hlog⟩
  have htailProd :
      HasProdUniformlyOn (fun n z ↦ f (n + N) z) (fun z ↦ ∏' n, f (n + N) z) K :=
    NormallyMultipliableOn.tail_hasProdUniformlyOn_of_slit_log_tail hslit hlog
  have htail :
      TendstoUniformlyOn
        (fun s z ↦ ∏ i ∈ tail_indices N s, f (i + N) z)
        (fun z ↦ ∏' n, f (n + N) z) atTop K := by
    have htail' :
        TendstoUniformlyOn
          (fun s z ↦ ∏ i ∈ s, f (i + N) z)
          (fun z ↦ ∏' n, f (n + N) z) atTop K :=
      htailProd.tendstoUniformlyOn
    rw [tendstoUniformlyOn_iff_tendsto] at htail' ⊢
    have hreindex :
        Tendsto
          (fun p : Finset ℕ × ℂ ↦ (tail_indices N p.1, p.2))
          (atTop ×ˢ 𝓟 K) (atTop ×ˢ 𝓟 K) :=
      ((tail_indices_tendsto_atTop N).comp tendsto_fst).prodMk
        (show Tendsto Prod.snd (atTop ×ˢ 𝓟 K) (𝓟 K) from tendsto_snd)
    exact htail'.comp hreindex
  have hprefixBound :
      ∃ C : ℝ, ∀ z ∈ K, ‖∏ i ∈ Finset.range N, f i z‖ ≤ C := by
    have hprefixCont : ContinuousOn (fun z ↦ ∏ i ∈ Finset.range N, f i z) K := by
      exact continuousOn_finsetProd (Finset.range N) fun i _ ↦
        (h.continuousOn i).mono h.subset_domain
    obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ (fun z ↦ ∏ i ∈ Finset.range N, f i z) '' K, ‖x‖ ≤ C :=
      (hK.image_of_continuousOn hprefixCont).isBounded.exists_norm_le
    refine ⟨C, ?_⟩
    intro z hz
    exact hC _ (Set.mem_image_of_mem _ hz)
  have hmul :
      TendstoUniformlyOn
        (fun s z ↦ (∏ i ∈ Finset.range N, f i z) * ∏ i ∈ tail_indices N s, f (i + N) z)
        (fun z ↦ (∏ i ∈ Finset.range N, f i z) * ∏' n, f (n + N) z) atTop K := by
    exact tendstoUniformlyOn_mul_left_of_boundedOn htail hprefixBound
  have hsplit :
      TendstoUniformlyOn
        (fun s z ↦ ∏ i ∈ s, f i z)
        (fun z ↦ (∏ i ∈ Finset.range N, f i z) * ∏' n, f (n + N) z) atTop K :=
    hmul.congr <| by
      rw [Filter.eventually_atTop]
      refine ⟨Finset.range N, ?_⟩
      intro s hs z hz
      exact (finset_prod_eq_prefix_mul_tail_indices (f := f) hs z).symm
  have htprod :
      Set.EqOn
        (fun z ↦ (∏ i ∈ Finset.range N, f i z) * ∏' n, f (n + N) z)
        (fun z ↦ ∏' n, f n z) K :=
    (tprod_eqOn_prefix_mul_tail (f := f) (K := K) N htailProd).symm
  exact hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr <| hsplit.congr_right htprod

/-- Definition V.3-extra-1 implies uniform multipliability on a compact `K`. -/
theorem NormallyMultipliableOn.multipliableUniformlyOn {f : ℕ → ℂ → ℂ} {D K : Set ℂ}
    (h : NormallyMultipliableOn f D K) (hK : IsCompact K) :
    MultipliableUniformlyOn f K :=
  (h.hasProdUniformlyOn hK).multipliableUniformlyOn

/-- For factors written as `f n z = 1 + u n z`, Definition V.3-extra-1 specializes to continuity
of the perturbations `u n` and normal convergence of a logarithmic tail on `K` on which the
principal logarithm is defined termwise; the uniform convergence `u n ⟶ 0` on `K` is then derived
from `NormallyMultipliableOn.tendstoUniformlyOn_one`. -/
theorem normallyMultipliableOn_one_add_iff {u : ℕ → ℂ → ℂ} {D K : Set ℂ} :
    NormallyMultipliableOn (fun n z ↦ 1 + u n z) D K ↔
      IsOpen D ∧ K ⊆ D ∧ (∀ n, ContinuousOn (u n) D) ∧
        ∃ N : ℕ, (∀ n, Set.MapsTo (fun z ↦ 1 + u (n + N) z) K Complex.slitPlane) ∧
          NormallySummableOn (fun n z ↦ Complex.log (1 + u (n + N) z)) K := by
  constructor
  · intro h
    refine ⟨h.isOpen_domain, h.subset_domain, ?_, ?_⟩
    · intro n
      have hcont : ContinuousOn (fun z ↦ (1 + u n z) - 1) D :=
        (h.continuousOn n).sub continuousOn_const
      simpa using hcont
    · rcases h.exists_slit_log_tail with ⟨N, hslit, hN⟩
      refine ⟨N, ?_, by simpa using hN⟩
      intro n
      simpa using hslit n
  · rintro ⟨hD, hKD, hu_cont, hlog⟩
    refine ⟨hD, hKD, ?_, ?_⟩
    · intro n
      simpa using (hu_cont n).const_add (1 : ℂ)
    · rcases hlog with ⟨N, hslit, hN⟩
      exact ⟨N, (fun n ↦ by simpa using hslit n), by simpa using hN⟩

/-- For factors written as `f n z = 1 + u n z`, Definition V.3-extra-1 implies that `u n`
converges uniformly to `0` on `K`. -/
theorem NormallyMultipliableOn.tendstoUniformlyOn_zero_of_one_add
    {u : ℕ → ℂ → ℂ} {D K : Set ℂ} (h : NormallyMultipliableOn (fun n z ↦ 1 + u n z) D K) :
    TendstoUniformlyOn u (fun _ ↦ (0 : ℂ)) atTop K := by
  have hOne :
      TendstoUniformlyOn (fun _ : ℕ ↦ fun _ : ℂ ↦ (1 : ℂ)) (fun _ : ℂ ↦ (1 : ℂ)) atTop K :=
    Filter.Tendsto.tendstoUniformlyOn_const
      (show Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds (1 : ℂ)) from tendsto_const_nhds) K
  have hSub :
      TendstoUniformlyOn
        ((fun n z ↦ 1 + u n z) - fun _ : ℕ ↦ fun _ : ℂ ↦ (1 : ℂ))
        (fun _ ↦ (0 : ℂ)) atTop K := by
    exact (h.tendstoUniformlyOn_one.sub hOne).congr_right (by
      intro z hz
      simp)
  have hEq :
      ∀ᶠ n in atTop,
        Set.EqOn
          (((fun n z ↦ 1 + u n z) - fun _ : ℕ ↦ fun _ : ℂ ↦ (1 : ℂ)) n)
          (u n) K := by
    filter_upwards with n z hz
    simp
  exact hSub.congr hEq
