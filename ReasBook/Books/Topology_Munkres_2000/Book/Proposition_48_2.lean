module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable

public section

open Filter Set

/-- Helper for Proposition 48.2: `cauchyControlSet F r N` consists of the points
where the tail of `F` after `N` has pairwise distances at most `r`. -/
private def cauchyControlSet
    (F : ℕ → unitInterval → ℝ) (r : ℝ) (N : ℕ) : Set unitInterval :=
  {x | ∀ m ≥ N, ∀ n ≥ N, dist (F m x) (F n x) ≤ r}

/-- Helper for Proposition 48.2: tail-Cauchy control sets of continuous
functions are closed. -/
private lemma isClosed_cauchyControlSet
    (F : ℕ → unitInterval → ℝ) (hF : ∀ n, Continuous (F n))
    (r : ℝ) (N : ℕ) : IsClosed (cauchyControlSet F r N) := by
  -- Rewrite the four quantified conditions as intersections of closed inequalities.
  simp only [cauchyControlSet, setOf_forall]
  exact isClosed_iInter fun m ↦
    isClosed_iInter fun _ ↦
      isClosed_iInter fun n ↦
        isClosed_iInter fun _ ↦ isClosed_le ((hF m).dist (hF n)) continuous_const

/-- Helper for Proposition 48.2: pointwise convergence makes the positive-scale
tail-Cauchy control sets cover the whole interval. -/
private lemma iUnion_cauchyControlSet_eq_univ
    (F : ℕ → unitInterval → ℝ) (f : unitInterval → ℝ)
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    {r : ℝ} (hr : 0 < r) : ⋃ N, cauchyControlSet F r N = Set.univ := by
  -- At each point, convergence supplies a tail that is Cauchy at scale `r`.
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    have hxCauchy : CauchySeq (fun n ↦ F n x) := (hf x).cauchySeq
    rw [Metric.cauchySeq_iff] at hxCauchy
    obtain ⟨N, hN⟩ := hxCauchy r hr
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    intro m hm n hn
    exact (hN m hm n hn).le

/-- Helper for Proposition 48.2: at every positive scale, the union of the
interiors of the tail-Cauchy control sets is dense. -/
private lemma dense_iUnion_interior_cauchyControlSet
    (F : ℕ → unitInterval → ℝ) (f : unitInterval → ℝ)
    (hF : ∀ n, Continuous (F n))
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    {r : ℝ} (hr : 0 < r) : Dense (⋃ N, interior (cauchyControlSet F r N)) := by
  -- Apply the Baire closed-cover theorem to the control sets at this scale.
  exact dense_iUnion_interior_of_closed
    (fun N ↦ isClosed_cauchyControlSet F hF r N)
    (iUnion_cauchyControlSet_eq_univ F f hf hr)

/-- Helper for Proposition 48.2: a point lying locally in tail-Cauchy control
sets at every reciprocal scale is a continuity point of the limit. -/
private lemma continuousAt_of_mem_iInter_cauchyControlInteriors
    (F : ℕ → unitInterval → ℝ) (f : unitInterval → ℝ)
    (hF : ∀ n, Continuous (F n))
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    {x : unitInterval}
    (hx : x ∈ ⋂ k : ℕ, ⋃ N, interior (cauchyControlSet F (1 / (k + 1 : ℝ)) N)) :
    ContinuousAt f x := by
  -- Work at a reciprocal scale smaller than one third of the requested error.
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hεThird : 0 < ε / 3 := by positivity
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hεThird
  have hxScale : x ∈ ⋃ N, interior (cauchyControlSet F (1 / (k + 1 : ℝ)) N) :=
    Set.mem_iInter.1 hx k
  obtain ⟨N, hxN⟩ := Set.mem_iUnion.1 hxScale
  have hControlNhds : cauchyControlSet F (1 / (k + 1 : ℝ)) N ∈ nhds x :=
    mem_interior_iff_mem_nhds.1 hxN
  obtain ⟨δA, hδA, hballA⟩ := Metric.mem_nhds_iff.1 hControlNhds
  obtain ⟨δF, hδF, hFδ⟩ :=
    Metric.continuousAt_iff.1 (hF N).continuousAt (ε / 3) hεThird
  refine ⟨min δA δF, lt_min hδA hδF, ?_⟩
  intro y hy
  have hyControl : y ∈ cauchyControlSet F (1 / (k + 1 : ℝ)) N :=
    hballA (Metric.mem_ball.2 (hy.trans_le (min_le_left δA δF)))
  have hxControl : x ∈ cauchyControlSet F (1 / (k + 1 : ℝ)) N :=
    interior_subset hxN
  have hyTail : dist (f y) (F N y) ≤ 1 / (k + 1 : ℝ) := by
    -- Pass the control inequality to the pointwise limit at `y`.
    apply le_of_tendsto ((hf y).dist tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop N] with m hm
    exact hyControl m hm N le_rfl
  have hxTail : dist (F N x) (f x) ≤ 1 / (k + 1 : ℝ) := by
    -- Pass the other control inequality to the pointwise limit at `x`.
    apply le_of_tendsto (tendsto_const_nhds.dist (hf x))
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hxControl N le_rfl n hn
  have hMiddle : dist (F N y) (F N x) < ε / 3 :=
    hFδ (hy.trans_le (min_le_right δA δF))
  have hTriangle₁ := dist_triangle (f y) (F N y) (f x)
  have hTriangle₂ := dist_triangle (F N y) (F N x) (f x)
  -- The two tail bounds and continuity of `F N` give the three-term estimate.
  linarith

/-- Proposition 48.2. A pointwise limit of continuous real-valued functions on
`unitInterval` has a dense set of continuity points. -/
theorem dense_continuousAt_unitInterval_of_tendsto
    (F : ℕ → unitInterval → ℝ) (f : unitInterval → ℝ)
    (hF : ∀ n, Continuous (F n))
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    Dense {x | ContinuousAt f x} := by
  -- Intersect the dense open control regions over all reciprocal scales.
  have hDense :
      Dense (⋂ k : ℕ, ⋃ N, interior (cauchyControlSet F (1 / (k + 1 : ℝ)) N)) := by
    apply dense_iInter_of_isOpen_nat
    · intro k
      exact isOpen_iUnion fun N ↦ isOpen_interior
    · intro k
      have hk : 0 < 1 / (k + 1 : ℝ) := by positivity
      exact dense_iUnion_interior_cauchyControlSet F f hF hf hk
  -- Every point of that dense intersection is a continuity point of `f`.
  apply hDense.mono
  intro x hx
  exact continuousAt_of_mem_iInter_cauchyControlInteriors F f hF hf hx

end
