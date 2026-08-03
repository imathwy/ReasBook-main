module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Cauchy

public section

open Filter Set

universe u v

/-- Helper for Theorem 48.5: `cauchyControlSet F r N` consists of the points
where the tail of `F` after `N` has pairwise distances at most `r`. -/
private def cauchyControlSet
    {X : Type u} {Y : Type v} [MetricSpace Y]
    (F : ℕ → X → Y) (r : ℝ) (N : ℕ) : Set X :=
  -- Record the source proof's closed tail-control condition as one set.
  {x | ∀ m ≥ N, ∀ n ≥ N, dist (F m x) (F n x) ≤ r}

/-- Helper for Theorem 48.5: tail-Cauchy control sets of continuous functions
are closed. -/
private lemma isClosed_cauchyControlSet
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (hF : ∀ n, Continuous (F n))
    (r : ℝ) (N : ℕ) : IsClosed (cauchyControlSet F r N) := by
  -- Express the four quantified conditions as intersections of closed inequalities.
  simp only [cauchyControlSet, setOf_forall]
  exact isClosed_iInter fun m ↦
    isClosed_iInter fun _ ↦
      isClosed_iInter fun n ↦
        isClosed_iInter fun _ ↦ isClosed_le ((hF m).dist (hF n)) continuous_const

/-- Helper for Theorem 48.5: pointwise convergence makes the positive-scale
tail-Cauchy control sets cover the whole domain. -/
private lemma iUnion_cauchyControlSet_eq_univ
    {X : Type u} {Y : Type v} [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y)
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

/-- Helper for Theorem 48.5: at every positive scale, the union of the
interiors of the tail-Cauchy control sets is dense. -/
private lemma dense_iUnion_interior_cauchyControlSet
    {X : Type u} {Y : Type v} [TopologicalSpace X] [BaireSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (hF : ∀ n, Continuous (F n))
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    {r : ℝ} (hr : 0 < r) : Dense (⋃ N, interior (cauchyControlSet F r N)) := by
  -- Apply the Baire closed-cover theorem to the control sets at this scale.
  exact dense_iUnion_interior_of_closed
    (fun N ↦ isClosed_cauchyControlSet F hF r N)
    (iUnion_cauchyControlSet_eq_univ F f hf hr)

/-- Helper for Theorem 48.5: membership in a tail-control set bounds the
distance from the pointwise limit to the selected approximant. -/
private lemma dist_limit_le_of_mem_cauchyControlSet
    {X : Type u} {Y : Type v} [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y)
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    {r : ℝ} {N : ℕ} {x : X} (hx : x ∈ cauchyControlSet F r N) :
    dist (f x) (F N x) ≤ r := by
  -- Pass the tail inequality to the limit while keeping the `N`th term fixed.
  apply le_of_tendsto ((hf x).dist tendsto_const_nhds)
  filter_upwards [eventually_ge_atTop N] with m hm
  exact hx m hm N le_rfl

/-- Helper for Theorem 48.5: a point lying locally in tail-Cauchy control
sets at every reciprocal scale is a continuity point of the limit. -/
private lemma continuousAt_of_mem_iInter_cauchyControlInteriors
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (hF : ∀ n, Continuous (F n))
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    {x : X}
    (hx : x ∈ ⋂ k : ℕ, ⋃ N, interior (cauchyControlSet F (1 / (k + 1 : ℝ)) N)) :
    ContinuousAt f x := by
  -- Choose a reciprocal control scale smaller than one third of the error.
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hεThird : 0 < ε / 3 := div_pos hε zero_lt_three
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hεThird
  have hxScale : x ∈ ⋃ N, interior (cauchyControlSet F (1 / (k + 1 : ℝ)) N) :=
    Set.mem_iInter.1 hx k
  obtain ⟨N, hxN⟩ := Set.mem_iUnion.1 hxScale
  have hControlNhds : cauchyControlSet F (1 / (k + 1 : ℝ)) N ∈ nhds x :=
    mem_interior_iff_mem_nhds.1 hxN
  have hApproxNhds : ∀ᶠ y in nhds x, dist (F N y) (F N x) < ε / 3 :=
    Metric.continuousAt_iff'.1 (hF N).continuousAt (ε / 3) hεThird
  have hxControl : x ∈ cauchyControlSet F (1 / (k + 1 : ℝ)) N :=
    interior_subset hxN
  -- On the common neighborhood, combine the two limit bounds with continuity of `F N`.
  filter_upwards [hControlNhds, hApproxNhds] with y hyControl hMiddle
  have hyTail : dist (f y) (F N y) ≤ 1 / (k + 1 : ℝ) :=
    dist_limit_le_of_mem_cauchyControlSet F f hf hyControl
  have hxTail : dist (f x) (F N x) ≤ 1 / (k + 1 : ℝ) :=
    dist_limit_le_of_mem_cauchyControlSet F f hf hxControl
  have hyTailThird : dist (f y) (F N y) < ε / 3 := hyTail.trans_lt hk
  have hxTailThird : dist (f x) (F N x) < ε / 3 := hxTail.trans_lt hk
  calc
    dist (f y) (f x) ≤
        dist (f y) (F N y) + dist (f x) (F N x) + dist (F N y) (F N x) :=
      dist_triangle4_right (f y) (f x) (F N y) (F N x)
    _ < ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add hyTailThird hxTailThird) hMiddle
    _ = ε := add_thirds ε

/-- Theorem 48.5. A pointwise limit of continuous functions from a Baire space
to a metric space has a dense set of continuity points. -/
theorem dense_continuousAt_of_tendsto
    {X : Type u} {Y : Type v} [TopologicalSpace X] [BaireSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (hF : ∀ n, Continuous (F n))
    (hf : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    Dense {x | ContinuousAt f x} := by
  -- Intersect the dense open control regions over all reciprocal scales.
  apply Dense.mono
  · intro x hx
    -- Membership at every scale gives the neighborhood estimate for continuity.
    exact continuousAt_of_mem_iInter_cauchyControlInteriors F f hF hf hx
  · apply dense_iInter_of_isOpen_nat
    · intro k
      exact isOpen_iUnion fun N ↦ isOpen_interior
    · intro k
      have hk : 0 < 1 / (k + 1 : ℝ) := one_div_pos.mpr (Nat.cast_add_one_pos k)
      exact dense_iUnion_interior_cauchyControlSet F f hF hf hk

end
