module

public import Topology_Munkres_2000.Book.Example_63_2.HornGeometry
public import Mathlib.Analysis.SpecificLimits.Basic

public section

open Filter

namespace AlexanderHornGeometry

/-- Helper for Example 63.2: a uniformly convergent family whose unequal arguments are
eventually separated by a positive distance has an injective limit. -/
lemma injectiveOfTendstoUniformlyOfEventuallyDistGe
    {ι X Y : Type*} [MetricSpace Y] {l : Filter ι} [l.NeBot]
    {F : ι → X → Y} {f : X → Y} (hF : TendstoUniformly F f l)
    (hseparated : ∀ ⦃x y : X⦄, x ≠ y →
      ∃ ε > 0, ∀ᶠ i in l, ε ≤ dist (F i x) (F i y)) :
    Function.Injective f := by
  -- Approximate both limit values within one third of the persistent separation.
  intro x y hxy
  by_contra hne
  obtain ⟨ε, hε, hdist⟩ := hseparated hne
  have hnear := Metric.tendstoUniformly_iff.mp hF (ε / 3) (by positivity)
  obtain ⟨i, hnearAt, hdistAt⟩ := (hnear.and hdist).exists
  -- The triangle inequality would then make the stage values less than `ε` apart.
  have hstageLt : dist (F i x) (F i y) < ε := by
    calc
      dist (F i x) (F i y) ≤
          dist (F i x) (f x) + dist (f x) (f y) + dist (f y) (F i y) :=
        dist_triangle4 _ _ _ _
      _ = dist (f x) (F i x) + dist (f y) (F i y) := by
        rw [dist_comm (F i x) (f x), hxy, dist_self, add_zero]
      _ < ε / 3 + ε / 3 := add_lt_add (hnearAt x) (hnearAt y)
      _ < ε := by linarith
  exact (not_lt_of_ge hdistAt) hstageLt

/-- Helper for Example 63.2: a uniform geometric bound on consecutive stages produces a
uniformly convergent limit. -/
lemma existsTendstoUniformlyOfGeometricStep
    {X Y : Type*} [PseudoMetricSpace Y] [CompleteSpace Y]
    (F : ℕ → X → Y) (C ρ : ℝ) (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hstep : ∀ n x, dist (F n x) (F (n + 1) x) ≤ C * ρ ^ n) :
    ∃ f : X → Y, TendstoUniformly F f atTop := by
  -- Every pointwise stage sequence is Cauchy by the same geometric estimate.
  have hpointwise (x : X) : CauchySeq (fun n ↦ F n x) :=
    cauchySeq_of_le_geometric ρ C hρlt (fun n ↦ hstep n x)
  choose f hf using fun x ↦ cauchySeq_tendsto_of_complete (hpointwise x)
  refine ⟨f, Metric.tendstoUniformly_iff.mpr ?_⟩
  -- The geometric tail estimate is independent of the source point, hence uniform.
  have htail : Tendsto (fun n : ℕ ↦ C * ρ ^ n / (1 - ρ)) atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρnonneg hρlt).const_mul C).div_const
        (1 - ρ)
  intro ε hε
  filter_upwards [htail.eventually (gt_mem_nhds hε)] with n hn x
  rw [dist_comm]
  exact (dist_le_of_le_geometric_of_tendsto ρ C hρlt
    (fun k ↦ hstep k x) (hf x) n).trans_lt hn

/-- Helper for Example 63.2: continuous stages with a uniform geometric displacement bound
have a continuous uniform limit. -/
lemma existsContinuousTendstoUniformlyOfGeometricStep
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] [CompleteSpace Y]
    (F : ℕ → X → Y) (C ρ : ℝ) (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hcontinuous : ∀ n, Continuous (F n))
    (hstep : ∀ n x, dist (F n x) (F (n + 1) x) ≤ C * ρ ^ n) :
    ∃ f : X → Y, Continuous f ∧ TendstoUniformly F f atTop := by
  -- First obtain the uniform limit from the quantitative displacement estimate.
  obtain ⟨f, hF⟩ := existsTendstoUniformlyOfGeometricStep
    F C ρ hρnonneg hρlt hstep
  refine ⟨f, ?_, hF⟩
  -- Uniform convergence transfers continuity from the continuously indexed stages.
  exact hF.continuous (Frequently.of_forall hcontinuous)

/-- Helper for Example 63.2: geometrically convergent continuous stages with persistent
point separation have a continuous injective uniform limit. -/
lemma existsContinuousInjectiveTendstoUniformlyOfGeometricStep
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [CompleteSpace Y]
    (F : ℕ → X → Y) (C ρ : ℝ) (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hcontinuous : ∀ n, Continuous (F n))
    (hstep : ∀ n x, dist (F n x) (F (n + 1) x) ≤ C * ρ ^ n)
    (hseparated : ∀ ⦃x y : X⦄, x ≠ y →
      ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ε ≤ dist (F n x) (F n y)) :
    ∃ f : X → Y,
      Continuous f ∧ Function.Injective f ∧ TendstoUniformly F f atTop := by
  -- Construct the continuous limit using only the contraction estimate.
  obtain ⟨f, hfcontinuous, hF⟩ := existsContinuousTendstoUniformlyOfGeometricStep
    F C ρ hρnonneg hρlt hcontinuous hstep
  refine ⟨f, hfcontinuous, ?_, hF⟩
  -- Persistent first-divergence separation passes injectivity to that limit.
  exact injectiveOfTendstoUniformlyOfEventuallyDistGe hF hseparated

end AlexanderHornGeometry
