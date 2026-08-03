module

public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Bounded
public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Exercise_35_3.Pseudocompact

public section

universe u

/-- A topological space is bounded for every compatible metric if every metric inducing its
topology has a uniform pairwise distance bound. -/
def BoundedForEveryCompatibleMetric (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ metric : MetricSpace X,
    metric.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) →
      ∃ C, ∀ x y : X, metric.dist x y ≤ C

/-- Helper for Exercise 35.3: a continuous real function is dominated by a metric compatible
with the topology of its domain. -/
private lemma existsCompatibleMetricDistDominates {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {f : X → ℝ} (hf : Continuous f) :
    ∃ metric : MetricSpace X,
      metric.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) ∧
        ∀ x y, dist (f x) (f y) ≤ metric.dist x y := by
  -- Pull the product metric back along the graph embedding of `f`.
  let ambientTopology : TopologicalSpace X := inferInstance
  let baseMetric : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : MetricSpace X := baseMetric
  let productMetric : MetricSpace (X × ℝ) :=
    @Prod.metricSpaceMax ℝ X baseMetric Real.metricSpace
  let graph : X → X × ℝ := fun x ↦ (x, f x)
  let metric : MetricSpace X :=
    @Topology.IsEmbedding.comapMetricSpace X (X × ℝ) ambientTopology productMetric
      graph (isEmbedding_graph hf)
  refine ⟨metric, rfl, ?_⟩
  -- The second-coordinate distance is bounded by the product maximum distance.
  intro x y
  have hmetricEq : metric =
      MetricSpace.induced graph (isEmbedding_graph hf).injective
        productMetric := by
    dsimp only [metric, Topology.IsEmbedding.comapMetricSpace]
    exact @MetricSpace.replaceTopology_eq X
      ambientTopology
      (MetricSpace.induced graph (isEmbedding_graph hf).injective
        productMetric)
      (isEmbedding_graph hf).eq_induced
  rw [hmetricEq]
  change dist (f x) (f y) ≤ productMetric.dist (graph x) (graph y)
  have hproductDist : productMetric.dist (graph x) (graph y) =
      max (baseMetric.dist x y) (dist (f x) (f y)) := rfl
  rw [hproductDist]
  exact le_max_right (baseMetric.dist x y) (dist (f x) (f y))

/-- Helper for Exercise 35.3: distance from a point is continuous for any metric inducing the
ambient topology. -/
private lemma continuousCompatibleMetricDist {X : Type u} [TopologicalSpace X]
    (metric : MetricSpace X)
    (hmetric : metric.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X)) (x₀ : X) :
    Continuous (metric.dist x₀) := by
  -- Replace the metric's bundled topology by the ambient one, without changing its distance.
  letI : MetricSpace X := metric.replaceTopology hmetric.symm
  have hreplace : metric.replaceTopology hmetric.symm = metric :=
    MetricSpace.replaceTopology_eq metric hmetric.symm
  rw [← hreplace]
  exact continuous_const.dist continuous_id

/-- Helper for Exercise 35.3: boundedness of the range of distance from one point gives a
uniform bound on all pairwise distances. -/
private lemma pairwiseDistBoundOfBoundedDistanceRange {X : Type u} (metric : MetricSpace X)
    (x₀ : X) (hbounded : Bornology.IsBounded (Set.range (metric.dist x₀))) :
    ∃ C, ∀ x y, metric.dist x y ≤ C := by
  letI : MetricSpace X := metric
  -- Compare every value of the distance function with its zero value at the base point.
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hbounded
  have hbase : ∀ x, metric.dist x₀ x ≤ C := by
    intro x
    simpa only [metric.dist_self, Real.dist_0_eq_abs,
      abs_of_nonneg dist_nonneg] using hC x x₀
  refine ⟨C + C, ?_⟩
  -- The metric triangle inequality reduces the pairwise estimate to the two base-point bounds.
  intro x y
  calc
    metric.dist x y ≤ metric.dist x x₀ + metric.dist x₀ y :=
      metric.dist_triangle x x₀ y
    _ = metric.dist x₀ x + metric.dist x₀ y := by rw [metric.dist_comm x x₀]
    _ ≤ C + C := add_le_add (hbase x) (hbase y)

/-- Helper for Exercise 35.3: every infinite discrete space admits a continuous real function
with unbounded range. -/
private lemma existsContinuousMapUnboundedRangeOfInfiniteDiscrete (A : Type u)
    [TopologicalSpace A] [DiscreteTopology A] [Infinite A] :
    ∃ f : C(A, ℝ), ¬ Bornology.IsBounded (Set.range f) := by
  classical
  -- Read natural-number coordinates from a fixed embedding of `ℕ` into `A`.
  let e : ℕ ↪ A := Infinite.natEmbedding A
  let f : C(A, ℝ) :=
    ⟨fun a ↦ ((Function.invFun e a : ℕ) : ℝ), continuous_of_discreteTopology⟩
  refine ⟨f, ?_⟩
  intro hbounded
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hbounded
  obtain ⟨n, hn⟩ := exists_nat_gt C
  -- Along the embedded natural numbers the function takes the values `n` and `0`.
  have fe (k : ℕ) : f (e k) = (k : ℝ) := by
    simpa only [f, ContinuousMap.coe_mk] using
      congrArg (fun m : ℕ ↦ (m : ℝ)) (Function.leftInverse_invFun e.injective k)
  have hdist := hC (e n) (e 0)
  rw [fe n, fe 0] at hdist
  have hnBound : (n : ℝ) ≤ C := by
    simpa only [Nat.cast_zero, Real.dist_0_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hdist
  exact (not_lt_of_ge hnBound) hn

/- Exercise 35.3: For a metrizable space, boundedness for every compatible metric,
pseudocompactness, and limit point compactness are equivalent. -/
mutual

-- Route correction: reuse the canonical pseudocompactness API while retaining the verified
-- graph-metric proof as the label-associated main entry.
/-- Exercise 35.3: A metrizable space is bounded for every compatible metric if and only if it
is pseudocompact. -/
theorem boundedForEveryCompatibleMetric_iff_pseudocompactSpace
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    BoundedForEveryCompatibleMetric X ↔ PseudocompactSpace X := by
  constructor
  · intro hmetrics
    -- The graph metric turns a uniform metric bound into a range bound for any continuous map.
    rw [pseudocompactSpace_iff]
    intro f hf
    obtain ⟨metric, hcompatible, hdominates⟩ :=
      existsCompatibleMetricDistDominates hf
    obtain ⟨C, hC⟩ := hmetrics metric hcompatible
    rw [Metric.isBounded_range_iff]
    exact ⟨C, fun x y ↦ (hdominates x y).trans (hC x y)⟩
  · intro hpseudo metric hcompatible
    -- In the empty case the pairwise bound is vacuous.
    cases isEmpty_or_nonempty X with
    | inl hEmpty =>
        letI : IsEmpty X := hEmpty
        exact ⟨0, fun x ↦ isEmptyElim x⟩
    | inr hNonempty =>
        letI : Nonempty X := hNonempty
        -- Otherwise pseudocompactness bounds distance from a base point, hence every distance.
        let x₀ : X := Classical.choice hNonempty
        have hcontinuous : Continuous (metric.dist x₀) :=
          continuousCompatibleMetricDist metric hcompatible x₀
        have hbounded : Bornology.IsBounded (Set.range (metric.dist x₀)) :=
          (pseudocompactSpace_iff X).mp hpseudo (metric.dist x₀) hcontinuous
        exact pairwiseDistBoundOfBoundedDistanceRange metric x₀ hbounded

/-- Helper for Exercise 35.3: A metrizable space is pseudocompact if and only if it is limit
point compact. -/
theorem pseudocompactSpace_iff_limitPointCompactSpace
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    PseudocompactSpace X ↔ LimitPointCompactSpace X := by
  constructor
  · intro hpseudo
    rw [limitPointCompactSpace_iff]
    intro s hsInfinite
    -- If `s` had no accumulation point, it would be a closed infinite discrete subspace.
    by_contra hnoAccPt
    push Not at hnoAccPt
    have hsClosed : IsClosed s := by
      rw [isClosed_iff_accPt]
      intro x hx
      exact (hnoAccPt x hx).elim
    letI : Infinite s := hsInfinite.to_subtype
    letI : DiscreteTopology s :=
      discreteTopology_of_noAccPts fun x _ ↦ hnoAccPt x
    obtain ⟨f, hfUnbounded⟩ :=
      existsContinuousMapUnboundedRangeOfInfiniteDiscrete s
    -- Tietze extension transports the unbounded discrete function to all of `X`.
    obtain ⟨g, hg⟩ := f.exists_restrict_eq hsClosed
    apply hfUnbounded
    refine hpseudo.isBounded_range g |>.subset ?_
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, DFunLike.congr_fun hg x⟩
  · intro hlimit
    -- In a metrizable space, limit point compactness gives sequential compactness and compactness.
    have hcountablyCompact : CountablyCompactSpace X :=
      (limitPointCompactSpace_iff_countablyCompactSpace X).mp hlimit
    letI : CompactSpace X := compactSpace_iff_seqCompactSpace.mpr
      ⟨hcountablyCompact.isCountablyCompact_univ.isSeqCompact⟩
    exact inferInstance

end
