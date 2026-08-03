module

public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded
public import Topology_Munkres_2000.Book.Theorem_45_4.ProperTarget
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergence

public section

open Filter

universe u

/-- Helper for Exercise 45.3: equicontinuity passes from an indexed function-like family to
the same family indexed by its range. -/
private lemma equicontinuous_range_of_equicontinuous
    {ι X Y A : Type*} [TopologicalSpace X] [UniformSpace Y]
    [CoeFun A (fun _ ↦ X → Y)] (F : ι → A)
    (hF : Equicontinuous (fun i ↦ (F i : X → Y))) :
    Equicontinuous (fun g : Set.range F ↦ (g.1 : X → Y)) := by
  -- Choose a source index for each range element and reindex the original family.
  classical
  let index : Set.range F → ι := fun g ↦ g.property.choose
  have h_reindexed := hF.comp index
  -- Identify the chosen representative with the corresponding range element pointwise.
  have h_family : (fun g ↦ (F (index g) : X → Y)) =
      fun g : Set.range F ↦ (g.1 : X → Y) := by
    funext g x
    exact congrFun (congrArg (fun a : A ↦ (a : X → Y)) (Exists.choose_spec g.property)) x
  simpa only [Function.comp_def, h_family] using h_reindexed

/-- Helper for Exercise 45.3: pointwise boundedness passes from an indexed function-like family
to the same family indexed by its range. -/
private lemma pointwiseBounded_range_of_pointwiseBounded
    {ι X Y A : Type*} [Bornology Y] [CoeFun A (fun _ ↦ X → Y)]
    (F : ι → A) (hF : PointwiseBounded (fun i ↦ (F i : X → Y))) :
    PointwiseBounded (fun g : Set.range F ↦ (g.1 : X → Y)) := by
  -- Compare each range-indexed evaluation set with the original evaluation range.
  classical
  rw [pointwiseBounded_iff]
  intro x
  let index : Set.range F → ι := fun g ↦ g.property.choose
  have h_range : Set.range (fun g : Set.range F ↦ g.1 x) ⊆
      Set.range (fun i ↦ F i x) := by
    intro y hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨index g,
      congrFun (congrArg (fun a : A ↦ (a : X → Y)) g.property.choose_spec) x⟩
  exact (pointwiseBounded_iff.1 hF x).subset h_range

/-- Helper for Exercise 45.3: convergence of bounded continuous maps on a compact domain
passes to their underlying continuous maps. -/
private lemma tendsto_toContinuousMap_of_tendsto
    {ι X Y : Type*} [TopologicalSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    {p : Filter ι} {F : ι → BoundedContinuousFunction X Y}
    {G : BoundedContinuousFunction X Y}
    (hF : Tendsto F p (nhds G)) :
    Tendsto (fun i ↦ (F i).toContinuousMap) p (nhds G.toContinuousMap) := by
  -- Use continuity of the inverse compact-domain isometry equivalence.
  exact (ContinuousMap.isometryEquivBoundedOfCompact X Y).symm.continuous.continuousAt.tendsto.comp
    hF

/-- Helper for Exercise 45.3: converting a continuous map to a bounded continuous map on a
compact domain and back recovers the original map. -/
private lemma toContinuousMap_equivBoundedOfCompact
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    (f : C(X, Y)) :
    (ContinuousMap.equivBoundedOfCompact X Y f).toContinuousMap = f := by
  -- This is the inverse law for the compact-domain equivalence.
  exact (ContinuousMap.equivBoundedOfCompact X Y).symm_apply_apply f

/-- Exercise 45.3. Arzelà's theorem: a pointwise bounded equicontinuous sequence of
continuous maps from a compact space to `ℝ^k` has a uniformly convergent
subsequence. -/
theorem exists_uniformlyConvergent_subsequence_of_equicontinuous
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {k : ℕ}
    (f : ℕ → C(X, Fin k → ℝ))
    (h_pointwise_bounded : PointwiseBounded (fun n ↦ (f n : X → Fin k → ℝ)))
    (h_equicontinuous : Equicontinuous (fun n ↦ (f n : X → Fin k → ℝ))) :
    ∃ (φ : ℕ → ℕ) (g : C(X, Fin k → ℝ)), StrictMono φ ∧
      TendstoUniformly (fun n ↦ (f (φ n) : X → Fin k → ℝ)) g atTop := by
  -- Transfer the sequence to bounded continuous maps on the compact domain.
  let F : ℕ → BoundedContinuousFunction X (Fin k → ℝ) := fun n ↦
    ContinuousMap.equivBoundedOfCompact X (Fin k → ℝ) (f n)
  have hF_coe : (fun n ↦ (F n : X → Fin k → ℝ)) =
      fun n ↦ (f n : X → Fin k → ℝ) := by
    -- Compute the underlying function through the inverse equivalence.
    funext n x
    exact congrFun (congrArg DFunLike.coe (toContinuousMap_equivBoundedOfCompact (f n))) x
  have hF_equicontinuous : Equicontinuous (fun n ↦ (F n : X → Fin k → ℝ)) := by
    rw [hF_coe]
    exact h_equicontinuous
  have hF_pointwise_bounded : PointwiseBounded (fun n ↦ (F n : X → Fin k → ℝ)) := by
    rw [hF_coe]
    exact h_pointwise_bounded
  -- Arzelà--Ascoli makes the closure of the sequence range compact.
  have h_compact : IsCompact (closure (Set.range F)) := by
    apply (BoundedContinuousFunction.isCompact_closure_iff_equicontinuous_and_pointwiseBounded
      (Set.range F)).2
    exact ⟨equicontinuous_range_of_equicontinuous F hF_equicontinuous,
      pointwiseBounded_range_of_pointwiseBounded F hF_pointwise_bounded⟩
  have h_mem : ∀ n, F n ∈ closure (Set.range F) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  -- Sequential compactness supplies a convergent subsequence of bounded maps.
  obtain ⟨G, _hG, φ, hφ, h_tendsto⟩ := h_compact.tendsto_subseq h_mem
  refine ⟨φ, G.toContinuousMap, hφ, ?_⟩
  -- Transport convergence back to continuous maps and identify it with uniform convergence.
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mp
  have h_continuousMap := tendsto_toContinuousMap_of_tendsto h_tendsto
  have h_subsequence : (fun n ↦ (F (φ n)).toContinuousMap) = fun n ↦ f (φ n) := by
    -- Compute the compact-domain equivalence along the extracted subsequence.
    funext n
    exact toContinuousMap_equivBoundedOfCompact (f (φ n))
  rw [← h_subsequence]
  simpa only [Function.comp_def] using h_continuousMap
