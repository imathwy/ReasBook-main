module

public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded
public import Topology_Munkres_2000.Book.Exercise_46_10.CompactExhaustible
public import Topology_Munkres_2000.Book.Exercise_47_2
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.CompactConvergence

import Topology_Munkres_2000.Book.Exercise_46_10.CompactConvergence

public section

open Filter

universe u

/-- Helper for Exercise 47.4: equicontinuity passes from an indexed family of continuous maps
to the same family indexed by its range. -/
private lemma equicontinuous_range_continuousMap
    {ι X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (F : ι → C(X, Y)) (hF : Equicontinuous (fun i ↦ (F i : X → Y))) :
    Equicontinuous (fun g : Set.range F ↦ (g.1 : X → Y)) := by
  -- Choose a source index for each range element and reindex the original family.
  classical
  let index : Set.range F → ι := fun g ↦ g.property.choose
  have h_reindexed := hF.comp index
  -- The chosen representative is equal to the corresponding range element.
  have h_family : (fun g ↦ (F (index g) : X → Y)) =
      fun g : Set.range F ↦ (g.1 : X → Y) := by
    funext g x
    exact congrFun (congrArg DFunLike.coe (Exists.choose_spec g.property)) x
  simpa only [Function.comp_def, h_family] using h_reindexed

/-- Helper for Exercise 47.4: pointwise boundedness passes from an indexed family of continuous
maps to the same family indexed by its range. -/
private lemma pointwiseBounded_range_continuousMap
    {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Bornology Y]
    (F : ι → C(X, Y)) (hF : PointwiseBounded (fun i ↦ (F i : X → Y))) :
    PointwiseBounded (fun g : Set.range F ↦ (g.1 : X → Y)) := by
  -- Identify the bundled range with the underlying function family pointwise.
  classical
  rw [pointwiseBounded_iff]
  intro x
  let index : Set.range F → ι := fun g ↦ g.property.choose
  have h_range : Set.range (fun g : Set.range F ↦ g.1 x) ⊆
      Set.range (fun i ↦ F i x) := by
    intro y hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨index g, congrFun (congrArg DFunLike.coe g.property.choose_spec) x⟩
  exact (pointwiseBounded_iff.1 hF x).subset h_range

/-- Exercise 47.4. Arzelà's theorem, general version: a pointwise bounded equicontinuous
sequence of maps from a Hausdorff σ-compact space to `ℝ^k` has a subsequence converging in
the topology of compact convergence to a continuous function. Here σ-compactness is understood
in Munkres's sense, formalized by `CompactlyExhaustibleSpace`. -/
theorem exists_compactConvergence_subsequence_of_equicontinuous
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactlyExhaustibleSpace X]
    {k : ℕ} (f : ℕ → X → Fin k → ℝ) (h_pointwise_bounded : PointwiseBounded f)
    (h_equicontinuous : Equicontinuous f) :
    ∃ (φ : ℕ → ℕ) (g : C(X, Fin k → ℝ)), StrictMono φ ∧
      Tendsto (fun n ↦ UniformOnFun.ofFun {K : Set X | IsCompact K} (f (φ n))) atTop
        (nhds (UniformOnFun.ofFun {K : Set X | IsCompact K} g)) := by
  -- Bundle the equicontinuous raw maps as continuous maps.
  have h_continuous : ∀ n, Continuous (f n) := h_equicontinuous.continuous
  let F : ℕ → C(X, Fin k → ℝ) := fun n ↦ ⟨f n, h_continuous n⟩
  have hF_equicontinuous : Equicontinuous (fun n ↦ (F n : X → Fin k → ℝ)) := by
    simpa only [F, ContinuousMap.coe_mk] using h_equicontinuous
  have hF_pointwise_bounded : PointwiseBounded (fun n ↦ (F n : X → Fin k → ℝ)) := by
    simpa only [F, ContinuousMap.coe_mk] using h_pointwise_bounded
  -- Arzelà--Ascoli makes the closure of the sequence range compact.
  have h_compact : IsCompact (closure (Set.range F)) := by
    apply (ContinuousMap.isCompact_closure_iff_equicontinuous_and_pointwiseBounded
      (Set.range F)).2
    exact ⟨equicontinuous_range_continuousMap F hF_equicontinuous,
      pointwiseBounded_range_continuousMap F hF_pointwise_bounded⟩
  have h_mem : ∀ n, F n ∈ closure (Set.range F) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  -- Sequential compactness supplies a convergent subsequence in the compact-open topology.
  obtain ⟨g, _hg, φ, hφ, h_tendsto⟩ := h_compact.tendsto_subseq h_mem
  refine ⟨φ, g, hφ, ?_⟩
  -- Transport convergence through the canonical embedding into uniform convergence on compacts.
  have h_mapped :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding.continuous.continuousAt
      |>.tendsto.comp h_tendsto
  simpa only [Function.comp_def, F, ContinuousMap.toUniformOnFunIsCompact,
    ContinuousMap.coe_mk] using h_mapped
