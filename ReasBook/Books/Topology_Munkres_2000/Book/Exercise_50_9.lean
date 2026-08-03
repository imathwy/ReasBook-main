module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Definition_50_8.FiniteClosedUnion
public import Topology_Munkres_2000.Book.Exercise_46_10.SigmaCompact
public import Topology_Munkres_2000.Book.Exercise_50_8
public import Topology_Munkres_2000.Book.Theorem_50_6
public import Mathlib.Topology.ShrinkingLemma

public section

universe u

/-- Helper for Exercise 50.9: a compact subset of a Euclidean-charted locally compact
Hausdorff space is an exact finite union of compact closed sets lying in chart sources. -/
private lemma existsFiniteCompactChartCover {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [LocallyCompactSpace M] (K : Set M) (hK : IsCompact K) :
    ∃ (t : Finset M) (C : t → Set M), K = ⋃ i, C i ∧
      (∀ i, IsClosed (C i)) ∧ (∀ i, IsCompact (C i)) ∧
      ∀ i, C i ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source := by
  classical
  -- First reduce the full family of chart sources to a finite cover of `K`.
  have h_chart_open : ∀ x : M,
      IsOpen (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x
    exact (chartAt (EuclideanSpace ℝ (Fin m)) x).open_source
  have h_chart_cover :
      K ⊆ ⋃ x : M, (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin m)) x⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin m)) x).source)
    h_chart_open h_chart_cover
  let U : t → Set M := fun i ↦ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source
  have hKU : K ⊆ ⋃ i, U i := by
    intro x hx
    have hx_cover := ht hx
    simp only [Set.mem_iUnion] at hx_cover ⊢
    obtain ⟨i, hi, hxi⟩ := hx_cover
    exact ⟨⟨i, hi⟩, hxi⟩
  -- Shrink that finite cover to compact closed sets still contained in their charts.
  have hU_open : ∀ i, IsOpen (U i) := by
    intro i
    exact (chartAt (EuclideanSpace ℝ (Fin m)) i.1).open_source
  have hU_pointFinite : ∀ x ∈ K, {i | x ∈ U i}.Finite := by
    intro _ _
    exact Set.toFinite _
  obtain ⟨V, hKV, hV_closed, hV_subset, hV_compact⟩ :=
    exists_subset_iUnion_compact_subset_t2space (u := U) hK hU_open hU_pointFinite hKU
  let C : t → Set M := fun i ↦ K ∩ V i
  refine ⟨t, C, ?_, ?_, ?_, ?_⟩
  · -- Intersecting with `K` changes containment into an exact union equality.
    ext x
    constructor
    · intro hxK
      have hxV := hKV hxK
      rw [Set.mem_iUnion] at hxV ⊢
      obtain ⟨i, hxi⟩ := hxV
      exact ⟨i, hxK, hxi⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      exact hxi.1
  · intro i
    exact hK.isClosed.inter (hV_closed i)
  · intro i
    exact (hV_compact i).inter_left hK.isClosed
  · intro i _ hxi
    exact hV_subset i hxi.2

/-- Helper for Exercise 50.9: a compact set contained in one chart source has covering
dimension at most the dimension of the Euclidean model. -/
private lemma compactSubset_chartSource_hasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    (K : Set M) (hK : IsCompact K) (x : M)
    (hK_source : K ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) x).source) :
    HasCoveringDimensionLE K m := by
  -- The restricted chart identifies `K` with its compact image in Euclidean space.
  have h_image_compact :
      IsCompact ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) :=
    hK.image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin m)) x).continuousOn.mono hK_source)
  have h_image_identity :
      (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K =
        (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K := rfl
  let restrictedChart :=
    (chartAt (EuclideanSpace ℝ (Fin m)) x).homeomorphOfImageSubsetSource
      hK_source h_image_identity
  have h_image_dimension :=
    compactSubset_euclideanSpace_hasCoveringDimensionLE
      ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) h_image_compact
  -- Transfer the Euclidean bound back along the inverse restricted chart.
  exact h_image_dimension.homeomorph restrictedChart.symm

/-- Helper for Exercise 50.9: every compact subset of a locally compact Hausdorff space
charted by `EuclideanSpace ℝ (Fin m)` has covering dimension at most `m`. -/
private lemma compactSubset_chartedSpace_hasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [LocallyCompactSpace M] (K : Set M) (hK : IsCompact K) :
    HasCoveringDimensionLE K m := by
  -- Apply the chart bound to every member of an exact finite compact chart cover.
  obtain ⟨t, C, hC_union, hC_closed, hC_compact, hC_source⟩ :=
    existsFiniteCompactChartCover (m := m) K hK
  have hC_dimension : ∀ i, HasCoveringDimensionLE (C i) m := by
    intro i
    exact compactSubset_chartSource_hasCoveringDimensionLE
      (C i) (hC_compact i) i.1 (hC_source i)
  have h_union_dimension :=
    HasCoveringDimensionLE.finiteUnionClosedSubtypes C hC_closed hC_dimension
  -- The cover equality identifies the finite union with the original compact subtype.
  rw [hC_union]
  exact h_union_dimension

/-- Exercise 50.9. Every topological `m`-manifold has covering dimension at most `m`. -/
theorem manifold_coveringDimension_le {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [TopologicalManifold m M] :
    HasCoveringDimensionLE M m := by
  -- Manifold charts supply local compactness; second countability then supplies an exhaustion.
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) M
  letI : CompactlyExhaustibleSpace M :=
    compactlyExhaustibleSpace_of_weaklyLocallyCompact_secondCountable M
  -- Exercise 50.8 globalizes the uniform bound on compact subspaces.
  have h_compact_dimension :
      ∀ K : Set M, IsCompact K → HasCoveringDimensionLE K m := by
    intro K hK
    exact compactSubset_chartedSpace_hasCoveringDimensionLE K hK
  exact hasCoveringDimensionLE_of_compact_subspaces h_compact_dimension
