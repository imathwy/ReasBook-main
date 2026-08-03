module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
import Topology_Munkres_2000.Book.Definition_50_8.FiniteClosedUnion
import Topology_Munkres_2000.Book.Exercise_50_6
import Topology_Munkres_2000.Book.Theorem_50_6
import Mathlib.Topology.ShrinkingLemma

public section

universe u

/-- Helper for Exercise 50.7: a compact subset of a Euclidean-charted locally compact
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

/-- Helper for Exercise 50.7: a compact set contained in one chart source has covering
dimension at most the dimension of the Euclidean model. -/
private lemma compactSubset_chartSource_hasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    (K : Set M) (hK : IsCompact K) (x : M)
    (hK_source : K ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) x).source) :
    HasCoveringDimensionLE K m := by
  -- The chart sends the compact set to a compact subset of the Euclidean model.
  have h_image_compact :
      IsCompact ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) :=
    hK.image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin m)) x).continuousOn.mono hK_source)
  have h_image_eq :
      (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K =
        (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K := by
    rfl
  let restrictedChart :
      K ≃ₜ (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K :=
    (chartAt (EuclideanSpace ℝ (Fin m)) x).homeomorphOfImageSubsetSource
      hK_source h_image_eq
  -- Apply the Euclidean bound and transport it back through the restricted chart.
  have h_image_dimension :
      HasCoveringDimensionLE
        ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) m :=
    compactSubset_euclideanSpace_hasCoveringDimensionLE _ h_image_compact
  exact h_image_dimension.homeomorph restrictedChart.symm

/-- Helper for Exercise 50.7: every compact subset of a locally compact Hausdorff space
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

/-- Exercise 50.7. Every `m`-manifold admits a closed embedding into
`EuclideanSpace ℝ (Fin (2 * m + 1))`. -/
theorem exists_isClosedEmbedding_euclidean_of_manifold {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [TopologicalManifold m M] :
    ∃ f : M → EuclideanSpace ℝ (Fin (2 * m + 1)),
      Topology.IsClosedEmbedding f := by
  -- Manifold charts provide local compactness, while the manifold instance already
  -- supplies the Hausdorff and second-countability assumptions of Exercise 50.6.
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) M
  -- The compact chart-cover lemma supplies the remaining dimension hypothesis.
  exact exists_isClosedEmbedding_euclidean_of_compactDimension_le fun K hK ↦
    compactSubset_chartedSpace_hasCoveringDimensionLE K hK
