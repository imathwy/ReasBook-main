module

public import Topology_Munkres_2000.Book.Theorem_36_1
public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Mathlib.Data.PNat.Defs
public import Mathlib.Topology.Compactness.Compact

public section

open Set TopologicalSpace

universe u

/-- Helper for Theorem 36.2: a partition coefficient times its subordinate chart is continuous. -/
private lemma continuous_partitionWeightedChart {m : ℕ} {X : Type u} {ι : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin m)) X]
    (ρ : PartitionOfUnity ι X univ) (c : ι → X)
    (hρ : ρ.IsSubordinate fun i ↦ (chartAt (EuclideanSpace ℝ (Fin m)) (c i)).source)
    (i : ι) :
    Continuous fun x ↦ ρ i x • chartAt (EuclideanSpace ℝ (Fin m)) (c i) x := by
  -- Subordination puts the entire topological support inside the chart domain.
  apply ρ.continuous_smul
  intro x hx
  exact (chartAt (EuclideanSpace ℝ (Fin m)) (c i)).continuousAt (hρ i hx)

/-- Helper for Theorem 36.2: a nonzero scalar multiple of chart values still separates points. -/
private lemma localHomeomorph_eq_of_smul_eq_smul {m : ℕ} {X : Type u}
    [TopologicalSpace X] (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m)))
    {x y : X} (hx : x ∈ e.source) (hy : y ∈ e.source) {c : ℝ} (hc : c ≠ 0)
    (hxy : c • e x = c • e y) : x = y := by
  -- Cancel the active coefficient, then use injectivity on the local chart source.
  have he : e x = e y := smul_right_injective _ hc hxy
  exact e.injOn hx hy he

/-- Helper for Theorem 36.2: equal partition coefficients and weighted charts
determine the point. -/
private lemma eq_of_partitionWeightedCharts_eq {m : ℕ} {X : Type u} {ι : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin m)) X]
    (ρ : PartitionOfUnity ι X univ) (c : ι → X)
    (hρ : ρ.IsSubordinate fun i ↦ (chartAt (EuclideanSpace ℝ (Fin m)) (c i)).source)
    {x y : X} (hcoeff : ∀ i, ρ i x = ρ i y)
    (hweighted : ∀ i,
      ρ i x • chartAt (EuclideanSpace ℝ (Fin m)) (c i) x =
        ρ i y • chartAt (EuclideanSpace ℝ (Fin m)) (c i) y) : x = y := by
  -- Choose a positive coefficient, which selects a chart containing both points.
  obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ x)
  have hix_support : x ∈ Function.support (ρ i) := hi.ne'
  have hix : x ∈ (chartAt (EuclideanSpace ℝ (Fin m)) (c i)).source :=
    hρ i (subset_closure hix_support)
  have hiy_pos : 0 < ρ i y := by
    rwa [← hcoeff i]
  have hiy_support : y ∈ Function.support (ρ i) := hiy_pos.ne'
  have hiy : y ∈ (chartAt (EuclideanSpace ℝ (Fin m)) (c i)).source :=
    hρ i (subset_closure hiy_support)
  -- Rewrite to a common nonzero scalar and invoke chart injectivity.
  apply localHomeomorph_eq_of_smul_eq_smul
    (chartAt (EuclideanSpace ℝ (Fin m)) (c i)) hix hiy hi.ne'
  calc
    ρ i x • chartAt (EuclideanSpace ℝ (Fin m)) (c i) x =
        ρ i y • chartAt (EuclideanSpace ℝ (Fin m)) (c i) y := hweighted i
    _ = ρ i x • chartAt (EuclideanSpace ℝ (Fin m)) (c i) y := by rw [hcoeff i]

/-- Theorem 36.2. Every compact `m`-manifold admits a topological embedding into
`EuclideanSpace ℝ (Fin N)` for some positive integer `N`. -/
theorem exists_isEmbedding_euclidean_of_compact_manifold {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin m)) X]
    [TopologicalManifold m X] [CompactSpace X] :
    ∃ (N : ℕ+) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f := by
  classical
  -- The chart sources form an open cover; compactness reduces it to finitely many charts.
  let allCharts : X → Opens X := fun c ↦
    ⟨(chartAt (EuclideanSpace ℝ (Fin m)) c).source,
      (chartAt (EuclideanSpace ℝ (Fin m)) c).open_source⟩
  have hallCharts : IsOpenCover allCharts := by
    apply top_unique
    rw [← SetLike.coe_subset_coe]
    intro x hx
    rw [Opens.coe_iSup, Set.mem_iUnion]
    exact ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin m)) x⟩
  obtain ⟨s, hs⟩ := hallCharts.exists_finite_of_compactSpace
  let I := ↥s
  let centers : I → X := fun i ↦ i.1
  let charts : I → Opens X := fun i ↦ allCharts i.1
  have hcharts : IsOpenCover charts := hs
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_finite charts hcharts
  -- Store coefficients and weighted chart coordinates in one finite coordinate family.
  let J := Unit ⊕ (I ⊕ (I × Fin m))
  let coordinates : X → J → ℝ := fun x ↦ Sum.elim (fun _ ↦ 0)
    (Sum.elim (fun i ↦ ρ i x) fun ij ↦
      (EuclideanSpace.equiv (Fin m) ℝ
        (ρ ij.1 x • chartAt (EuclideanSpace ℝ (Fin m)) (centers ij.1) x)) ij.2)
  have hcoordinates : Continuous coordinates := by
    apply continuous_pi
    intro j
    rcases j with j | j
    · exact continuous_const
    · rcases j with i | ij
      · exact (ρ i).continuous
      · exact (continuous_apply ij.2).comp
          ((EuclideanSpace.equiv (Fin m) ℝ).continuous.comp
            (continuous_partitionWeightedChart ρ centers hρ ij.1))
  -- Reindex the finite family by a standard `Fin` type and package it as Euclidean space.
  let reindex : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let coordinateFin : X → Fin (Fintype.card J) → ℝ :=
    fun x k ↦ coordinates x (reindex.symm k)
  have hcoordinateFin : Continuous coordinateFin := by
    apply continuous_pi
    intro k
    exact (continuous_apply (reindex.symm k)).comp hcoordinates
  let f : X → EuclideanSpace ℝ (Fin (Fintype.card J)) :=
    fun x ↦ (EuclideanSpace.equiv (Fin (Fintype.card J)) ℝ).symm (coordinateFin x)
  have hf_continuous : Continuous f :=
    (EuclideanSpace.equiv (Fin (Fintype.card J)) ℝ).symm.continuous.comp hcoordinateFin
  -- Equality of the Euclidean vectors recovers every coefficient and weighted chart value.
  have hf_injective : Function.Injective f := by
    intro x y hxy
    have hfin : coordinateFin x = coordinateFin y := by
      have h := congrArg (EuclideanSpace.equiv (Fin (Fintype.card J)) ℝ) hxy
      simpa only [f, ContinuousLinearEquiv.apply_symm_apply] using h
    have hcoordinate (j : J) : coordinates x j = coordinates y j := by
      simpa only [coordinateFin, Equiv.symm_apply_apply] using congrFun hfin (reindex j)
    apply eq_of_partitionWeightedCharts_eq ρ centers hρ
    · intro i
      exact hcoordinate (Sum.inr (Sum.inl i))
    · intro i
      apply (EuclideanSpace.equiv (Fin m) ℝ).injective
      funext k
      exact hcoordinate (Sum.inr (Sum.inr (i, k)))
  -- The dummy `Unit` coordinate makes the finite target dimension strictly positive.
  have hJ : 0 < Fintype.card J := Fintype.card_pos
  let N : ℕ+ := ⟨Fintype.card J, hJ⟩
  refine ⟨N, f, ?_⟩
  exact (hf_continuous.isClosedEmbedding hf_injective).isEmbedding
