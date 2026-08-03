module

public import Topology_Munkres_2000.Book.Lemma_39_2
public import Topology_Munkres_2000.Book.Exercise_13_99_1.BarycentricRefinement
public import Mathlib.Topology.ShrinkingLemma

public section

universe u

/-- Helper for Exercise 13.99.1: among two intersecting metric balls, the ball with
the larger radius has its triple-radius ball containing their union. -/
private lemma metricBall_union_subset_tripleBall_of_inter
    {X : Type*} [PseudoMetricSpace X] {x y : X} {r s : ℝ} (hrs : r ≤ s)
    (hinter : (Metric.ball x r ∩ Metric.ball y s).Nonempty) :
    Metric.ball x r ∪ Metric.ball y s ⊆ Metric.ball y (3 * s) := by
  -- Route both sides of the union through a point common to the two balls.
  obtain ⟨z, hzx, hzy⟩ := hinter
  intro w hw
  rw [Set.mem_union] at hw
  rw [Metric.mem_ball]
  rcases hw with hwx | hwy
  · rw [Metric.mem_ball] at hwx hzx hzy
    have htriangle := dist_triangle4 w x z y
    rw [dist_comm z x] at hzx
    linarith
  · rw [Metric.mem_ball] at hwy hzy
    have hspos := Metric.pos_of_mem_ball hzy
    linarith

/-- Helper for Exercise 13.99.1: the cell associated to `J` consists of the points
in every `A i` for `i ∈ J` and outside every `closure (C i)` for `i ∉ J`. -/
private def barycentricCell {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (A C : ι → Set X) (J : Finset ι) : Set X :=
  (⋂ i ∈ J, A i) \ (⋃ i ∈ Jᶜ, closure (C i))

/-- Helper for Exercise 13.99.1: a barycentric cell is contained in every
original set indexed by its signature. -/
private lemma barycentricCell_subset_of_mem {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι]
    (A C : ι → Set X) {J : Finset ι} {i : ι} (hi : i ∈ J) :
    barycentricCell A C J ⊆ A i := by
  -- Read the required coordinate from the finite intersection defining the cell.
  intro x hx
  exact Set.mem_iInter.mp (Set.mem_iInter.mp hx.1 i) hi

/-- Helper for Exercise 13.99.1: cells built from open `A i` are open. -/
private lemma isOpen_barycentricCell {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] (A C : ι → Set X)
    (hAopen : ∀ i, IsOpen (A i)) (J : Finset ι) :
    IsOpen (barycentricCell A C J) := by
  -- A finite open intersection minus a finite union of closed sets is open.
  exact (isOpen_biInter_finset fun i _ ↦ hAopen i).sdiff
    (isClosed_biUnion_finset (f := fun i ↦ closure (C i)) fun _ _ ↦ isClosed_closure)

/-- Helper for Exercise 13.99.1: membership in `C i` forces `i` into the
signature of every barycentric cell containing that point. -/
private lemma index_mem_of_mem_barycentricCell_of_mem
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (A C : ι → Set X) {J : Finset ι} {i : ι} {x : X}
    (hxcell : x ∈ barycentricCell A C J) (hxC : x ∈ C i) : i ∈ J := by
  -- Otherwise `x` lies in one of the excluded closures, contradicting cell membership.
  by_contra hi
  have hiCompl : i ∈ Jᶜ := Finset.mem_compl.mpr hi
  have hxClosure : x ∈ closure (C i) := subset_closure hxC
  have hxExcluded : x ∈ ⋃ j ∈ Jᶜ, closure (C j) :=
    Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem hiCompl hxClosure)
  exact hxcell.2 hxExcluded

/-- Helper for Exercise 13.99.1: the nonempty finite-signature barycentric cells
cover the space whenever `C` covers and `closure (C i) ⊆ A i`. -/
private lemma sUnion_barycentricCells {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] (A C : ι → Set X)
    (hCcover : ⋃ i, C i = Set.univ)
    (hclosure : ∀ i, closure (C i) ⊆ A i) :
    ⋃₀ Set.range (fun J : {J : Finset ι // J.Nonempty} ↦ barycentricCell A C J) =
      Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  -- Use the complete `A`-membership signature of `x`.
  have hxCover : x ∈ ⋃ i, C i := hCcover.symm ▸ Set.mem_univ x
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxCover
  have hxiA : x ∈ A i := hclosure i (subset_closure hxi)
  let J : Finset ι := Finset.univ.filter (fun j ↦ x ∈ A j)
  have hJnonempty : J.Nonempty := by
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxiA⟩⟩
  have hcellRange : barycentricCell A C J ∈
      Set.range (fun K : {K : Finset ι // K.Nonempty} ↦ barycentricCell A C K) :=
    ⟨⟨J, hJnonempty⟩, rfl⟩
  rw [Set.mem_sUnion]
  refine ⟨barycentricCell A C J, hcellRange, ?_⟩
  constructor
  · -- Every index in the signature records actual `A`-membership.
    rw [Set.mem_iInter]
    intro j
    rw [Set.mem_iInter]
    intro hj
    exact (Finset.mem_filter.mp hj).2
  · -- An excluded closure would force its index back into the signature.
    intro hxExcluded
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxExcluded
    obtain ⟨hjCompl, hxjClosure⟩ := Set.mem_iUnion.mp hxj
    have hxjA : x ∈ A j := hclosure j hxjClosure
    have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxjA⟩
    exact (Finset.mem_compl.mp hjCompl) hjJ

/-- Helper for Exercise 13.99.1: the finite-signature cells form a barycentric
refinement of the indexed original cover. -/
private lemma isBarycentricRefinement_barycentricCells
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (A C : ι → Set X) (𝒜 : Set (Set X)) (hAmem : ∀ i, A i ∈ 𝒜)
    (hAopen : ∀ i, IsOpen (A i)) (hCcover : ⋃ i, C i = Set.univ)
    (hclosure : ∀ i, closure (C i) ⊆ A i) :
    IsBarycentricRefinement
      (Set.range (fun J : {J : Finset ι // J.Nonempty} ↦ barycentricCell A C J)) 𝒜 := by
  classical
  rw [isBarycentricRefinement_iff]
  refine ⟨isOpenRefinement_range _ 𝒜 ?_ ?_,
    sUnion_barycentricCells A C hCcover hclosure, ?_⟩
  · -- Openness is inherited from the finite-cell construction.
    intro J
    exact isOpen_barycentricCell A C hAopen J
  · -- A nonempty signature supplies an original-cover parent.
    intro J
    obtain ⟨i, hi⟩ := J.property
    exact ⟨A i, hAmem i, barycentricCell_subset_of_mem A C hi⟩
  · -- At an intersection point, one member of the shrinking cover indexes both cells.
    rintro B ⟨J, rfl⟩ B' ⟨K, rfl⟩ hinter
    obtain ⟨x, hxJ, hxK⟩ := hinter
    have hxCover : x ∈ ⋃ i, C i := hCcover.symm ▸ Set.mem_univ x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxCover
    have hiJ := index_mem_of_mem_barycentricCell_of_mem A C hxJ hxi
    have hiK := index_mem_of_mem_barycentricCell_of_mem A C hxK hxi
    exact ⟨A i, hAmem i, Set.union_subset
      (barycentricCell_subset_of_mem A C hiJ)
      (barycentricCell_subset_of_mem A C hiK)⟩

/-- Exercise 13.99.1 (1). Every open cover of a metrizable space admits a
barycentric refinement. -/
theorem exists_barycentricRefinement_of_metrizable {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] (𝒜 : Set (Set X))
    (h_open : ∀ A ∈ 𝒜, IsOpen A)
    (h_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℬ : Set (Set X), IsBarycentricRefinement ℬ 𝒜 := by
  classical
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  -- Around each point, choose a ball whose triple-radius ball has an original-cover parent.
  have hlocal : ∀ x : X, ∃ r > 0, ∃ A ∈ 𝒜, Metric.ball x (3 * r) ⊆ A := by
    intro x
    have hxCover : x ∈ ⋃₀ 𝒜 := h_cover.symm ▸ Set.mem_univ x
    obtain ⟨A, hA, hxA⟩ := Set.mem_sUnion.mp hxCover
    obtain ⟨δ, hδpos, hδsub⟩ := (Metric.isOpen_iff.mp (h_open A hA)) x hxA
    have hradius : 0 < δ / 3 := by
      linarith
    have hscale : 3 * (δ / 3) = δ := by
      ring
    refine ⟨δ / 3, hradius, A, hA, ?_⟩
    rwa [hscale]
  choose r hrpos A hAmem htriple using hlocal
  let ℬ : Set (Set X) := Set.range (fun x ↦ Metric.ball x (r x))
  refine ⟨ℬ, ?_⟩
  rw [isBarycentricRefinement_iff]
  refine ⟨isOpenRefinement_range _ 𝒜 (fun _ ↦ Metric.isOpen_ball) ?_, ?_, ?_⟩
  · -- Each chosen ball is contained in its triple-radius parent.
    intro x
    refine ⟨A x, hAmem x, (Metric.ball_subset_ball ?_).trans (htriple x)⟩
    linarith [hrpos x]
  · -- Every point is the center of one of the chosen positive-radius balls.
    unfold ℬ
    rw [Set.sUnion_range]
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion_of_mem x (Metric.mem_ball_self (hrpos x))
  · -- Order the two radii; the larger one's parent contains the union.
    rintro B ⟨x, rfl⟩ B' ⟨y, rfl⟩ hinter
    rcases le_total (r x) (r y) with hxy | hyx
    · exact ⟨A y, hAmem y,
        (metricBall_union_subset_tripleBall_of_inter hxy hinter).trans (htriple y)⟩
    · have hinter' : (Metric.ball y (r y) ∩ Metric.ball x (r x)).Nonempty := by
        simpa only [Set.inter_comm] using hinter
      have hsubset := metricBall_union_subset_tripleBall_of_inter hyx hinter'
      have hunion : Metric.ball x (r x) ∪ Metric.ball y (r y) ⊆ A x := by
        simpa only [Set.union_comm] using hsubset.trans (htriple x)
      exact ⟨A x, hAmem x, hunion⟩

/-- Exercise 13.99.1 (2). Every open cover of a compact Hausdorff space admits a
barycentric refinement. -/
theorem exists_barycentricRefinement_of_compact_t2 {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (𝒜 : Set (Set X)) (h_open : ∀ A ∈ 𝒜, IsOpen A)
    (h_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℬ : Set (Set X), IsBarycentricRefinement ℬ 𝒜 := by
  classical
  -- Compactness reduces the original cover to a finite indexed family.
  have hindexedCover : Set.univ ⊆ ⋃ U : 𝒜, (U : Set X) := by
    intro x _
    have hxCover : x ∈ ⋃₀ 𝒜 := h_cover.symm ▸ Set.mem_univ x
    obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hxCover
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : 𝒜 ↦ (U : Set X)) (fun U ↦ h_open U U.property) hindexedCover
  let ι := {U : 𝒜 // U ∈ t}
  let A : ι → Set X := fun i ↦ i.1.1
  have hAmem : ∀ i : ι, A i ∈ 𝒜 := fun i ↦ i.1.2
  have hAopen : ∀ i : ι, IsOpen (A i) := fun i ↦ h_open i.1.1 i.1.2
  have hAcover : ⋃ i : ι, A i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨U, hUt⟩, hxU⟩
  -- Normality shrinks the finite family while retaining closure control.
  obtain ⟨C, hCcover, hCopen, hclosure⟩ :=
    exists_iUnion_eq_closure_subset hAopen (fun x ↦ Set.toFinite {i | x ∈ A i}) hAcover
  -- The membership-signature cells now satisfy all barycentric-refinement fields.
  exact ⟨Set.range (fun J : {J : Finset ι // J.Nonempty} ↦ barycentricCell A C J),
    isBarycentricRefinement_barycentricCells A C 𝒜 hAmem hAopen hCcover hclosure⟩
