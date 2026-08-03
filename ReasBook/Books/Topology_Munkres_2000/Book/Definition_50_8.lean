module

public import Topology_Munkres_2000.Book.Corollary_50_3
public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Definition_50_8.FiniteClosedUnion
public import Topology_Munkres_2000.Book.Definition_50_8.Partition
public import Topology_Munkres_2000.Book.Definition_50_8.ClosedSwelling
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.SmallInductiveDimension

public section

open TopologicalSpace

universe u

/- Definition 50.8 (1). `HasSmallInductiveDimensionLT` is the inductively defined strict small
inductive dimension bound; at `0`, it is the empty-space base case corresponding to dimension
`-1`. -/
#check HasSmallInductiveDimensionLT

/- Definition 50.8 (2). `HasSmallInductiveDimensionLE X n` represents small inductive dimension
at most `n` by abbreviating the strict bound `< n + 1`. -/
#check HasSmallInductiveDimensionLE

/- Definition 50.8 (3). The least small inductive dimension value is `smallInductiveDimension X`,
with `⊥` representing dimension `-1`. -/
#check smallInductiveDimension

-- Route correction: instead of unfolding covering dimension inside the two basis bridges, isolate
-- the finite closed-union invariant and the two directions of the local frontier characterization.

/-- Helper for Definition 50.8: a covering-dimension bound separates a closed set from the
complement of an open neighborhood by an open set with lower-dimensional frontier. -/
lemma exists_open_between_frontier_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {K U : Set X} (hK : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ V : Set X,
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧
        HasCoveringDimensionLT ↥(frontier V) n := by
  -- Apply the closed-pair partition theorem to `K` and the closed complement of `U`.
  obtain ⟨V, hVopen, hKV, hVclosure, hVfrontier⟩ :=
    existsOpenPartition_of_hasCoveringDimensionLE h hK hU.isClosed_compl
      hKU.disjoint_compl_right
  refine ⟨V, hVopen, hKV, ?_, hVfrontier⟩
  simpa only [compl_compl] using hVclosure

/-- Helper for Definition 50.8: finitely many locally controlled neighborhoods cover a closed
compact set while their union still has closure inside the prescribed ambient open set. -/
lemma existsFiniteLocalFrontierCover
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n)
    {K U : Set X} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (s : Finset K) (V : K → Set X),
      (∀ x, IsOpen (V x) ∧ x.1 ∈ V x ∧ closure (V x) ⊆ U ∧
        HasCoveringDimensionLT ↥(frontier (V x)) n) ∧
      K ⊆ ⋃ x ∈ s, V x ∧
      IsOpen (⋃ x ∈ s, V x) ∧
      closure (⋃ x ∈ s, V x) ⊆ U ∧
      frontier (⋃ x ∈ s, V x) ⊆ ⋃ x ∈ s, frontier (V x) := by
  classical
  -- Choose one controlled neighborhood for every point of the closed set.
  have hchoice (x : K) :
      ∃ V : Set X,
        IsOpen V ∧ x.1 ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n :=
    hlocal x.1 U (hKU x.2) hU
  choose V hVopen hxV hVclosure hVfrontier using hchoice
  -- Compactness reduces this point-indexed cover to finitely many chosen neighborhoods.
  have hKcover : K ⊆ ⋃ x : K, V x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨s, hscover⟩ := hK.isCompact.elim_finite_subcover V hVopen hKcover
  refine ⟨s, V, ?_, hscover, ?_, ?_, ?_⟩
  · intro x
    exact ⟨hVopen x, hxV x, hVclosure x, hVfrontier x⟩
  · exact isOpen_biUnion fun x _ ↦ hVopen x
  · -- Finite unions commute with closure, so each selected closure remains inside `U`.
    rw [Finset.closure_biUnion]
    exact Set.iUnion₂_subset fun x _ ↦ hVclosure x
  · -- The union frontier lies in the finite union of the selected controlled frontiers.
    exact frontier_biUnion_finset_subset s V

/-- Helper for Definition 50.8: an arbitrary open cover of a compact metrizable space admits a
finite indexed subcover together with a closure-controlled shrinking and explicit original-cover
parents, without assuming any dimension bound. -/
lemma existsFiniteIndexedShrinkingOfOpenCover
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
    (𝒜 : Set (Set X)) (h𝒜open : ∀ U ∈ 𝒜, IsOpen U) (h𝒜cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ (ι : Type u) (_ : Finite ι) (B C : ι → Opens X) (p : ι → 𝒜),
      IsOpenCover B ∧ IsOpenCover C ∧
        (∀ i, (B i : Set X) ⊆ p i) ∧
        ∀ i, closure (C i : Set X) ⊆ B i := by
  classical
  -- Compactness first selects finitely many members of the original cover itself.
  have hsubcover : Set.univ ⊆ ⋃ U : 𝒜, U.1 := by
    intro x _
    have hx : x ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ x
    obtain ⟨U, hU𝒜, hxU⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨U, hU𝒜⟩, hxU⟩
  obtain ⟨t, htcover⟩ := isCompact_univ.elim_finite_subcover
    (fun U : 𝒜 ↦ U.1) (fun U ↦ h𝒜open U.1 U.2) hsubcover
  -- Index the selected members and remember their tautological parents in the input cover.
  let ι := {U : 𝒜 // U ∈ t}
  letI : Finite ι := Finite.of_fintype ι
  let B : ι → Opens X := fun i ↦ ⟨i.1.1, h𝒜open i.1.1 i.1.2⟩
  let p : ι → 𝒜 := fun i ↦ i.1
  have hBcover : IsOpenCover B := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ U ∈ t, U.1 := htcover (Set.mem_univ x)
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨U, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hUt, hxU⟩ := hx
    exact ⟨⟨U, hUt⟩, hxU⟩
  -- Finite indexation makes the selected cover point-finite, so normality supplies a shrinking.
  have hBfinite : PointFinite (fun i ↦ (B i : Set X)) := by
    rw [pointFinite_iff]
    intro x
    exact Set.toFinite _
  obtain ⟨C, hCcover, hCclosure⟩ := hBcover.exists_shrinking hBfinite
  refine ⟨ι, inferInstance, B, C, p, hBcover, hCcover, ?_, hCclosure⟩
  intro i
  exact Set.Subset.rfl

/-- Helper for Definition 50.8: a finite linearly ordered open cover decomposes away from its
frontiers into pairwise disjoint open cores, each contained in its original member. -/
lemma existsPairwiseDisjointOrderedOpenCores
    {X ι : Type*} [TopologicalSpace X] [Finite ι] [LinearOrder ι]
    (V : ι → Opens X) (hVcover : IsOpenCover V) :
    ∃ D : ι → Set X,
      (∀ i, IsOpen (D i)) ∧
      (∀ i, D i ⊆ V i) ∧
      Pairwise (fun i j ↦ Disjoint (D i) (D j)) ∧
      (⋃ i, frontier (V i : Set X))ᶜ ⊆ ⋃ i, D i := by
  classical
  let D : ι → Set X := fun i ↦
    (V i : Set X) \ ⋃ j : {j : ι // j < i}, closure (V j.1 : Set X)
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · -- Earlier closures form a finite closed union, so removing them preserves openness.
    intro i
    exact (V i).2.sdiff <| isClosed_iUnion_of_finite fun j ↦ isClosed_closure
  · -- Every core is obtained by deleting points from its indexed cover member.
    intro i
    exact Set.sdiff_subset
  · -- The later core omits the closure of every earlier cover member.
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · refine Set.disjoint_left.mpr ?_
      intro x hxi hxj
      exact hxj.2 <| Set.mem_iUnion.mpr ⟨⟨i, hijlt⟩, subset_closure hxi.1⟩
    · refine Set.disjoint_left.mpr ?_
      intro x hxi hxj
      exact hxi.2 <| Set.mem_iUnion.mpr ⟨⟨j, hjilt⟩, subset_closure hxj.1⟩
  · -- Choose the least cover member containing the point; off all frontiers, no earlier closure
    -- can contain it, because closure minus frontier is the open set itself.
    intro x hxfrontier
    have hindicesNonempty : {i : ι | x ∈ V i}.Nonempty := by
      have hxcover : x ∈ ⋃ i, (V i : Set X) := hVcover.iSup_set_eq_univ.symm ▸ Set.mem_univ x
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcover
      exact ⟨i, hxi⟩
    obtain ⟨i, hxi, himin⟩ :=
      Set.exists_min_image {i : ι | x ∈ V i} (fun i ↦ i) (Set.toFinite _) hindicesNonempty
    refine Set.mem_iUnion.mpr ⟨i, hxi, ?_⟩
    intro hxEarlier
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxEarlier
    have hxnotFrontier : x ∉ frontier (V j.1 : Set X) := by
      intro hxjfrontier
      exact hxfrontier <| Set.mem_iUnion.mpr ⟨j.1, hxjfrontier⟩
    have hxjOpen : x ∈ V j.1 := by
      have hxInterior : x ∈ interior (V j.1 : Set X) := by
        rw [← closure_sdiff_frontier]
        exact ⟨hxj, hxnotFrontier⟩
      exact interior_subset hxInterior
    exact (not_lt_of_ge (himin j.1 hxjOpen)) j.2

/-- Helper for Definition 50.8: every finite indexed open cover decomposes away from its
frontiers into pairwise-disjoint open cores contained in the corresponding cover members. -/
lemma existsPairwiseDisjointOpenCores
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (V : ι → Opens X) (hVcover : IsOpenCover V) :
    ∃ D : ι → Set X,
      (∀ i, IsOpen (D i)) ∧ (∀ i, D i ⊆ V i) ∧
      Pairwise (fun i j ↦ Disjoint (D i) (D j)) ∧
      (⋃ i, frontier (V i : Set X))ᶜ ⊆ ⋃ i, D i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let W : Fin (Fintype.card ι) → Opens X := fun j ↦ V (e.symm j)
  have hWcover : IsOpenCover W := by
    apply IsOpenCover.of_sets
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hx : x ∈ ⋃ i, (V i : Set X) := hVcover.iSup_set_eq_univ.symm ▸ Set.mem_univ x
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e i, by simpa [W] using hxi⟩
  obtain ⟨D, hDopen, hDV, hDdisjoint, hDcover⟩ :=
    existsPairwiseDisjointOrderedOpenCores W hWcover
  let E : ι → Set X := fun i ↦ D (e i)
  refine ⟨E, fun i ↦ hDopen (e i), fun i ↦ ?_, ?_, ?_⟩
  · simpa [E, W] using hDV (e i)
  · intro i j hij
    exact hDdisjoint fun heij ↦ hij (e.injective heij)
  · intro x hx
    have hxW : x ∈ (⋃ j, frontier (W j : Set X))ᶜ := by
      intro hxfrontier
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxfrontier
      exact hx <| Set.mem_iUnion.mpr ⟨e.symm j, by simpa [W] using hxj⟩
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hDcover hxW)
    exact Set.mem_iUnion.mpr ⟨e.symm j, by simpa [E] using hxj⟩

/-- Helper for Definition 50.8: adjoining a pairwise-disjoint indexed family increases the order
of an existing indexed family by at most one. -/
lemma hasOrderLE_sum_of_pairwiseDisjoint
    {X I J : Type*} (E : I → Set X) (D : J → Set X) {q : ℕ}
    (hE : (Set.range E).HasOrderLE q)
    (hD : Pairwise fun i j ↦ Disjoint (D i) (D j)) :
    (Set.range (Sum.elim E D)).HasOrderLE (q + 1) := by
  -- Split the combined range into its two summands and bound their pointwise incidences.
  rw [Set.hasOrderLE_iff]
  intro x
  have hrange : Set.range (Sum.elim E D) = Set.range E ∪ Set.range D := by
    ext U
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Set.mem_union_left _ ⟨i, rfl⟩
      | inr j => exact Set.mem_union_right _ ⟨j, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [hrange]
  let S : Set (Set X) := {U ∈ Set.range E | x ∈ U}
  let T : Set (Set X) := {U ∈ Set.range D | x ∈ U}
  have hincidence : {U ∈ Set.range E ∪ Set.range D | x ∈ U} = S ∪ T := by
    ext U
    simp only [S, T, Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hincidence]
  apply (Set.encard_union_le S T).trans
  have hTsubsingleton : T.Subsingleton := by
    intro U hU V hV
    obtain ⟨i, rfl⟩ := hU.1
    obtain ⟨j, hji⟩ := hV.1
    subst V
    by_cases hij : i = j
    · simp only [hij]
    · exact (Set.disjoint_left.mp (hD hij) hU.2 hV.2).elim
  exact add_le_add (Set.hasOrderLE_iff.mp hE x)
    (Set.encard_le_one_iff_subsingleton.mpr hTsubsingleton)

/-- Helper for Definition 50.8: every controlled closed-pair partition yields the corresponding
covering-dimension bound on a compact metrizable space. -/
lemma hasCoveringDimensionLE_of_openPartitions
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (hpartition : ∀ K F : Set X, IsClosed K → IsClosed F → Disjoint K F →
      ∃ V : Set X,
        IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Fᶜ ∧
          HasCoveringDimensionLT ↥(frontier V) n) :
    HasCoveringDimensionLE X n := by
  classical
  -- Begin with a finite shrinking of the requested cover and separate each closed shrinking from
  -- the complement of its parent open set.
  rw [hasCoveringDimensionLE_iff_pointwise]
  intro 𝒜 h𝒜open h𝒜cover
  obtain ⟨ι, hιfinite, B, C, p, hBcover, hCcover, hBp, hCclosure⟩ :=
    existsFiniteIndexedShrinkingOfOpenCover 𝒜 h𝒜open h𝒜cover
  letI : Finite ι := hιfinite
  have hseparator (i : ι) :
      ∃ V : Set X,
        IsOpen V ∧ closure (C i : Set X) ⊆ V ∧ closure V ⊆ B i ∧
          HasCoveringDimensionLT ↥(frontier V) n := by
    simpa only [compl_compl] using
      hpartition (closure (C i : Set X)) (B i : Set X)ᶜ isClosed_closure
        (B i).2.isClosed_compl (hCclosure i).disjoint_compl_right
  choose V hVopen hCV hVclosure hVfrontier using hseparator
  let VO : ι → Opens X := fun i ↦ ⟨V i, hVopen i⟩
  have hVcover : IsOpenCover VO := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    have hxC : x ∈ ⋃ i, (C i : Set X) := hCcover.iSup_set_eq_univ.symm ▸ Set.mem_univ x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxC
    exact Set.mem_iUnion.mpr ⟨i, hCV i (subset_closure hxi)⟩
  obtain ⟨D, hDopen, hDV, hDdisjoint, hDcover⟩ :=
    existsPairwiseDisjointOpenCores VO hVcover
  -- The only points not covered by the disjoint cores lie in the finite union of controlled
  -- frontiers, which still has strict covering dimension below `n`.
  let L : Set X := ⋃ i, frontier (V i)
  have hLclosed : IsClosed L := isClosed_iUnion_of_finite fun _ ↦ isClosed_frontier
  have hLdim : HasCoveringDimensionLT L n :=
    hasCoveringDimensionLT_finiteUnionClosedSubtypes
      (fun i ↦ frontier (V i)) (fun _ ↦ isClosed_frontier) hVfrontier
  cases n with
  | zero =>
      have hLempty : IsEmpty L := hLdim
      have hDcoverUniv : ⋃ i, D i = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        have hxnotL : x ∉ L := by
          intro hx
          exact hLempty.false ⟨x, hx⟩
        exact hDcover hxnotL
      refine ⟨Set.range D, ?_, ?_, ?_⟩
      · rw [isOpenRefinement_iff]
        constructor
        · rw [isRefinement_iff]
          rintro U ⟨i, rfl⟩
          exact ⟨p i, (p i).2,
            (hDV i).trans (subset_closure.trans (hVclosure i) |>.trans (hBp i))⟩
        · rintro U ⟨i, rfl⟩
          exact hDopen i
      · rw [Set.sUnion_range]
        exact hDcoverUniv
      · have hDorder : (Set.range D).HasOrderLE 1 := by
          rw [Set.hasOrderLE_iff]
          intro x
          have hsubsingleton : {U ∈ Set.range D | x ∈ U}.Subsingleton := by
            intro U hU W hW
            obtain ⟨i, rfl⟩ := hU.1
            obtain ⟨j, hji⟩ := hW.1
            subst W
            by_cases hij : i = j
            · simp only [hij]
            · exact (Set.disjoint_left.mp (hDdisjoint hij) hU.2 hW.2).elim
          simpa using Set.encard_le_one_iff_subsingleton.mpr hsubsingleton
        exact Set.hasOrderLE_iff.mp hDorder
  | succ q =>
      -- Refine the traces of the original finite cover on the closed frontier locus, then swell
      -- its closed shrinking back into the ambient space without changing its nerve.
      let 𝒜L : Set (Set L) := Set.range fun i ↦ Subtype.val ⁻¹' (B i : Set X)
      letI : CompactSpace L := isCompact_iff_compactSpace.mp hLclosed.isCompact
      have h𝒜Lopen : ∀ U ∈ 𝒜L, IsOpen U := by
        rintro U ⟨i, rfl⟩
        exact (B i).2.preimage continuous_subtype_val
      have h𝒜Lcover : ⋃₀ 𝒜L = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        exact Set.mem_sUnion.mpr ⟨Subtype.val ⁻¹' (B (Classical.choose
          (Set.mem_iUnion.mp (hBcover.iSup_set_eq_univ.symm ▸ Set.mem_univ x.1))) : Set X),
          ⟨Classical.choose
            (Set.mem_iUnion.mp (hBcover.iSup_set_eq_univ.symm ▸ Set.mem_univ x.1)), rfl⟩,
          Classical.choose_spec
            (Set.mem_iUnion.mp (hBcover.iSup_set_eq_univ.symm ▸ Set.mem_univ x.1))⟩
      obtain ⟨κ, hκfinite, R, S, r, hRcover, hScover, hRorder, hRinjective,
          hRparent, hSclosure⟩ :=
        existsFiniteIndexedShrinkingRefinement hLdim 𝒜L h𝒜Lopen h𝒜Lcover
      letI : Finite κ := hκfinite
      have hrindex (j : κ) : ∃ i : ι, (r j : Set L) = Subtype.val ⁻¹' (B i : Set X) :=
        by
          have hj := (r j).2
          simp only [𝒜L, Set.mem_range] at hj
          obtain ⟨i, hi⟩ := hj
          exact ⟨i, hi.symm⟩
      choose a ha using hrindex
      have hRA : ∀ j, Subtype.val '' (R j : Set L) ⊆ (B (a j) : Set X) := by
        intro j x hx
        obtain ⟨z, hzR, rfl⟩ := hx
        have hzparent : z ∈ (r j : Set L) := hRparent j hzR
        rw [ha j] at hzparent
        exact hzparent
      obtain ⟨E, hEopen, hLE, hEclosure, hEorder⟩ :=
        existsAmbientOpenSwelling_of_closedSubtypeCover hLclosed R S hScover hRorder
          hRinjective hSclosure (fun j ↦ (B (a j) : Set X)) (fun j ↦ (B (a j)).2) hRA
      let F : Sum κ ι → Set X := Sum.elim E D
      refine ⟨Set.range F, ?_, ?_, ?_⟩
      · rw [isOpenRefinement_iff]
        constructor
        · rw [isRefinement_iff]
          rintro U ⟨j, rfl⟩
          cases j with
          | inl j =>
              exact ⟨p (a j), (p (a j)).2,
                subset_closure.trans (hEclosure j) |>.trans (hBp (a j))⟩
          | inr i =>
              exact ⟨p i, (p i).2,
                (hDV i).trans (subset_closure.trans (hVclosure i) |>.trans (hBp i))⟩
        · rintro U ⟨j, rfl⟩
          cases j with
          | inl j => exact hEopen j
          | inr i => exact hDopen i
      · rw [Set.sUnion_range]
        apply Set.eq_univ_of_forall
        intro x
        by_cases hxL : x ∈ L
        · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hLE hxL)
          exact Set.mem_iUnion.mpr ⟨Sum.inl j, hxj⟩
        · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hDcover hxL)
          exact Set.mem_iUnion.mpr ⟨Sum.inr i, hxi⟩
      · exact Set.hasOrderLE_iff.mp <|
          hasOrderLE_sum_of_pairwiseDisjoint E D hEorder hDdisjoint

/-- Helper for Definition 50.8: local frontier control produces a controlled partition between
any two disjoint closed subsets. -/
lemma existsOpenPartition_of_localFrontier
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n)
    {K F : Set X} (hK : IsClosed K) (hF : IsClosed F) (hKF : Disjoint K F) :
    ∃ V : Set X,
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Fᶜ ∧
        HasCoveringDimensionLT ↥(frontier V) n := by
  -- Select finitely many local neighborhoods around `K` inside the complement of `F`.
  classical
  obtain ⟨s, V, hV, hKcover, hopen, hclosure, hfrontier⟩ :=
    existsFiniteLocalFrontierCover hlocal hK hF.isOpen_compl hKF.subset_compl_right
  let ι := {x : K // x ∈ s}
  let Y : ι → Set X := fun i ↦ frontier (V i.1)
  have hYclosed : ∀ i, IsClosed (Y i) := fun _ ↦ isClosed_frontier
  have hYdim : ∀ i, HasCoveringDimensionLT (Y i) n := fun i ↦ (hV i.1).2.2.2
  have hunion : HasCoveringDimensionLT (⋃ i, Y i) n :=
    hasCoveringDimensionLT_finiteUnionClosedSubtypes Y hYclosed hYdim
  have hfrontierUnion : frontier (⋃ x ∈ s, V x) ⊆ ⋃ i, Y i := by
    intro x hx
    obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.mp (hfrontier hx)
    exact Set.mem_iUnion.mpr ⟨⟨y, hyS⟩, hxy⟩
  have hfrontierDim : HasCoveringDimensionLT ↥(frontier (⋃ x ∈ s, V x)) n :=
    hunion.closedSubset hfrontierUnion isClosed_frontier
  exact ⟨⋃ x ∈ s, V x, hopen, hKcover, hclosure, hfrontierDim⟩

/-- Helper for Definition 50.8: locally available neighborhoods with lower-dimensional
frontiers imply the corresponding covering-dimension bound. -/
lemma hasCoveringDimensionLE_of_local_frontier
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n) :
    HasCoveringDimensionLE X n := by
  -- Build the required closed-pair partitions from the local neighborhoods, then invoke the
  -- finite-cover partition characterization.
  apply hasCoveringDimensionLE_of_openPartitions
  intro K F hK hF hKF
  exact existsOpenPartition_of_localFrontier hlocal hK hF hKF

/-- Helper for Definition 50.8: a local supply of open neighborhoods with controlled frontiers
forms a topological basis. -/
lemma frontierControlledBasis_of_local_frontier
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (hlocal : ∀ x U, x ∈ U → IsOpen U →
      ∃ V : Set X,
        IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
          HasCoveringDimensionLT ↥(frontier V) n) :
    ∃ s : Set (Set X),
      IsTopologicalBasis s ∧ ∀ U ∈ s, HasCoveringDimensionLT ↥(frontier U) n := by
  -- Use all open sets with controlled frontier and verify the local basis criterion.
  let s : Set (Set X) :=
    {U | IsOpen U ∧ HasCoveringDimensionLT ↥(frontier U) n}
  have hs : IsTopologicalBasis s := by
    apply isTopologicalBasis_opens.isTopologicalBasis_of_exists_subset
    · intro U hUs
      exact hUs.1
    · intro U hU x hxU
      obtain ⟨V, hVopen, hxV, hVclosure, hVfrontier⟩ := hlocal x U hxU hU
      exact ⟨V, ⟨hVopen, hVfrontier⟩, hxV, subset_closure.trans hVclosure⟩
  refine ⟨s, hs, ?_⟩
  intro U hUs
  exact hUs.2

/-- Helper for Definition 50.8: a frontier-bounded basis gives the corresponding covering
dimension bound on a compact metrizable space. -/
lemma hasCoveringDimensionLE_of_basis_frontier
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (s : Set (Set X)) (hs : IsTopologicalBasis s)
    (hfrontier : ∀ U ∈ s, HasCoveringDimensionLT ↥(frontier U) n) :
    HasCoveringDimensionLE X n := by
  -- First shrink the requested neighborhood, then choose a basis member inside the shrink.
  apply hasCoveringDimensionLE_of_local_frontier
  intro x U hxU hU
  obtain ⟨W, hWopen, hxW, hWclosure⟩ :=
    normal_exists_closure_subset isClosed_singleton hU (Set.singleton_subset_iff.mpr hxU)
  obtain ⟨V, hVs, hxV, hVW⟩ := hs.exists_subset_of_mem_open (hxW rfl) hWopen
  refine ⟨V, hs.isOpen hVs, hxV, ?_, hfrontier V hVs⟩
  exact (closure_mono hVW).trans hWclosure

/-- Helper for Definition 50.8: a covering dimension bound on a compact metrizable space yields
a basis whose frontiers satisfy the preceding strict bound. -/
lemma exists_basis_frontier_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) :
    ∃ s : Set (Set X),
      IsTopologicalBasis s ∧ ∀ U ∈ s, HasCoveringDimensionLT ↥(frontier U) n := by
  -- Apply the separator theorem to singletons and package the resulting neighborhoods as a basis.
  apply frontierControlledBasis_of_local_frontier
  intro x U hxU hU
  obtain ⟨V, hVopen, hxV, hVclosure, hVfrontier⟩ :=
    exists_open_between_frontier_of_hasCoveringDimensionLE h isClosed_singleton hU
      (Set.singleton_subset_iff.mpr hxU)
  exact ⟨V, hVopen, hxV rfl, hVclosure, hVfrontier⟩

/-- Helper for Definition 50.8: strict small inductive and covering dimension bounds agree on
compact metrizable spaces. -/
lemma hasSmallInductiveDimensionLT_iff_hasCoveringDimensionLT
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] (k : ℕ) :
    HasSmallInductiveDimensionLT X k ↔ HasCoveringDimensionLT X k := by
  -- Induct on the strict bound, using emptiness at zero and the frontier-basis interface at
  -- successor bounds.
  induction k generalizing X with
  | zero =>
      rw [hasSmallInductiveDimensionLT_zero_iff, hasCoveringDimensionLT_zero_iff]
  | succ n ih =>
      constructor
      · intro hsmall
        cases hsmall with
        | succ _ s hs hfrontier =>
            apply hasCoveringDimensionLE_of_basis_frontier s hs
            intro U hU
            letI : CompactSpace ↥(frontier U) :=
              isCompact_iff_compactSpace.mp isClosed_frontier.isCompact
            exact (ih ↥(frontier U)).mp (hfrontier U hU)
      · intro hcover
        obtain ⟨s, hs, hfrontier⟩ := exists_basis_frontier_of_hasCoveringDimensionLE hcover
        refine .succ n s hs ?_
        intro U hU
        letI : CompactSpace ↥(frontier U) :=
          isCompact_iff_compactSpace.mp isClosed_frontier.isCompact
        exact (ih ↥(frontier U)).mpr (hfrontier U hU)

/-- Helper for Definition 50.8: the defining sets for the numerical small inductive and covering
dimensions coincide on compact metrizable spaces. -/
lemma smallInductiveDimension_definingSet_eq_coveringDimension_definingSet
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] :
    {d : WithBot ℕ∞ | ∀ k : ℕ, d < k → HasSmallInductiveDimensionLT X k} =
      {d : WithBot ℕ∞ | ∀ k : ℕ, d < k → HasCoveringDimensionLT X k} := by
  -- Compare membership pointwise, rewriting only the strict dimension predicate.
  ext d
  constructor
  · intro hd k hdk
    exact (hasSmallInductiveDimensionLT_iff_hasCoveringDimensionLT X k).mp (hd k hdk)
  · intro hd k hdk
    exact (hasSmallInductiveDimensionLT_iff_hasCoveringDimensionLT X k).mpr (hd k hdk)

/-- Definition 50.8 (4). On compact metrizable spaces, the small inductive dimension has the same
value as the covering dimension of Definition 50.3, including the value `⊥` for the empty space. -/
theorem smallInductiveDimension_eq_coveringDimension
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] :
    smallInductiveDimension X = coveringDimension X := by
  -- Both invariants are infima of the same set after replacing their equivalent strict bounds.
  rw [smallInductiveDimension, coveringDimension,
    smallInductiveDimension_definingSet_eq_coveringDimension_definingSet]

/-- On compact metrizable spaces, the natural-valued upper-bound predicates for small inductive
dimension and covering dimension agree. -/
theorem hasSmallInductiveDimensionLE_iff_hasCoveringDimensionLE
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] (n : ℕ) :
    HasSmallInductiveDimensionLE X n ↔ HasCoveringDimensionLE X n := by
  -- The non-strict predicates are the strict predicates at the common successor bound.
  exact hasSmallInductiveDimensionLT_iff_hasCoveringDimensionLT X (n + 1)
