module

public import Topology_Munkres_2000.Book.Lemma_41_3

public section

universe u v

namespace ParacompactSpace

/-- Helper for Exercise 41.7: a locally finite family in a closed subspace remains
locally finite after taking its images in the ambient space. -/
lemma _root_.LocallyFinite.imageSubtypeVal_of_isClosed
    {X : Type u} [TopologicalSpace X]
    {s : Set X} (hs : IsClosed s) {κ : Type v} {f : κ → Set s}
    (hf : LocallyFinite f) :
    LocallyFinite (fun k ↦ Subtype.val '' f k) := by
  -- Inside the closed set, lift a witnessing subtype neighborhood to the ambient space.
  intro x
  by_cases hx : x ∈ s
  · obtain ⟨t, ht_nhds, ht_finite⟩ := hf ⟨x, hx⟩
    obtain ⟨w, hw_nhds, hwt⟩ := (mem_nhds_subtype s ⟨x, hx⟩ t).mp ht_nhds
    refine ⟨w, hw_nhds, ht_finite.subset ?_⟩
    intro k hk
    obtain ⟨y, ⟨z, hzf, hzy⟩, hyw⟩ := hk
    have hzw : z.1 ∈ w := by
      rw [hzy]
      exact hyw
    exact ⟨z, hzf, hwt hzw⟩
  · -- Outside the closed set, its open complement meets none of the image sets.
    refine ⟨sᶜ, hs.isOpen_compl.mem_nhds hx, Set.finite_empty.subset ?_⟩
    intro k hk
    obtain ⟨y, ⟨z, _, hzy⟩, hy_compl⟩ := hk
    exact (hy_compl (hzy ▸ z.property)).elim

/-- Helper for Exercise 41.7: dependent locally finite families subordinate to a
locally finite outer family combine to a locally finite Sigma-indexed family. -/
lemma _root_.LocallyFinite.sigma_of_subset {X : Type u} [TopologicalSpace X]
    {ι : Type v} {κ : ι → Type*} {s : ι → Set X}
    {t : ∀ i, κ i → Set X} (hs : LocallyFinite s)
    (ht : ∀ i, LocallyFinite (t i)) (hsub : ∀ i k, t i k ⊆ s i) :
    LocallyFinite (fun q : Σ i, κ i ↦ t q.1 q.2) := by
  -- Restrict first to the finitely many outer indices visible near the point.
  intro x
  obtain ⟨w, hw_nhds, hw_finite⟩ := hs x
  choose v hv_nhds hv_finite using fun i ↦ ht i x
  let active : Set ι := {i | (s i ∩ w).Nonempty}
  have hactive : active.Finite := hw_finite
  letI : Finite active := Set.finite_coe_iff.mpr hactive
  let neighborhood : Set X := w ∩ ⋂ i : active, v i
  have hneighborhood : neighborhood ∈ nhds x := by
    exact Filter.inter_mem hw_nhds (Filter.iInter_mem.2 fun i ↦ hv_nhds i)
  let controlled : Set (Σ i, κ i) :=
    ⋃ i : active, Sigma.mk i.1 '' {k | (t i.1 k ∩ v i.1).Nonempty}
  have hcontrolled : controlled.Finite := by
    apply Set.finite_iUnion
    intro i
    exact (hv_finite i.1).image (Sigma.mk i.1)
  refine ⟨neighborhood, hneighborhood, hcontrolled.subset ?_⟩
  intro q hq
  obtain ⟨y, hyq, hy_neighborhood⟩ := hq
  have hq_active : q.1 ∈ active := by
    exact ⟨y, hsub q.1 q.2 hyq, hy_neighborhood.1⟩
  let i : active := ⟨q.1, hq_active⟩
  refine Set.mem_iUnion_of_mem i ?_
  refine ⟨q.2, ?_, rfl⟩
  exact ⟨y, hyq, Set.mem_iInter.mp hy_neighborhood.2 i⟩

/-- Helper for Exercise 41.7: an ambiently closed subset of a paracompact
subspace is itself paracompact. -/
lemma ofIsClosedSubset {X : Type u} [TopologicalSpace X] {p s : Set X}
    (hp : IsClosed p) (hps : p ⊆ s) [ParacompactSpace s] : ParacompactSpace p := by
  -- View `p` as a closed subspace of `s` and use preservation by closed embeddings.
  have hp_relative : IsClosed ((Subtype.val : s → X) ⁻¹' p) :=
    hp.preimage continuous_subtype_val
  exact (Topology.IsClosedEmbedding.inclusion hps hp_relative).paracompactSpace

/-- Helper for Exercise 41.7: a regular space covered by a locally finite closed
family of paracompact subspaces is paracompact. -/
lemma ofLocallyFiniteClosedCover {X : Type u} [TopologicalSpace X] [T3Space X]
    {ι : Type v} (s : ι → Set X) (h_closed : ∀ i, IsClosed (s i))
    [∀ i, ParacompactSpace (s i)] (h_finite : LocallyFinite s)
    (h_cover : ⋃ i, s i = Set.univ) : ParacompactSpace X := by
  -- Lemma 41.3 reduces the goal to constructing an arbitrary locally finite refinement.
  apply ((_root_.openCoverRefinement_tfae X).out 1 3).mp
  intro 𝒜 h𝒜_open h𝒜_cover
  classical
  have h_restricted_cover (i : ι) :
      ⋃ U : 𝒜, (Subtype.val : s i → X) ⁻¹' U.1 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx_union : x.1 ∈ ⋃₀ 𝒜 := by
      rw [h𝒜_cover]
      exact Set.mem_univ x.1
    obtain ⟨U, hU𝒜, hxU⟩ := Set.mem_sUnion.mp hx_union
    exact Set.mem_iUnion_of_mem ⟨U, hU𝒜⟩ hxU
  choose β t ht_open ht_cover ht_finite ht_refines using fun i ↦
    ParacompactSpace.locallyFinite_refinement 𝒜
      (fun U ↦ (Subtype.val : s i → X) ⁻¹' U.1)
      (fun U ↦ (h𝒜_open U U.property).preimage continuous_subtype_val)
      (h_restricted_cover i)
  let ambient : (Σ i, β i) → Set X :=
    fun q ↦ Subtype.val '' t q.1 q.2
  have h_ambient_finite : LocallyFinite ambient := by
    unfold ambient
    refine LocallyFinite.sigma_of_subset
      (t := fun i k ↦ Subtype.val '' t i k) h_finite ?_ ?_
    · intro i
      exact LocallyFinite.imageSubtypeVal_of_isClosed (h_closed i) (ht_finite i)
    · intro i k x hx
      obtain ⟨y, _, hxy⟩ := hx
      exact hxy ▸ y.property
  have h_ambient_refines : IsRefinement (Set.range ambient) 𝒜 := by
    rw [isRefinement_iff]
    rintro B ⟨q, rfl⟩
    obtain ⟨U, hsubset⟩ := ht_refines q.1 q.2
    refine ⟨U.1, U.property, ?_⟩
    intro x hx
    obtain ⟨y, hyt, hxy⟩ := hx
    exact hxy ▸ hsubset hyt
  have h_ambient_cover : ⋃₀ (Set.range ambient) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx_outer : x ∈ ⋃ i, s i := by
      rw [h_cover]
      exact Set.mem_univ x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx_outer
    let y : s i := ⟨x, hxi⟩
    have hy_inner : y ∈ ⋃ k, t i k := by
      rw [ht_cover i]
      exact Set.mem_univ y
    obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hy_inner
    have hset : ambient ⟨i, k⟩ ∈ Set.range ambient := ⟨⟨i, k⟩, rfl⟩
    apply Set.mem_sUnion_of_mem _ hset
    unfold ambient
    exact ⟨y, hyk, rfl⟩
  exact ⟨Set.range ambient, h_ambient_refines, h_ambient_cover,
    h_ambient_finite.on_range⟩

/-- Helper for Exercise 41.7: a countable closed family whose interiors cover
admits a locally finite closed subordinate cover. -/
lemma _root_.Set.existsLocallyFiniteClosedRefinementOfCountableInteriorCover
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Countable ι]
    (s : ι → Set X) (h_closed : ∀ i, IsClosed (s i))
    (h_interior_cover : ⋃ i, interior (s i) = Set.univ) :
    ∃ p : ι → Set X, (∀ i, IsClosed (p i)) ∧ (∀ i, p i ⊆ s i) ∧
      LocallyFinite p ∧ ⋃ i, p i = Set.univ := by
  -- Rank the countable family and delete every strictly earlier interior from each layer.
  classical
  obtain ⟨rank, hrank⟩ := Countable.exists_injective_nat ι
  let p : ι → Set X := fun i ↦
    s i \ ⋃ j, ⋃ (_ : rank j < rank i), interior (s j)
  have hp_closed : ∀ i, IsClosed (p i) := by
    intro i
    exact (h_closed i).sdiff (isOpen_iUnion fun j ↦
      isOpen_iUnion fun _ ↦ isOpen_interior)
  have hp_subset : ∀ i, p i ⊆ s i := by
    intro i
    exact Set.sdiff_subset
  have hp_cover : ⋃ i, p i = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx_union : x ∈ ⋃ i, interior (s i) := by
      rw [h_interior_cover]
      exact Set.mem_univ x
    obtain ⟨i₀, hxi₀⟩ := Set.mem_iUnion.mp hx_union
    have hexists : ∃ n, ∃ i, rank i = n ∧ x ∈ interior (s i) :=
      ⟨rank i₀, i₀, rfl, hxi₀⟩
    let n := Nat.find hexists
    obtain ⟨i, hirank, hxi⟩ := Nat.find_spec hexists
    apply Set.mem_iUnion_of_mem i
    refine ⟨interior_subset hxi, ?_⟩
    intro hx_earlier
    obtain ⟨j, hx_earlier⟩ := Set.mem_iUnion.mp hx_earlier
    obtain ⟨hji, hxj⟩ := Set.mem_iUnion.mp hx_earlier
    have hminimal : n ≤ rank j :=
      Nat.find_min' hexists ⟨j, rfl, hxj⟩
    rw [hirank] at hji
    exact (Nat.not_lt_of_ge hminimal) hji
  have hp_finite : LocallyFinite p := by
    -- Any chosen covering interior meets only layers of no larger rank.
    intro x
    have hx_union : x ∈ ⋃ i, interior (s i) := by
      rw [h_interior_cover]
      exact Set.mem_univ x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx_union
    have hbounded : (rank ⁻¹' Set.Iic (rank i)).Finite :=
      (Set.finite_Iic (rank i)).preimage hrank.injOn
    refine ⟨interior (s i), isOpen_interior.mem_nhds hxi, hbounded.subset ?_⟩
    intro j hj
    by_contra hnot
    have hij : rank i < rank j := Nat.lt_of_not_ge hnot
    obtain ⟨y, hyp, hyi⟩ := hj
    exact hyp.2 (Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem hij hyi))
  exact ⟨p, hp_closed, hp_subset, hp_finite, hp_cover⟩

/-- Exercise 41.7 (1). A space covered by finitely many closed paracompact
subspaces of a regular space is paracompact. -/
theorem ofFiniteClosedCover {X : Type u} [TopologicalSpace X] [T3Space X]
    {ι : Type v} [Finite ι]
    (s : ι → Set X) (h_closed : ∀ i, IsClosed (s i))
    [∀ i, ParacompactSpace (s i)] (h_cover : ⋃ i, s i = Set.univ) :
    ParacompactSpace X := by
  -- A finite family is locally finite, so the closed-cover gluing lemma applies directly.
  exact ofLocallyFiniteClosedCover s h_closed (locallyFinite_of_finite s) h_cover

/-- Exercise 41.7 (2). A regular space with a countable closed paracompact family
whose interiors cover the space is paracompact. The interior-cover condition already
implies that the underlying closed subspaces cover the space. -/
theorem ofCountableClosedCoverWithInteriorCover {X : Type u} [TopologicalSpace X]
    [T3Space X] {ι : Type v} [Countable ι] (s : ι → Set X)
    (h_closed : ∀ i, IsClosed (s i)) [∀ i, ParacompactSpace (s i)]
    (h_interior_cover : ⋃ i, interior (s i) = Set.univ) : ParacompactSpace X := by
  -- Replace the countable family by its locally finite rank-trimmed closed layers.
  obtain ⟨p, hp_closed, hp_subset, hp_finite, hp_cover⟩ :=
    Set.existsLocallyFiniteClosedRefinementOfCountableInteriorCover
      s h_closed h_interior_cover
  letI : ∀ i, ParacompactSpace (p i) := fun i ↦
    ofIsClosedSubset (hp_closed i) (hp_subset i)
  exact ofLocallyFiniteClosedCover p hp_closed hp_finite hp_cover

end ParacompactSpace
