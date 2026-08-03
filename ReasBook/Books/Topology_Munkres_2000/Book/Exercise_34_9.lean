module

public import Mathlib.Topology.Metrizable.Urysohn

public section

universe u

namespace TopologicalSpace

/-- Helper for Exercise 34.9: in a two-set cover, removing one set from the other gives
the complement of the removed set. -/
private lemma sdiff_eq_compl_of_union_eq_univ {X : Type*} {s t : Set X}
    (hcover : s ∪ t = Set.univ) : s \ t = tᶜ := by
  -- The cover supplies membership in `s` whenever a point is outside `t`.
  ext x
  constructor
  · exact fun hx ↦ hx.2
  · intro hxt
    have hxcover : x ∈ s ∪ t := by
      rw [hcover]
      exact Set.mem_univ x
    exact ⟨hxcover.resolve_right hxt, hxt⟩

/-- Helper for Exercise 34.9: ambient open lifts of a subtype basis still restrict to a
topological basis. -/
private lemma IsTopologicalBasis.restrict_of_open_lifts {X : Type*} [TopologicalSpace X]
    {s : Set X} {b : Set (Set s)} {A : Set (Set X)} (hb : IsTopologicalBasis b)
    (hAopen : ∀ U ∈ A, IsOpen U)
    (hlift : ∀ V ∈ b, ∃ U ∈ A, ((↑) : s → X) ⁻¹' U = V) :
    IsTopologicalBasis ((fun U : Set X ↦ ((↑) : s → X) ⁻¹' U) '' A) := by
  -- Every restricted ambient member is open in the subtype topology.
  refine hb.of_isOpen_of_subset ?_ ?_
  · rintro _ ⟨U, hUA, rfl⟩
    exact (hAopen U hUA).preimage continuous_subtype_val
  · intro V hVb
    obtain ⟨U, hUA, hUV⟩ := hlift V hVb
    exact ⟨U, hUA, hUV⟩

/-- Helper for Exercise 34.9: finite intersections of ambient open sets form a basis when
their restrictions are bases on two closed pieces covering the space. -/
private lemma isTopologicalBasis_finiteInter_of_closedCover {X : Type*} [TopologicalSpace X]
    {s t : Set X} {A : Set (Set X)} (hcover : s ∪ t = Set.univ)
    (hAopen : ∀ U ∈ A, IsOpen U)
    (hsbasis : IsTopologicalBasis ((fun U : Set X ↦ ((↑) : s → X) ⁻¹' U) '' A))
    (htbasis : IsTopologicalBasis ((fun U : Set X ↦ ((↑) : t → X) ⁻¹' U) '' A))
    (hst : s \ t ∈ A) (hts : t \ s ∈ A) :
    IsTopologicalBasis
      ((fun F : Set (Set X) ↦ ⋂₀ F) '' {F : Set (Set X) | F.Finite ∧ F ⊆ A}) := by
  -- Finite intersections of members of `A` are open.
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨F, ⟨hFfinite, hFA⟩, rfl⟩
    exact hFfinite.isOpen_sInter fun U hUF ↦ hAopen U (hFA hUF)
  · intro x U hxU hUopen
    have hxcover : x ∈ s ∪ t := by
      rw [hcover]
      exact Set.mem_univ x
    by_cases hxs : x ∈ s
    · obtain ⟨Us, ⟨Us', hUsA, rfl⟩, hxsUs, hUsU⟩ :=
        hsbasis.exists_subset_of_mem_open (a := ⟨x, hxs⟩) hxU
          (hUopen.preimage continuous_subtype_val)
      by_cases hxt : x ∈ t
      · obtain ⟨Ut, ⟨Ut', hUtA, rfl⟩, hxtUt, hUtU⟩ :=
          htbasis.exists_subset_of_mem_open (a := ⟨x, hxt⟩) hxU
            (hUopen.preimage continuous_subtype_val)
        -- At an overlap point, intersect one lifted basis neighborhood from each piece.
        refine ⟨Us' ∩ Ut', ⟨{Us', Ut'}, ?_, Set.sInter_pair Us' Ut'⟩, ?_, ?_⟩
        · exact ⟨by simp, Set.pair_subset hUsA hUtA⟩
        · exact ⟨hxsUs, hxtUt⟩
        · intro y hy
          have hycover : y ∈ s ∪ t := by
            rw [hcover]
            exact Set.mem_univ y
          rcases hycover with hys | hyt
          · have hysUs : (⟨y, hys⟩ : s) ∈ ((↑) : s → X) ⁻¹' Us' := hy.1
            exact hUsU hysUs
          · have hytUt : (⟨y, hyt⟩ : t) ∈ ((↑) : t → X) ⁻¹' Ut' := hy.2
            exact hUtU hytUt
      · -- Off the other piece, intersect with the open difference `s \ t`.
        refine ⟨Us' ∩ (s \ t), ⟨{Us', s \ t}, ?_, Set.sInter_pair Us' (s \ t)⟩, ?_, ?_⟩
        · exact ⟨by simp, Set.pair_subset hUsA hst⟩
        · exact ⟨hxsUs, hxs, hxt⟩
        · intro y hy
          have hysUs : (⟨y, hy.2.1⟩ : s) ∈ ((↑) : s → X) ⁻¹' Us' := hy.1
          exact hUsU hysUs
    · have hxt : x ∈ t := hxcover.resolve_left hxs
      obtain ⟨Ut, ⟨Ut', hUtA, rfl⟩, hxtUt, hUtU⟩ :=
        htbasis.exists_subset_of_mem_open (a := ⟨x, hxt⟩) hxU
          (hUopen.preimage continuous_subtype_val)
      -- The remaining case is symmetric and uses `t \ s`.
      refine ⟨Ut' ∩ (t \ s), ⟨{Ut', t \ s}, ?_, Set.sInter_pair Ut' (t \ s)⟩, ?_, ?_⟩
      · exact ⟨by simp, Set.pair_subset hUtA hts⟩
      · exact ⟨hxtUt, hxt, hxs⟩
      · intro y hy
        have hytUt : (⟨y, hy.2.1⟩ : t) ∈ ((↑) : t → X) ⁻¹' Ut' := hy.1
        exact hUtU hytUt

/-- Exercise 34.9: A compact Hausdorff space covered by two closed metrizable subspaces is
metrizable. -/
theorem metrizableSpace_of_isClosed_union {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {X₁ X₂ : Set X} (hX₁ : IsClosed X₁) (hX₂ : IsClosed X₂)
    (hcover : X₁ ∪ X₂ = Set.univ) [MetrizableSpace X₁] [MetrizableSpace X₂] :
    MetrizableSpace X := by
  -- The main proof constructs a countable ambient family and glues its restricted bases.
  classical
  letI : CompactSpace X₁ := isCompact_iff_compactSpace.mp hX₁.isCompact
  letI : CompactSpace X₂ := isCompact_iff_compactSpace.mp hX₂.isCompact
  letI : SecondCountableTopology X₁ := inferInstance
  letI : SecondCountableTopology X₂ := inferInstance
  have hlift₁ : ∀ V : countableBasis X₁, ∃ U : Set X,
      IsOpen U ∧ ((↑) : X₁ → X) ⁻¹' U = V := by
    intro V
    exact isOpen_induced_iff.mp (isOpen_of_mem_countableBasis V.property)
  have hlift₂ : ∀ V : countableBasis X₂, ∃ U : Set X,
      IsOpen U ∧ ((↑) : X₂ → X) ⁻¹' U = V := by
    intro V
    exact isOpen_induced_iff.mp (isOpen_of_mem_countableBasis V.property)
  choose lift₁ hlift₁open hlift₁eq using hlift₁
  choose lift₂ hlift₂open hlift₂eq using hlift₂
  let A : Set (Set X) :=
    Set.range lift₁ ∪ Set.range lift₂ ∪ {X₁ \ X₂, X₂ \ X₁}
  have hAopen : ∀ U ∈ A, IsOpen U := by
    intro U hUA
    rcases hUA with (⟨V, rfl⟩ | ⟨V, rfl⟩) | hUdiff
    · exact hlift₁open V
    · exact hlift₂open V
    · rcases hUdiff with rfl | rfl
      · rw [sdiff_eq_compl_of_union_eq_univ hcover]
        exact hX₂.isOpen_compl
      · rw [sdiff_eq_compl_of_union_eq_univ (s := X₂) (t := X₁)]
        · exact hX₁.isOpen_compl
        · simpa [Set.union_comm] using hcover
  have hX₁basis :
      IsTopologicalBasis ((fun U : Set X ↦ ((↑) : X₁ → X) ⁻¹' U) '' A) := by
    -- Each canonical countable basis member has its chosen ambient representative in `A`.
    refine (isBasis_countableBasis X₁).restrict_of_open_lifts hAopen ?_
    intro V hV
    let V' : countableBasis X₁ := ⟨V, hV⟩
    refine ⟨lift₁ V', ?_, hlift₁eq V'⟩
    exact Or.inl (Or.inl (Set.mem_range_self V'))
  have hX₂basis :
      IsTopologicalBasis ((fun U : Set X ↦ ((↑) : X₂ → X) ⁻¹' U) '' A) := by
    -- The second piece is handled by the symmetric family of chosen lifts.
    refine (isBasis_countableBasis X₂).restrict_of_open_lifts hAopen ?_
    intro V hV
    let V' : countableBasis X₂ := ⟨V, hV⟩
    refine ⟨lift₂ V', ?_, hlift₂eq V'⟩
    exact Or.inl (Or.inr (Set.mem_range_self V'))
  have hfiniteBasis :
      IsTopologicalBasis
        ((fun F : Set (Set X) ↦ ⋂₀ F) '' {F : Set (Set X) | F.Finite ∧ F ⊆ A}) := by
    -- The two restricted bases glue because the family contains both exclusive regions.
    refine isTopologicalBasis_finiteInter_of_closedCover hcover hAopen hX₁basis hX₂basis ?_ ?_
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hAcount : A.Countable := by
    -- Both lift families are countable ranges, and only two extra sets are added.
    exact ((Set.countable_range lift₁).union (Set.countable_range lift₂)).union (by simp)
  have hfiniteCount :
      ((fun F : Set (Set X) ↦ ⋂₀ F) '' {F : Set (Set X) | F.Finite ∧ F ⊆ A}).Countable := by
    exact (Set.countable_setOf_finite_subset hAcount).image _
  letI : SecondCountableTopology X := hfiniteBasis.secondCountableTopology hfiniteCount
  -- Compact Hausdorff spaces are T₃, so Urysohn metrization finishes the proof.
  exact inferInstance

end TopologicalSpace

end
