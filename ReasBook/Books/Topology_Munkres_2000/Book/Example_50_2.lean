module

public import Topology_Munkres_2000.Book.Example_50_1
public import Mathlib.Topology.UnitInterval

public section

open Set
open scoped CoveringDimension

/-- The relative-open cover of `unitInterval` by `[0, 1)` and `(0, 1]`. -/
def unitIntervalEndpointCover : Set (Set unitInterval) :=
  {{x : unitInterval | (x : ℝ) < 1}, {x : unitInterval | 0 < (x : ℝ)}}

/-- Every member of `unitIntervalEndpointCover` is open. -/
theorem unitIntervalEndpointCover_isOpen :
    ∀ U ∈ unitIntervalEndpointCover, IsOpen U := by
  -- Each member is the inverse image of an open order relation under continuous maps.
  intro U hU
  rcases hU with hU | hU
  · rw [hU]
    exact isOpen_lt continuous_subtype_val continuous_const
  · rw [Set.mem_singleton_iff.mp hU]
    exact isOpen_lt continuous_const continuous_subtype_val

/-- The family `unitIntervalEndpointCover` covers `unitInterval`. -/
theorem sUnion_unitIntervalEndpointCover :
    ⋃₀ unitIntervalEndpointCover = Set.univ := by
  -- A point lies in the left member unless it is the right endpoint.
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    rcases lt_or_eq_of_le x.2.2 with hx | hx
    · exact ⟨{x : unitInterval | (x : ℝ) < 1}, Set.mem_insert_iff.mpr (Or.inl rfl), hx⟩
    · refine ⟨{x : unitInterval | 0 < (x : ℝ)}, Set.mem_insert_iff.mpr (Or.inr rfl), ?_⟩
      simpa only [Set.mem_setOf_eq, hx] using (zero_lt_one : (0 : ℝ) < 1)

/-- The closed unit interval has covering dimension at most `1`. -/
theorem unitInterval_hasCoveringDimensionLE_one :
    HasCoveringDimensionLE unitInterval 1 :=
  Set.real_hasCoveringDimensionLE_one unitInterval

/-- Helper for Example 50.2: a family of order at most one is pairwise disjoint. -/
private lemma pairwiseDisjoint_of_hasOrderLE_one {X : Type*} {𝒰 : Set (Set X)}
    (horder : 𝒰.HasOrderLE 1) : 𝒰.PairwiseDisjoint id := by
  -- Two members meeting at a point must be the unique member through that point.
  intro U hU V hV hUV
  change Disjoint U V
  rw [Set.disjoint_left]
  intro z hzU hzV
  have hzorder := Set.hasOrderLE_iff.mp horder z
  have hunique := Set.encard_le_one_iff.mp hzorder
  have hUV_eq : U = V := hunique U V ⟨hU, hzU⟩ ⟨hV, hzV⟩
  exact hUV hUV_eq

/-- Helper for Example 50.2: each member of an open order-one cover is clopen. -/
private lemma isClopen_of_mem_hasOrderLE_one_openCover
    {X : Type*} [TopologicalSpace X] {𝒰 : Set (Set X)}
    (hopen : ∀ V ∈ 𝒰, IsOpen V) (hcover : ⋃₀ 𝒰 = Set.univ)
    (horder : 𝒰.HasOrderLE 1) {U : Set X} (hU : U ∈ 𝒰) : IsClopen U := by
  -- The complement of `U` is exactly the union of the other cover members.
  have hcompl : Uᶜ = ⋃₀ (𝒰 \ {U}) := by
    ext z
    constructor
    · intro hz
      have hzuniv : z ∈ Set.univ := Set.mem_univ z
      rw [← hcover] at hzuniv
      obtain ⟨V, hV, hzV⟩ := hzuniv
      refine ⟨V, ⟨hV, ?_⟩, hzV⟩
      intro hVU
      exact hz (hVU ▸ hzV)
    · rintro ⟨V, ⟨hV, hVU⟩, hzV⟩
      intro hzU
      have hVU_ne : V ≠ U := by
        simpa only [Set.mem_singleton_iff] using hVU
      have hdisjoint := pairwiseDisjoint_of_hasOrderLE_one horder hU hV hVU_ne.symm
      exact Set.disjoint_left.mp hdisjoint hzU hzV
  constructor
  · -- Openness of the complementary union proves that `U` is closed.
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_sUnion fun V hV ↦ hopen V hV.1
  · exact hopen U hU

/-- Every open cover of `unitInterval` refining the endpoint cover has a point
belonging to at least two members. -/
theorem unitInterval_endpointCover_refinement_multiplicity_ge_two
    (ℬ : Set (Set unitInterval))
    (h_refinement : IsOpenRefinement ℬ unitIntervalEndpointCover)
    (h_cover : ⋃₀ ℬ = Set.univ) :
    ∃ x : unitInterval, 2 ≤ Set.encard {U ∈ ℬ | x ∈ U} := by
  -- If no point has multiplicity two, the refinement has order at most one.
  by_contra hmultiplicity
  have horder : ℬ.HasOrderLE 1 := by
    rw [Set.hasOrderLE_iff]
    intro x
    have hxlt : Set.encard {U ∈ ℬ | x ∈ U} < 2 :=
      lt_of_not_ge fun hx ↦ hmultiplicity ⟨x, hx⟩
    have hxle : Set.encard {U ∈ ℬ | x ∈ U} ≤ (1 : ℕ∞) :=
      ENat.lt_two_iff.mp hxlt
    simpa using hxle
  -- Choose a refinement member through the left endpoint.
  have hzero_cover : (0 : unitInterval) ∈ ⋃₀ ℬ := by
    rw [h_cover]
    exact Set.mem_univ 0
  obtain ⟨U, hU, hzeroU⟩ := hzero_cover
  -- Refinement into the endpoint cover forces this member to omit the right endpoint.
  have hone_not_mem : (1 : unitInterval) ∉ U := by
    obtain ⟨A, hA, hUA⟩ := h_refinement.toIsRefinement.subset_of_mem hU
    simp only [unitIntervalEndpointCover, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hA
    rcases hA with hA | hA
    · rw [hA] at hUA
      intro honeU
      have hone_lt := hUA honeU
      norm_num at hone_lt
    · rw [hA] at hUA
      have hzero_pos := hUA hzeroU
      norm_num at hzero_pos
  -- The order-one member is clopen, so connectedness makes it all of the interval.
  have hU_clopen := isClopen_of_mem_hasOrderLE_one_openCover
    (fun V hV ↦ h_refinement.isOpen_of_mem hV) h_cover horder hU
  have hU_univ : U = Set.univ := hU_clopen.eq_univ ⟨0, hzeroU⟩
  apply hone_not_mem
  rw [hU_univ]
  exact Set.mem_univ 1

/-- Example 50.2. The closed unit interval has topological dimension `1`. -/
theorem unitInterval_coveringDimension : dim unitInterval = 1 := by
  -- The real-subspace theorem gives the upper bound; exclude a strict bound below one.
  apply le_antisymm
  · exact (coveringDimension_le_iff unitInterval 1).mpr
      unitInterval_hasCoveringDimensionLE_one
  · apply le_of_not_gt
    intro hdim
    have hdim_succ :
        dim unitInterval < ((0 + 1 : ℕ) : WithBot ℕ∞) := by
      simpa using hdim
    have hdim_zero : dim unitInterval ≤ (0 : WithBot ℕ∞) :=
      ENat.WithBot.lt_add_one_iff.mp hdim_succ
    have hbound : HasCoveringDimensionLE unitInterval 0 :=
      (coveringDimension_le_iff unitInterval 0).mp hdim_zero
    -- A zero-dimensional refinement contradicts the endpoint-cover obstruction.
    obtain ⟨ℬ, h_refinement, h_cover, horder⟩ :=
      hbound unitIntervalEndpointCover unitIntervalEndpointCover_isOpen
        sUnion_unitIntervalEndpointCover
    obtain ⟨x, hx⟩ :=
      unitInterval_endpointCover_refinement_multiplicity_ge_two ℬ h_refinement h_cover
    have hpoint_le_one : Set.encard {U ∈ ℬ | x ∈ U} ≤ 1 := by
      simpa using Set.hasOrderLE_iff.mp horder x
    have htwo_le_one : (2 : ℕ∞) ≤ 1 := hx.trans hpoint_le_one
    norm_num at htwo_le_one


end
