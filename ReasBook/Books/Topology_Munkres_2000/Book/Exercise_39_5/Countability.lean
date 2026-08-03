module

public import Topology_Munkres_2000.Book.Definition_6_0_3.CountablyLocallyFinite

public section

universe u

/-- Helper for Exercise 39.5: a countable collection of subsets is sigma-locally finite. -/
theorem Set.Countable.countablyLocallyFinite {X : Type u} [TopologicalSpace X]
    {𝒜 : Set (Set X)} (h𝒜 : 𝒜.Countable) : 𝒜.CountablyLocallyFinite := by
  rw [Set.countablyLocallyFinite_iff]
  by_cases hnonempty : 𝒜.Nonempty
  · obtain ⟨f, hf⟩ := h𝒜.exists_eq_range hnonempty
    -- Enumerate the collection and use its singleton fibers as locally finite layers.
    refine ⟨fun n ↦ {f n}, ?_, ?_⟩
    · rw [hf]
      ext A
      simp
    · intro n
      exact locallyFinite_of_finite _
  · have hempty : 𝒜 = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    -- The empty collection is the union of constantly empty layers.
    refine ⟨fun _ ↦ ∅, ?_, ?_⟩
    · simp [hempty]
    · intro n
      exact locallyFinite_of_finite _

/-- Helper for Exercise 39.5: a locally finite collection in a second-countable space is
countable. -/
lemma Set.LocallyFinite.countable {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] {𝒜 : Set (Set X)} (h𝒜 : 𝒜.LocallyFinite) :
    𝒜.Countable := by
  let meeting : Set X → Set (Set X) :=
    fun U ↦ {A | A ∈ 𝒜 ∧ (A ∩ U).Nonempty}
  let goodBasis : Set (Set X) :=
    {U | U ∈ TopologicalSpace.countableBasis X ∧ (meeting U).Finite}
  have hgoodBasis : goodBasis.Countable := by
    apply (TopologicalSpace.countable_countableBasis X).mono
    intro U hU
    exact hU.1
  have hmeeting : ∀ U ∈ goodBasis, (meeting U).Countable := by
    intro U hU
    exact hU.2.countable
  have hcover : 𝒜 ⊆ {∅} ∪ ⋃ U ∈ goodBasis, meeting U := by
    intro A hA
    by_cases hAempty : A = ∅
    · left
      exact hAempty
    · obtain ⟨x, hxA⟩ := Set.nonempty_iff_ne_empty.mpr hAempty
      obtain ⟨V, hV, hfinite⟩ := Set.locallyFinite_iff.mp h𝒜 x
      obtain ⟨U, ⟨hUbasis, hxU⟩, hUV⟩ :=
        (TopologicalSpace.isBasis_countableBasis X).nhds_hasBasis.mem_iff.mp hV
      have hmeetingFinite : (meeting U).Finite := by
        apply hfinite.subset
        intro B hB
        exact ⟨hB.1, hB.2.mono (Set.inter_subset_inter_right B hUV)⟩
      have hUgood : U ∈ goodBasis := ⟨hUbasis, hmeetingFinite⟩
      -- The chosen basis neighborhood witnesses that `A` lies in a finite layer.
      right
      apply Set.mem_iUnion_of_mem U
      apply Set.mem_iUnion_of_mem hUgood
      exact ⟨hA, x, hxA, hxU⟩
  have hunion : (⋃ U ∈ goodBasis, meeting U).Countable :=
    hgoodBasis.biUnion hmeeting
  exact ((Set.countable_singleton ∅).union hunion).mono hcover

/-- Helper for Exercise 39.5: a sigma-locally finite collection of subsets of a
second-countable space is countable. -/
theorem Set.CountablyLocallyFinite.countable {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.CountablyLocallyFinite) : 𝒜.Countable := by
  rw [Set.countablyLocallyFinite_iff] at h𝒜
  obtain ⟨pieces, hcover, hfinite⟩ := h𝒜
  rw [hcover]
  exact Set.countable_iUnion fun n ↦ (hfinite n).countable
