module

public import Topology_Munkres_2000.Book.Definition_6_0_1.LocallyFinite

public section

/-- The collection of all singleton subsets of `ℕ`. -/
def naturalSingletonCollection : Set (Set ℕ) :=
  Set.range (fun n : ℕ ↦ ({n} : Set ℕ))

/-- Helper for Exercise 39.3: Every nonempty subset of an indiscrete space is dense. -/
lemma closure_eq_univ_of_nonempty_of_indiscrete {X : Type*} [TopologicalSpace X]
    [IndiscreteTopology X] {s : Set X} (hs : s.Nonempty) : closure s = Set.univ := by
  -- Every open neighborhood of a point is the whole indiscrete space, hence meets `s`.
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  have hUuniv : U = Set.univ := by
    rw [IndiscreteTopology.eq_top X] at hU
    rw [TopologicalSpace.isOpen_top_iff] at hU
    exact hU.resolve_left fun hUempty ↦ by
      rw [hUempty] at hxU
      exact hxU
  rw [hUuniv, Set.univ_inter]
  exact hs

/-- The singleton collection is not locally finite on indiscrete `ℕ`. -/
theorem not_locallyFinite_naturalSingletonCollection [TopologicalSpace ℕ]
    [IndiscreteTopology ℕ] : ¬ naturalSingletonCollection.LocallyFinite := by
  -- A locally finite neighborhood of `0` would have to be `univ` and meet every singleton.
  intro hlocal
  rw [Set.locallyFinite_iff] at hlocal
  obtain ⟨U, hU, hfinite⟩ := hlocal 0
  have hUuniv : U = Set.univ := by
    rw [IndiscreteTopology.nhds_eq] at hU
    exact Filter.mem_top.mp hU
  have hsubset : naturalSingletonCollection ⊆
      {A | A ∈ naturalSingletonCollection ∧ (A ∩ U).Nonempty} := by
    intro A hA
    refine ⟨hA, ?_⟩
    rw [hUuniv, Set.inter_univ]
    obtain ⟨n, rfl⟩ := hA
    exact Set.singleton_nonempty n
  -- This contradicts the infinite injective range of the singleton map.
  exact Set.infinite_range_of_injective Set.singleton_injective (hfinite.subset hsubset)

/-- The collection of distinct closures of the singleton collection is locally finite on
indiscrete `ℕ`. -/
theorem locallyFinite_closure_naturalSingletonCollection [TopologicalSpace ℕ]
    [IndiscreteTopology ℕ] :
    (closure '' naturalSingletonCollection).LocallyFinite := by
  -- All singleton closures coincide with `univ`, so the image collection has one member.
  have hclosures : closure '' naturalSingletonCollection = ({Set.univ} : Set (Set ℕ)) := by
    ext A
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨n, rfl⟩ := hs
      rw [closure_eq_univ_of_nonempty_of_indiscrete (Set.singleton_nonempty n)]
      exact Set.mem_singleton Set.univ
    · intro hA
      rw [Set.mem_singleton_iff] at hA
      subst A
      refine ⟨{0}, ?_, closure_eq_univ_of_nonempty_of_indiscrete (Set.singleton_nonempty 0)⟩
      exact ⟨0, rfl⟩
  rw [hclosures, Set.locallyFinite_iff]
  intro x
  -- The universal neighborhood meets at most the sole member of the normalized collection.
  refine ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton Set.univ).subset ?_⟩
  intro A hA
  exact hA.1

/-- Exercise 39.3: On indiscrete `ℕ`, the singleton collection is not locally finite, but the
collection of closures of its members is locally finite. -/
theorem naturalSingletonCollection_spec [TopologicalSpace ℕ] [IndiscreteTopology ℕ] :
    ¬ naturalSingletonCollection.LocallyFinite ∧
      (closure '' naturalSingletonCollection).LocallyFinite :=
  ⟨not_locallyFinite_naturalSingletonCollection,
    locallyFinite_closure_naturalSingletonCollection⟩
