module

public import Topology_Munkres_2000.Book.Example_12_1.ThreePointTopology

public section

open Set

/-- Helper for Remark 12.1: the collection in the left diagram of Figure 12.2. -/
def figure12_2Left : Set (Set ThreePointTopology.ThreePoint) :=
  {s | s = ∅ ∨ s = Set.univ ∨ s = {.a} ∨ s = {.b}}

/-- Helper for Remark 12.1: the collection in the right diagram of Figure 12.2. -/
def figure12_2Right : Set (Set ThreePointTopology.ThreePoint) :=
  {s | s = ∅ ∨ s = Set.univ ∨ s = {.a, .b} ∨ s = {.b, .c}}

/-- Remark 12.1 (1): The three-element set admits distinct topologies. -/
theorem threePoint_has_distinctTopologies :
    ThreePointTopology.topology .indiscrete ≠ ThreePointTopology.topology .discrete := by
  intro htopology
  -- The singleton `{a}` is one of the open sets in the displayed discrete topology.
  have hopenDiscrete :
      (ThreePointTopology.topology .discrete).IsOpen
        ({ThreePointTopology.ThreePoint.a} : Set ThreePointTopology.ThreePoint) := by
    rw [ThreePointTopology.isOpen_iff]
    exact (ThreePointTopology.mem_openSets_iff .discrete _).mpr True.intro
  -- Transporting openness across the alleged equality forces `{a}` into the indiscrete family.
  rw [← htopology] at hopenDiscrete
  have hlisted :=
    (ThreePointTopology.mem_openSets_iff .indiscrete _).mp
      ((ThreePointTopology.isOpen_iff .indiscrete _).mp hopenDiscrete)
  rcases hlisted with hempty | huniv
  · -- Membership of `a` distinguishes the singleton from the empty set.
    have ha := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.a ∈ s) hempty
    simp at ha
  · -- Membership of `b` distinguishes the singleton from the whole space.
    have hb := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.b ∈ s) huniv
    simp at hb

/-- Companion for Remark 12.1: the collection in the left diagram of Figure 12.2 is not a
topology. -/
theorem figure12_2Left_notTopology :
    ¬ ∃ t : TopologicalSpace ThreePointTopology.ThreePoint, t.IsOpen = figure12_2Left := by
  rintro ⟨t, ht⟩
  -- The alleged identification makes each of the two displayed singletons open.
  have hopenA : t.IsOpen ({.a} : Set ThreePointTopology.ThreePoint) := by
    rw [ht]
    exact Or.inr (Or.inr (Or.inl rfl))
  have hopenB : t.IsOpen ({.b} : Set ThreePointTopology.ThreePoint) := by
    rw [ht]
    exact Or.inr (Or.inr (Or.inr rfl))
  -- Arbitrary-union closure applies to the two-element family of these singletons.
  have hopenEach :
      ∀ s ∈ ({({.a} : Set ThreePointTopology.ThreePoint), {.b}} :
        Set (Set ThreePointTopology.ThreePoint)), t.IsOpen s := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hopenA
    · exact hopenB
  have hopenUnion :
      t.IsOpen (⋃₀ ({({.a} : Set ThreePointTopology.ThreePoint), {.b}} :
        Set (Set ThreePointTopology.ThreePoint))) :=
    t.isOpen_sUnion _ hopenEach
  have hopenPair : t.IsOpen ({.a, .b} : Set ThreePointTopology.ThreePoint) := by
    simpa only [Set.sUnion_pair, Set.singleton_union] using hopenUnion
  -- The explicit left family omits `{a, b}`; each listed alternative fails pointwise.
  rw [ht] at hopenPair
  rcases hopenPair with hempty | huniv | ha | hb
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.a ∈ s) hempty
    simp at hmem
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.c ∈ s) huniv
    simp at hmem
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.b ∈ s) ha
    simp at hmem
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.a ∈ s) hb
    simp at hmem

/-- Companion for Remark 12.1: the collection in the right diagram of Figure 12.2 is not a
topology. -/
theorem figure12_2Right_notTopology :
    ¬ ∃ t : TopologicalSpace ThreePointTopology.ThreePoint, t.IsOpen = figure12_2Right := by
  rintro ⟨t, ht⟩
  -- The alleged identification makes both overlapping displayed pairs open.
  have hopenAB : t.IsOpen ({.a, .b} : Set ThreePointTopology.ThreePoint) := by
    rw [ht]
    exact Or.inr (Or.inr (Or.inl rfl))
  have hopenBC : t.IsOpen ({.b, .c} : Set ThreePointTopology.ThreePoint) := by
    rw [ht]
    exact Or.inr (Or.inr (Or.inr rfl))
  -- Their intersection is exactly the singleton `{b}`.
  have hintersection :
      ({.a, .b} : Set ThreePointTopology.ThreePoint) ∩ {.b, .c} = {.b} := by
    ext x
    cases x
    · simp
    · simp
    · simp
  have hopenB : t.IsOpen ({.b} : Set ThreePointTopology.ThreePoint) := by
    rw [← hintersection]
    exact t.isOpen_inter _ _ hopenAB hopenBC
  -- The explicit right family omits `{b}`; each listed alternative fails pointwise.
  rw [ht] at hopenB
  rcases hopenB with hempty | huniv | hab | hbc
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.b ∈ s) hempty
    simp at hmem
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.a ∈ s) huniv
    simp at hmem
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.a ∈ s) hab
    simp at hmem
  · have hmem := congrArg
      (fun s : Set ThreePointTopology.ThreePoint => ThreePointTopology.ThreePoint.c ∈ s) hbc
    simp at hmem
