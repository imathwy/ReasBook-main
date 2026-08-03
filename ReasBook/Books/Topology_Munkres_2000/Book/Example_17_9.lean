module

public import Topology_Munkres_2000.Book.Example_12_1.ThreePointTopology

public section

open ThreePointTopology
open scoped Topology

/-- Helper for Example 17.9: The complement of `{b}` is not open in the topology
shown in Figure 17.3. -/
theorem ThreePointTopology.not_isOpen_compl_singleton_b :
    ¬ IsOpen[topology .bAndABAndBC] ({.b} : Set ThreePoint)ᶜ := by
  -- Rewrite openness into the displayed family, then compute that `{a, c}` is not listed.
  intro hOpen
  have hListed : ({.b} : Set ThreePoint)ᶜ ∈ openSets .bAndABAndBC :=
    (isOpen_iff .bAndABAndBC _).mp hOpen
  -- The branch characterization reduces the claim to impossible finite-set equalities.
  rw [mem_openSets_bAndABAndBC_iff] at hListed
  rcases hListed with hEmpty | hSingleton | hAB | hBC | hUniv
  · -- The complement contains `a`, so it is not empty.
    have hMembership := congrArg (fun s : Set ThreePoint => ThreePoint.a ∈ s) hEmpty
    simp at hMembership
  · -- The complement of `{b}` cannot equal `{b}` because it omits `b`.
    have hMembership := congrArg (fun s : Set ThreePoint => ThreePoint.b ∈ s) hSingleton
    simp at hMembership
  · -- The complement cannot equal `{a, b}` because the latter contains `b`.
    have hMembership := congrArg (fun s : Set ThreePoint => ThreePoint.b ∈ s) hAB
    simp at hMembership
  · -- The complement cannot equal `{b, c}` for the same membership reason.
    have hMembership := congrArg (fun s : Set ThreePoint => ThreePoint.b ∈ s) hBC
    simp at hMembership
  · -- The complement is not universal because it omits `b`.
    have hMembership := congrArg (fun s : Set ThreePoint => ThreePoint.b ∈ s) hUniv
    simp at hMembership

/-- Example 17.9: In the particular-point topology on `{a, b, c}`, the singleton
`{b}` is not closed. -/
theorem ThreePointTopology.not_isClosed_singleton_b :
    ¬ IsClosed[topology .bAndABAndBC] ({.b} : Set ThreePoint) := by
  -- Closedness would make the complement open, contradicting the displayed list.
  simpa only [isOpen_compl_iff] using not_isOpen_compl_singleton_b
