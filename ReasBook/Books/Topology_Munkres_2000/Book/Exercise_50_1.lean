module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Mathlib.Topology.Order

public section

open scoped CoveringDimension

universe u

namespace DiscreteTopology

/-- Helper for Exercise 50.1: the family of singleton subsets has point multiplicity
at most one. -/
private lemma singletonCover_hasOrderLE_one (X : Type u) :
    (Set.range (Set.singleton : X → Set X)).HasOrderLE 1 := by
  -- Two singleton members containing the same point must be the same set.
  rw [Set.hasOrderLE_iff]
  intro x
  apply Set.encard_le_one_iff_subsingleton.mpr
  intro U hU V hV
  obtain ⟨u, rfl⟩ := hU.1
  obtain ⟨v, rfl⟩ := hV.1
  exact congrArg Set.singleton
    ((Set.mem_singleton_iff.mp hU.2).symm.trans (Set.mem_singleton_iff.mp hV.2))

/-- Helper for Exercise 50.1: in a discrete space, the singleton cover openly
refines every collection that covers the whole space. -/
private lemma singletonCover_isOpenRefinement {X : Type u} [TopologicalSpace X]
    [DiscreteTopology X] {𝒜 : Set (Set X)} (hcover : ⋃₀ 𝒜 = Set.univ) :
    IsOpenRefinement (Set.range (Set.singleton : X → Set X)) 𝒜 := by
  -- Choose a member of the original cover containing the singleton's point.
  rw [isOpenRefinement_iff, isRefinement_iff]
  constructor
  · intro B hB
    obtain ⟨x, rfl⟩ := hB
    obtain ⟨A, hA, hxA⟩ := Set.sUnion_eq_univ_iff.mp hcover x
    exact ⟨A, hA, Set.singleton_subset_iff.mpr hxA⟩
  · intro B _
    -- Discreteness makes every member of the singleton family open.
    exact isOpen_discrete B

/-- Exercise 50.1. Every discrete space has covering dimension at most zero. -/
theorem hasCoveringDimensionLE_zero (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] : HasCoveringDimensionLE X 0 := by
  -- Use all singleton subsets as the required multiplicity-one refinement.
  rw [hasCoveringDimensionLE_iff]
  intro 𝒜 _ hcover
  refine ⟨Set.range (Set.singleton : X → Set X),
    singletonCover_isOpenRefinement hcover, ?_, ?_⟩
  · -- Every point lies in its own singleton, so this family covers the space.
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      exact Set.mem_sUnion_of_mem (Set.mem_singleton x) ⟨x, rfl⟩
  · -- Its order is at most `0 + 1 = 1` by the multiplicity helper.
    simpa only [Nat.zero_add] using singletonCover_hasOrderLE_one X

/-- Every discrete space has numerical covering dimension at most zero. -/
theorem coveringDimension_le_zero (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] : dim X ≤ 0 := by
  -- Transport the open-cover bound through the numerical characterization.
  exact (coveringDimension_le_iff X 0).mpr (hasCoveringDimensionLE_zero X)

/-- Under the convention `dim ∅ = ⊥`, every nonempty discrete space has numerical
covering dimension zero. -/
theorem coveringDimension_eq_zero (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] [Nonempty X] : dim X = 0 := by
  -- Combine the upper bound with nonemptiness, which excludes dimension `⊥`.
  apply le_antisymm
  · exact coveringDimension_le_zero X
  · apply le_of_not_gt
    intro hnegative
    have hbot : dim X = ⊥ :=
      (WithBot.lt_zero_iff_eq_bot (dim X)).mp hnegative
    have hempty : IsEmpty X := (coveringDimension_eq_bot_iff X).mp hbot
    exact not_isEmpty_of_nonempty X hempty

end DiscreteTopology
