module

public import Topology_Munkres_2000.Book.Definition_4_5.LinearContinuum
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.IntermediateValue

universe u

public section

namespace LinearContinuum

/-- Helper for Exercise 24.4: the points that are not upper bounds form an open set. -/
private lemma isOpen_compl_upperBounds {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {s : Set X} :
    IsOpen (upperBounds s)ᶜ := by
  -- A non-upper-bound lies below some member of the original set.
  refine isOpen_iff_forall_mem_open.2 ?_
  intro a ha
  rw [Set.mem_compl_iff, mem_upperBounds] at ha
  push Not at ha
  obtain ⟨x, hxs, hax⟩ := ha
  -- The ray below that member remains outside the upper-bound set.
  refine ⟨Set.Iio x, ?_, isOpen_Iio, hax⟩
  intro y hy hyUpper
  exact (not_le_of_gt hy) (hyUpper hxs)

/-- Helper for Exercise 24.4: without a least upper bound, the upper bounds form an open set. -/
private lemma isOpen_upperBounds_of_no_isLUB {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {s : Set X}
    (hNoLUB : ¬ ∃ a, IsLUB s a) : IsOpen (upperBounds s) := by
  -- Every upper bound has a strictly smaller upper bound.
  refine isOpen_iff_forall_mem_open.2 ?_
  intro b hb
  have hNotLower : b ∉ lowerBounds (upperBounds s) := by
    intro hbLower
    exact hNoLUB ⟨b, hb, hbLower⟩
  rw [mem_lowerBounds] at hNotLower
  push Not at hNotLower
  obtain ⟨c, hc, hcb⟩ := hNotLower
  -- The ray above the smaller upper bound stays among the upper bounds.
  refine ⟨Set.Ioi c, ?_, isOpen_Ioi, hcb⟩
  intro y hy
  exact upperBounds_mono_mem (le_of_lt hy) hc

/-- Helper for Exercise 24.4: a preconnected ordered space has least upper bounds. -/
private lemma exists_isLUB_of_preconnectedSpace {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [PreconnectedSpace X]
    (s : Set X) (hs : s.Nonempty) (hb : BddAbove s) : ∃ a, IsLUB s a := by
  classical
  -- If no least upper bound existed, the upper bounds and their complement would separate `X`.
  by_contra hNoLUB
  have hOpenCompl : IsOpen (upperBounds s)ᶜ := isOpen_compl_upperBounds
  have hOpenUpper : IsOpen (upperBounds s) :=
    isOpen_upperBounds_of_no_isLUB hNoLUB
  obtain ⟨b, hb⟩ := hb
  obtain ⟨x, hxs⟩ := hs
  have hxNotUpper : x ∉ upperBounds s := by
    intro hxUpper
    have hxLUB : IsLUB s x := by
      constructor
      · exact hxUpper
      · intro c hc
        exact hc hxs
    exact hNoLUB ⟨x, hxLUB⟩
  have hDisjoint : Disjoint (upperBounds s)ᶜ (upperBounds s) := disjoint_compl_left
  have hCover : (Set.univ : Set X) ⊆ (upperBounds s)ᶜ ∪ upperBounds s := by
    intro y hy
    simp
  -- Preconnectedness forces all points onto one side, contradicting a witness on the other side.
  obtain hAllCompl | hAllUpper :=
    isPreconnected_univ.subset_or_subset hOpenCompl hOpenUpper hDisjoint hCover
  · exact (hAllCompl (Set.mem_univ b)) hb
  · exact hxNotUpper (hAllUpper (Set.mem_univ x))

/-- Helper for Exercise 24.4: preconnected order topology supplies the LUB property. -/
private lemma leastUpperBoundPropertyOfPreconnectedOrderTopology (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [PreconnectedSpace X] :
    LeastUpperBoundProperty X := by
  -- Package the cut argument in the canonical least-upper-bound-property constructor.
  refine LeastUpperBoundProperty.of_exists_isLUB ?_
  intro s hs hb
  exact exists_isLUB_of_preconnectedSpace s hs hb

/-- Exercise 24.4: A connected linearly ordered space with its order topology is a linear
continuum. -/
theorem ofConnectedOrderTopology (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [ConnectedSpace X] :
    LinearContinuum X where
  toDenselyOrdered := denselyOrdered_of_preconnectedSpace
  -- Connectedness supplies preconnectedness, so the cut argument gives completeness.
  leastUpperBoundProperty := leastUpperBoundPropertyOfPreconnectedOrderTopology X

end LinearContinuum
