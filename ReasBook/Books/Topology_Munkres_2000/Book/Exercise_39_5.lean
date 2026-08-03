module

public import Topology_Munkres_2000.Book.Exercise_39_5.Countability

public section

universe u

/-- Exercise 39.5: In a second-countable space, a collection of subsets is
sigma-locally finite if and only if it is countable. -/
theorem countablyLocallyFinite_iff_countable {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (𝒜 : Set (Set X)) :
    𝒜.CountablyLocallyFinite ↔ 𝒜.Countable := by
  constructor
  · -- Second countability turns countable local finiteness into countability.
    exact Set.CountablyLocallyFinite.countable
  · -- A countable collection is the union of its singleton locally finite pieces.
    exact Set.Countable.countablyLocallyFinite
