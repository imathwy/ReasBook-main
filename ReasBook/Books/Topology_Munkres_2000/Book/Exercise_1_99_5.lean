module

public import Topology_Munkres_2000.Book.Exercise_1_99_5.WellOrderedSubset

public section

open scoped WellOrderedSubset

universe u

/- Exercise 1.99.5: A well-ordered subset is a proper initial section of another
when it is the strict predecessor section of one of its elements. -/
#check WellOrderedSubset.isProperSection_iff

namespace WellOrderedSubset

/-- Companion for Exercise 1.99.5 (1): Proper initial-section inclusion is a strict
partial order on the collection of well-ordered subsets of a fixed ambient type. -/
instance instIsStrictOrder {X : Type u} :
    IsStrictOrder (WellOrderedSubset X) (· ≺ ·) := by
  -- Apply the strict-order laws proved from the proper-section characterization.
  exact isStrictOrder_isProperSection

/-- Exercise 1.99.5 (2): The literal unions of the carriers and relations in a chain
form a well-ordered set. -/
theorem chainUnion_isWellOrder {X : Type u} (C : Set (WellOrderedSubset X))
    (hC : IsChain (· ≺ ·) C) :
    IsWellOrder (unionCarrier C) (Subrel (unionRel C) (unionCarrier C)) := by
  -- Use the support theorem established from well-foundedness and trichotomy.
  exact chainUnionWellOrder C hC

end WellOrderedSubset
