module

public import Mathlib.Order.Interval.Set.OrdConnected

/- Definition 16.4: A subset of an ordered set is convex when it contains the
open interval `Set.Ioo a b` between each pair of its points `a < b`; intervals
and rays are convex. -/
#check Set.OrdConnected

/-- The canonical order-connectedness predicate is equivalent to the textbook
open-interval definition of convexity. -/
public theorem Set.ordConnected_iff_Ioo {α : Type*} [PartialOrder α] {s : Set α} :
    s.OrdConnected ↔ ∀ a ∈ s, ∀ b ∈ s, a < b → Set.Ioo a b ⊆ s := by
  constructor
  · intro hs a ha b hb _
    exact Set.Ioo_subset_Icc_self.trans (hs.out ha hb)
  · exact Set.ordConnected_of_Ioo

-- Open intervals and open right rays are canonically order-convex; the other
-- standard intervals and rays are supplied by the same canonical API.
#check Set.ordConnected_Ioo
#check Set.ordConnected_Ioi
