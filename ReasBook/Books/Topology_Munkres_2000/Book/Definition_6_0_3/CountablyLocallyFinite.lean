module

public import Topology_Munkres_2000.Book.Definition_6_0_2.SigmaLocallyFinite

public section

open Set

universe u

namespace Set

/-- A collection of subsets is countably locally finite if its inclusion family is
sigma-locally finite. -/
def CountablyLocallyFinite {X : Type u} [TopologicalSpace X] (𝓑 : Set (Set X)) : Prop :=
  SigmaLocallyFinite (Subtype.val : 𝓑 → Set X)

/-- A collection is countably locally finite exactly when it is a countable union of
locally finite subcollections. -/
theorem countablyLocallyFinite_iff {X : Type u} [TopologicalSpace X] {𝓑 : Set (Set X)} :
    𝓑.CountablyLocallyFinite ↔
      ∃ pieces : ℕ → Set (Set X),
        𝓑 = ⋃ n, pieces n ∧
          ∀ n, (pieces n).LocallyFinite :=
  sigmaLocallyFinite_subtype_iff

end Set
