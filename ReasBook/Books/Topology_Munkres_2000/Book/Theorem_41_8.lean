module

public import Topology_Munkres_2000.Book.Theorem_41_8.Minorant

public section

universe u

open Set TopologicalSpace

/-- Theorem 41.8. For a locally finite collection of subsets of a paracompact
Hausdorff space, positive bounds on the members admit an everywhere-positive
continuous function bounded by each assigned value on the corresponding set. -/
theorem exists_continuousMap_pos_le_on_of_locallyFinite {X : Type u}
    [TopologicalSpace X] [ParacompactSpace X] [T2Space X] (𝒞 : Set (Set X))
    (ε : 𝒞 → ℝ) (hε : ∀ C, 0 < ε C)
    (h𝒞 : LocallyFinite (Subtype.val : 𝒞 → Set X)) :
    ∃ f : C(X, ℝ), (∀ x, 0 < f x) ∧ ∀ C : 𝒞, ∀ x ∈ C.val, f x ≤ ε C := by
  -- Apply the indexed-family minorant theorem to the subtype of members of the collection.
  exact h𝒞.exists_continuousMap_pos_le ε hε
