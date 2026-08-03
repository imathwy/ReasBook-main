module

public import Topology_Munkres_2000.Book.Definition_17_5

/- Definition 17.6: A topological space satisfies the `T₁` axiom if every
finite set of points is closed. Mathlib uses the equivalent condition that
every singleton is closed, expressed by `T1Space`. -/
#check T1Space

-- In a `T1Space`, every finite set of points is closed.
#check Set.Finite.isClosed

public section

universe u

/-- A topological space satisfies the `T₁` axiom exactly when every finite set is closed. -/
theorem t1Space_iff_finite_isClosed (X : Type u) [TopologicalSpace X] :
    T1Space X ↔ ∀ s : Set X, s.Finite → IsClosed s := by
  constructor
  · intro h s hs
    exact Set.Finite.induction_on s hs isClosed_empty fun {x s} _ _ h_closed ↦ by
      simpa only [Set.singleton_union] using (h.t1 x).union h_closed
  · intro h
    exact ⟨fun x ↦ h {x} (Set.finite_singleton x)⟩
