module

import Mathlib.Order.Defs.Unbundled

public section

/-- Definition 3.8 (1): Comparability of distinct elements allows a distinct pair
to be related in both directions. -/
theorem comparabilityAllowsBothDirections :
    let C : Bool → Bool → Prop := fun _ _ ↦ True
    (∀ x y, x ≠ y → C x y ∨ C y x) ∧ C false true ∧ C true false := by
  dsimp
  exact ⟨fun _ _ _ ↦ Or.inl trivial, trivial, trivial⟩

/- Definition 3.8 (2): An irreflexive transitive relation is asymmetric. -/
#check asymm_of_isTrans_of_irrefl
