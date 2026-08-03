module

public import Mathlib.Topology.Perfect

public section

universe u

/-- A point is isolated when its singleton is open. -/
def IsIsolated {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  IsOpen {x}

/-- A point is isolated exactly when its singleton is open. -/
theorem isIsolated_iff_isOpen_singleton {X : Type u} [TopologicalSpace X]
    {x : X} : IsIsolated x ↔ IsOpen {x} :=
  Iff.rfl

/-- A point is isolated exactly when its neighborhood filter is pure. -/
theorem isIsolated_iff_nhds_eq_pure {X : Type u} [TopologicalSpace X]
    {x : X} : IsIsolated x ↔ nhds x = pure x :=
  isOpen_singleton_iff_nhds_eq_pure x

/-- A point is isolated exactly when its punctured neighborhood filter is bottom. -/
theorem isIsolated_iff_punctured_nhds_eq_bot {X : Type u} [TopologicalSpace X]
    {x : X} : IsIsolated x ↔ nhdsWithin x {x}ᶜ = ⊥ :=
  isOpen_singleton_iff_punctured_nhds x

/-- A space is perfect exactly when none of its points are isolated. -/
theorem perfectSpace_iff_no_isolated_points {X : Type u} [TopologicalSpace X] :
    PerfectSpace X ↔ ∀ x : X, ¬ IsIsolated x := by
  rw [perfectSpace_iff_forall_not_isolated]
  simp only [isIsolated_iff_punctured_nhds_eq_bot, Filter.neBot_iff]
