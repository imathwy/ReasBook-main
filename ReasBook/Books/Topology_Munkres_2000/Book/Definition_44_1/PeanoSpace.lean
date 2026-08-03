module

public import Mathlib.Topology.UnitInterval

public section

universe u

/-- A Peano space is a Hausdorff space that is a continuous image of the closed unit
interval. -/
class PeanoSpace (X : Type u) [TopologicalSpace X] : Prop extends T2Space X where
  exists_surjective : ∃ f : C(unitInterval, X), Function.Surjective f

/-- A space is Peano exactly when it is Hausdorff and admits a continuous surjection
from the closed unit interval. -/
theorem peanoSpace_iff (X : Type u) [TopologicalSpace X] :
    PeanoSpace X ↔ T2Space X ∧ ∃ f : C(unitInterval, X), Function.Surjective f := by
  constructor
  · intro h
    exact ⟨h.toT2Space, h.exists_surjective⟩
  · rintro ⟨hT2, hf⟩
    exact { toT2Space := hT2, exists_surjective := hf }
