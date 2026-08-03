module

public import Mathlib.Order.WellFounded

import Mathlib.Order.Bounds.Basic

public section

universe u

variable {A : Type u} [LinearOrder A]

/- Definition 10.1: A linearly ordered type is well ordered when every nonempty
subset has a least element. The canonical mathlib owner is `WellFoundedLT`. -/
#check (WellFoundedLT A)

/-- On a linear order, `WellFoundedLT` is equivalent to the textbook
least-element definition of a well-order. -/
theorem wellFoundedLT_iff_exists_isLeast :
    WellFoundedLT A ↔ ∀ s : Set A, s.Nonempty → ∃ m, IsLeast s m := by
  constructor
  · intro h s hs
    obtain ⟨m, hm⟩ := h.exists_minimal s hs
    exact ⟨m, minimal_iff_isLeast.mp hm⟩
  · intro h
    rw [WellFounded.wellFoundedLT_iff_exists_minimal]
    intro s hs
    obtain ⟨m, hm⟩ := h s hs
    exact ⟨m, minimal_iff_isLeast.mpr hm⟩
