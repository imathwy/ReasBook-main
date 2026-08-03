module

public import Mathlib.GroupTheory.PresentedGroup

public section

namespace NonorientableSurfaceGroup

/-- The ordered word `α₀² * ⋯ * αₘ₋₁²` defining the standard nonorientable surface
presentation. -/
def relator (m : ℕ) : FreeGroup (Fin m) :=
  (List.ofFn fun i : Fin m ↦ (FreeGroup.of i) ^ 2).prod

/-- The explicit ordered-list formula defining `relator`. -/
theorem relator_def (m : ℕ) :
    relator m = (List.ofFn fun i : Fin m ↦ (FreeGroup.of i) ^ 2).prod := sorry

/-- The group with presentation `⟨α₀, …, αₘ₋₁ | α₀² * ⋯ * αₘ₋₁² = 1⟩`. -/
abbrev Presentation (m : ℕ) : Type :=
  PresentedGroup ({relator m} : Set (FreeGroup (Fin m)))

/-- The canonical generator indexed by `i : Fin m`. -/
def generator (m : ℕ) (i : Fin m) : Presentation m :=
  PresentedGroup.of i

/-- The canonical generator is the image of `i` in the presented group. -/
theorem generator_def (m : ℕ) (i : Fin m) :
    generator m i = PresentedGroup.of i := sorry

/-- The canonical generators satisfy the ordered product-of-squares relation. -/
theorem relation (m : ℕ) :
    (List.ofFn fun i : Fin m ↦ (generator m i) ^ 2).prod = 1 := sorry

end NonorientableSurfaceGroup
