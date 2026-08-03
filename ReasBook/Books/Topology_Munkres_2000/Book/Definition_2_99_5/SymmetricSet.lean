module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic

public section

universe u

open scoped Pointwise

namespace Set

variable {G : Type u} [Group G]

/-- A subset of a group is symmetric when it is fixed by pointwise inversion. -/
def IsSymmetric (V : Set G) : Prop :=
  V = V⁻¹

/-- A subset is symmetric exactly when it equals its pointwise inverse. -/
theorem isSymmetric_iff {V : Set G} : V.IsSymmetric ↔ V = V⁻¹ :=
  Iff.rfl

namespace IsSymmetric

/-- The pointwise inverse of a symmetric subset equals the subset. -/
theorem inv_eq {V : Set G} (hV : V.IsSymmetric) : V⁻¹ = V :=
  hV.symm

/-- The pointwise inverse of a symmetric subset is symmetric. -/
theorem inv {V : Set G} (hV : V.IsSymmetric) : (V⁻¹).IsSymmetric := by
  change V⁻¹ = (V⁻¹)⁻¹
  rw [inv_inv]
  exact hV.symm

/-- Membership in a symmetric subset is invariant under inversion. -/
theorem mem_inv_iff {V : Set G} (hV : V.IsSymmetric) {x : G} :
    x⁻¹ ∈ V ↔ x ∈ V := by
  constructor
  · intro hx
    rw [hV] at hx
    exact inv_mem_inv.mp hx
  · intro hx
    rw [hV]
    exact inv_mem_inv.mpr hx

end IsSymmetric

end Set
