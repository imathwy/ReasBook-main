import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {G : Type u} [Group G] {H : Set G}

-- Proof sketch: if `H` is the carrier of a subgroup, then it is nonempty because `1 ∈ H`, and
-- closure under `x * y⁻¹` follows from closure under multiplication and inversion. Conversely,
-- use `Subgroup.ofDiv H` to build the subgroup from the assumed nonemptiness and division
-- closure, then observe that its carrier is definitionally `H`.
/-- Proposition 1.1.27: a subset `H` of a group `G` is a subgroup exactly when it is nonempty and
closed under the operation `(x, y) ↦ x * y⁻¹`. -/
theorem set_is_subgroup_iff_nonempty_mul_inv_mem :
    (∃ K : Subgroup G, (K : Set G) = H) ↔ H.Nonempty ∧ ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H := by
  constructor
  · rintro ⟨K, rfl⟩
    refine ⟨K.coe_nonempty, ?_⟩
    intro x hx y hy
    exact K.mul_mem hx (K.inv_mem hy)
  · rintro ⟨hH, hmul_inv⟩
    exact ⟨Subgroup.ofDiv H hH hmul_inv, rfl⟩
