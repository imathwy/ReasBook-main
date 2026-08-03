module

public import Mathlib.Data.Set.Image

public section

universe u v

namespace Set

variable {X : Type u} {Y : Type v}

/-- Definition 22.2: A subset is saturated with respect to a map when it contains every
fiber that it intersects, equivalently when it is the complete preimage of a subset of the
codomain. The source assumes that the map is surjective, but neither characterization needs
that hypothesis. -/
def IsSaturated (p : X → Y) (C : Set X) : Prop :=
  p ⁻¹' (p '' C) = C

/-- The defining fixed-point equation for a saturated set. -/
theorem isSaturated_iff_preimage_image {p : X → Y} {C : Set X} :
    IsSaturated p C ↔ p ⁻¹' (p '' C) = C := by
  -- The displayed equation is exactly the definition of saturation.
  rfl

/-- Saturation means that membership is constant along fibers of the map. -/
theorem isSaturated_iff_mem_of_eq {p : X → Y} {C : Set X} :
    IsSaturated p C ↔
      ∀ ⦃x x' : X⦄, x ∈ C → p x' = p x → x' ∈ C := by
  constructor
  · intro hSaturated x x' hx hFiber
    -- The point `x` witnesses that `x'` lies in the preimage of the image of `C`.
    have hx' : x' ∈ p ⁻¹' (p '' C) := ⟨x, hx, hFiber.symm⟩
    rw [hSaturated] at hx'
    exact hx'
  · intro hFiber
    rw [isSaturated_iff_preimage_image]
    ext x
    constructor
    · rintro ⟨z, hz, hImage⟩
      -- Fiberwise closure moves membership from the image witness `z` to `x`.
      exact hFiber hz hImage.symm
    · intro hx
      -- Every member of `C` supplies its own image witness.
      exact ⟨x, hx, rfl⟩

/-- A set is saturated exactly when it is the full preimage of a set in the codomain. -/
theorem isSaturated_iff_exists_preimage {p : X → Y} {C : Set X} :
    IsSaturated p C ↔ ∃ D : Set Y, C = p ⁻¹' D := by
  constructor
  · intro hSaturated
    -- A saturated set is the full preimage of its own image.
    exact ⟨p '' C, hSaturated.symm⟩
  · rintro ⟨D, hC⟩
    rw [isSaturated_iff_mem_of_eq]
    intro x x' hx hFiber
    -- Membership in a preimage depends only on the common value in the codomain.
    rw [hC] at hx ⊢
    have hx' : p x' ∈ D := hFiber.symm ▸ hx
    exact hx'

/-- The preimage of every set is saturated. -/
theorem isSaturated_preimage (p : X → Y) (D : Set Y) :
    IsSaturated p (p ⁻¹' D) := by
  -- Use the complete-preimage characterization with the original codomain set.
  rw [isSaturated_iff_exists_preimage]
  exact ⟨D, rfl⟩

end Set


end
