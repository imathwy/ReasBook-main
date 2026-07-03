import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G]

/- Definition 1-1.2-1: a degree-1 complex representation of a group `G` is the canonical type
`G →* ℂˣ` of group homomorphisms from `G` to the multiplicative group of nonzero complex numbers. -/
#check (G →* ℂˣ)

namespace MonoidHom

/-- A degree-1 complex character canonically yields a one-dimensional complex representation. -/
def toRepresentation (ρ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := LinearMap.lsmul ℂ ℂ (ρ g : ℂ)
  map_one' := by
    apply LinearMap.ext
    intro z
    simp [LinearMap.lsmul_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    simp [LinearMap.lsmul_apply, mul_assoc]

@[simp] theorem toRepresentation_character_apply (ρ : G →* ℂˣ) (g : G) :
    ρ.toRepresentation.character g = (ρ g : ℂ) := by
  rw [Representation.character]
  have hρg :
      ρ.toRepresentation g = (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (ρ g : ℂ) := by
    apply LinearMap.ext
    intro z
    simp [MonoidHom.toRepresentation, LinearMap.lsmul_apply, mul_comm]
  rw [hρg]
  exact LinearMap.trace_smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (ρ g : ℂ)

end MonoidHom

/-- The value of a degree-1 complex representation at `s` lies in
`rootsOfUnity (orderOf s) ℂ`. -/
theorem degree_one_representation_value_mem_rootsOfUnity (ρ : G →* ℂˣ) (s : G) :
    ρ s ∈ rootsOfUnity (orderOf s) ℂ := by
  rw [mem_rootsOfUnity, ← map_pow, pow_orderOf_eq_one, map_one]

/-- A degree-1 complex representation takes every finite-order element to the unit circle. -/
theorem degree_one_representation_norm_eq_one (ρ : G →* ℂˣ) (s : G) (hs : IsOfFinOrder s) :
    ‖(ρ s : ℂ)‖ = 1 := by
  exact (Units.isOfFinOrder_val.mpr <| ρ.isOfFinOrder hs).norm_eq_one

end
