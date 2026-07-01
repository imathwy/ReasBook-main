import Mathlib
import Serre.LinearAlgebra.TensorPower.Symmetric

noncomputable section

open scoped TensorProduct

universe u v

namespace Representation

section SymmetricPower

variable {k : Type} [CommRing k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- The `n`th symmetric-power representation obtained by functoriality of symmetric tensor
powers. -/
def nthSymmetricPower (ρ : Representation k G V) (n : ℕ) :
    Representation k G (Sym[k]^n V) where
  toFun := fun g ↦ SymmetricPower.map n (ρ g)
  map_one' := by
    calc
      SymmetricPower.map n (ρ 1) = SymmetricPower.map n (1 : V →ₗ[k] V) := by
        rw [ρ.map_one]
      _ = SymmetricPower.map n (LinearMap.id : V →ₗ[k] V) := rfl
      _ = LinearMap.id := SymmetricPower.map_id n
      _ = 1 := rfl
  map_mul' g h := by
    calc
      SymmetricPower.map n (ρ (g * h)) = SymmetricPower.map n (ρ g * ρ h) := by
        rw [ρ.map_mul]
      _ = SymmetricPower.map n ((ρ g).comp (ρ h)) := rfl
      _ = (SymmetricPower.map n (ρ g)).comp (SymmetricPower.map n (ρ h)) :=
        SymmetricPower.map_comp n (ρ h) (ρ g)
      _ = SymmetricPower.map n (ρ g) * SymmetricPower.map n (ρ h) := rfl

end SymmetricPower

section ExteriorPower

variable {k : Type} [CommRing k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- The `n`th exterior-power representation obtained by functoriality of exterior powers. -/
def nthExteriorPower (ρ : Representation k G V) (n : ℕ) :
    Representation k G (⋀[k]^n V) where
  toFun := fun g ↦ exteriorPower.map n (ρ g)
  map_one' := by
    calc
      exteriorPower.map n (ρ 1) = exteriorPower.map n (1 : V →ₗ[k] V) := by
        rw [ρ.map_one]
      _ = exteriorPower.map n (LinearMap.id : V →ₗ[k] V) := rfl
      _ = LinearMap.id := by
        exact
          (exteriorPower.map_id :
            exteriorPower.map n (LinearMap.id : V →ₗ[k] V) = LinearMap.id)
      _ = 1 := rfl
  map_mul' g h := by
    calc
      exteriorPower.map n (ρ (g * h)) = exteriorPower.map n (ρ g * ρ h) := by
        rw [ρ.map_mul]
      _ = exteriorPower.map n ((ρ g).comp (ρ h)) := rfl
      _ = (exteriorPower.map n (ρ g)).comp (exteriorPower.map n (ρ h)) := by
        exact
          (exteriorPower.map_comp (ρ h) (ρ g) :
            exteriorPower.map n ((ρ g).comp (ρ h)) =
              (exteriorPower.map n (ρ g)).comp (exteriorPower.map n (ρ h)))
      _ = exteriorPower.map n (ρ g) * exteriorPower.map n (ρ h) := rfl

end ExteriorPower

end Representation
