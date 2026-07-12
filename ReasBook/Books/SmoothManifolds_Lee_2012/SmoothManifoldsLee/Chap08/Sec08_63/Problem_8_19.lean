import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note: this file lies in the cross-product/Lie-algebra interface. The owner
-- declarations checked before refinement were `crossProduct` and `Cross.lieRing` in
-- `Mathlib.LinearAlgebra.CrossProduct`, together with the generic `LieAlgebra` structure pattern
-- from `Mathlib.Algebra.Lie.Basic`. Primitive data is the cross-product Lie ring; the Lie algebra
-- structure is derived bridge/view API from the ambient `Module R (Fin 3 → R)`.

open scoped Matrix

namespace Cross

section

variable {R : Type*} [CommRing R]

local notation "R3" => Fin 3 → R

attribute [local instance] Cross.lieRing

/-- Problem 8-19, bridge/view layer: together with `Cross.lieRing`, the standard `R`-module
structure on `R^3` makes the cross product into a Lie algebra bracket. -/
instance lieAlgebra : LieAlgebra R R3 := by
  let _ : LieRing R3 := lieRing
  exact
    { (inferInstance : Module R R3) with
      lie_smul := fun t u v ↦ by
        change u ⨯₃ (t • v) = t • (u ⨯₃ v)
        exact (crossProduct u).map_smul t v }

attribute [local instance] lieAlgebra

/-- The bracket from `Cross.lieRing` on `R^3` is the usual cross product. -/
theorem lie_eq_cross (u v : R3) : ⁅u, v⁆ = u ⨯₃ v := rfl

end

end Cross
