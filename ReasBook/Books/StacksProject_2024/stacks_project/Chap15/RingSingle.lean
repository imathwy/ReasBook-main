import Mathlib

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The canonical degree-zero derived object `R[0]` in `D(R)`. -/
abbrev ringSingle : DMod :=
  (single₀).obj (ModuleCat.of R R)

end

end CategoryTheory
