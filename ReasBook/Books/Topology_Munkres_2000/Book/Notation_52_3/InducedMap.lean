module

public import Topology_Munkres_2000.Book.Definition_52_4.FundamentalGroup

@[expose] public section

universe u v

namespace FundamentalGroup.LeftToRight

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x₀ : X}

/-- The homomorphism induced by a continuous map at a specified basepoint, with
multiplication in left-to-right path order. -/
noncomputable abbrev map (f : C(X, Y)) (x : X) :
    π₁(X, x) →* π₁(Y, f x) :=
  MonoidHom.op (FundamentalGroup.map f x)

/-- Munkres's notation for the homomorphism induced at a specified basepoint. -/
notation:max "(" f:arg "₍" x:arg "₎)₊" => map f x

/-- The induced map sends a loop class to the class obtained by postcomposition. -/
@[simp] theorem map_apply (f : C(X, Y)) (p : π₁(X, x₀)) :
    (f₍x₀₎)₊ p = .op (FundamentalGroup.map f x₀ p.unop) := rfl

end FundamentalGroup.LeftToRight
