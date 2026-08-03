module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

universe u v

open Path.Homotopic.Quotient

namespace CircleWedge

/-- The ambient fundamental-group class represented by a loop in one component
of a family of subspaces with common basepoint. -/
noncomputable def includedLoopClass {ι : Type v} {X : Type u} [TopologicalSpace X]
    (S : ι → Set X) (p : X) (i : ι) {hp : p ∈ S i}
    (f : Path (⟨p, hp⟩ : S i) ⟨p, hp⟩) : FundamentalGroup X p :=
  FundamentalGroup.mapOfEq ⟨Subtype.val, continuous_subtype_val⟩ rfl
    (FundamentalGroup.fromPath (mk f))

end CircleWedge
