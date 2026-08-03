module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention

@[expose] public section

universe u

namespace FundamentalGroup.LeftToRight

variable {X : Type u} [TopologicalSpace X] {x₀ x₁ : X}

/-- The basepoint-change map induced by a path `α`, defined on loop classes by
`[f] ↦ [α⁻¹ * f * α]`. -/
noncomputable abbrev hat (α : Path x₀ x₁) : π₁(X, x₀) → π₁(X, x₁) :=
  fun p ↦ fromPath ((Path.Homotopic.Quotient.mk α).symm.trans
    ((toPath p).trans (Path.Homotopic.Quotient.mk α)))

postfix:max "̂" => hat

/-- The defining formula for the basepoint-change map `α̂`. -/
@[simp] theorem toPath_hat_apply (α : Path x₀ x₁) (p : π₁(X, x₀)) :
    toPath (α̂ p) = (Path.Homotopic.Quotient.mk α).symm.trans
      ((toPath p).trans (Path.Homotopic.Quotient.mk α)) := rfl

end FundamentalGroup.LeftToRight
