module

public import Topology_Munkres_2000.Book.Definition_52_6.BasepointChange

@[expose] public section

universe u

namespace FundamentalGroup.LeftToRight

variable {X : Type u} [TopologicalSpace X] {x₀ x₁ : X}

/- Theorem 52.1. For a path `α : Path x₀ x₁`, the basepoint-change map `α̂` is the
bundled group isomorphism
`π₁(X, x₀) ≃* π₁(X, x₁)`. -/
#check FundamentalGroup.LeftToRight.mulEquivOfPath

/-- The canonical basepoint-change isomorphism acts by the previously defined map `α̂`. -/
@[simp] theorem mulEquivOfPath_apply (α : Path x₀ x₁) (p : π₁(X, x₀)) :
    mulEquivOfPath α p = α̂ p := rfl

end FundamentalGroup.LeftToRight
