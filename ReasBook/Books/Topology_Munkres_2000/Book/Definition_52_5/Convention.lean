module

public import Topology_Munkres_2000.Book.Definition_52_4.FundamentalGroup
public import Topology_Munkres_2000.Book.Notation_52_3.InducedMap

@[expose] public section

universe u v

namespace FundamentalGroup.LeftToRight

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x₀ x₁ : X} {y₀ : Y}

/-- The homomorphism induced by a pointed continuous map, in left-to-right convention. -/
noncomputable abbrev mapOfEq (f : C(X, Y)) (h : f x₀ = y₀) :
    π₁(X, x₀) →* π₁(Y, y₀) :=
  MonoidHom.op (FundamentalGroup.mapOfEq f h)

/-- Basepoint change along a path, in left-to-right convention. -/
noncomputable abbrev mulEquivOfPath (p : Path x₀ x₁) :
    π₁(X, x₀) ≃* π₁(X, x₁) :=
  MulEquiv.op (FundamentalGroup.fundamentalGroupMulEquivOfPath p)

/-- Basepoint change in a path-connected space, in left-to-right convention. -/
noncomputable abbrev mulEquivOfPathConnected [PathConnectedSpace X] (x₀ x₁ : X) :
    π₁(X, x₀) ≃* π₁(X, x₁) :=
  MulEquiv.op (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x₀ x₁)

@[simp] theorem mapOfEq_apply (f : C(X, Y)) (h : f x₀ = y₀)
    (p : π₁(X, x₀)) :
    mapOfEq f h p =
      .op ((Path.Homotopic.Quotient.map p.unop f).cast h.symm h.symm) := by
  rw [show mapOfEq f h p = .op (FundamentalGroup.mapOfEq f h p.unop) from rfl]
  rw [FundamentalGroup.mapOfEq_apply]

/-- Basepoint change along `α` sends a loop class `p` to the class of
`α.symm.trans (p.trans α)`. -/
theorem toPath_mulEquivOfPath_apply (α : Path x₀ x₁) (p : π₁(X, x₀)) :
    toPath (mulEquivOfPath α p) =
      (Path.Homotopic.Quotient.mk α).symm.trans
        ((toPath p).trans (Path.Homotopic.Quotient.mk α)) := rfl

end FundamentalGroup.LeftToRight
