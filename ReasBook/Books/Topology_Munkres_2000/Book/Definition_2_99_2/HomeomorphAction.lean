module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Topology.Homeomorph.Defs

public section

universe u

namespace Homeomorph

/-- The tautological action of self-homeomorphisms on a topological space. -/
instance applyMulAction (X : Type u) [TopologicalSpace X] : MulAction (X ≃ₜ X) X where
  smul e x := e x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action of a self-homeomorphism is evaluation. -/
@[simp]
protected theorem smul_def {X : Type u} [TopologicalSpace X] (e : X ≃ₜ X) (x : X) :
    e • x = e x := rfl

end Homeomorph
