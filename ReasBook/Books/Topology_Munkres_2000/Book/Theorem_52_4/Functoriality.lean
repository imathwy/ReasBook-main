module

public import Topology_Munkres_2000.Book.Notation_52_3.InducedMap

public section

universe u v w

namespace FundamentalGroup.LeftToRight

open Path.Homotopic

/-- The homomorphism induced by a composite of continuous maps is the composite
of their induced homomorphisms. -/
@[simp] theorem map_comp {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (h : C(X, Y)) (k : C(Y, Z)) (x₀ : X) :
    ((k.comp h)₍x₀₎)₊ = (k₍(h x₀)₎)₊.comp (h₍x₀₎)₊ := by
  ext p
  simp only [map_apply]
  exact congrArg MulOpposite.op Quotient.map_comp

/-- The identity continuous map induces the identity homomorphism on the
fundamental group. -/
@[simp] theorem map_id {X : Type u} [TopologicalSpace X] (x₀ : X) :
    ((ContinuousMap.id X)₍x₀₎)₊ = MonoidHom.id π₁(X, x₀) := by
  ext p
  simp only [map_apply]
  rcases p with ⟨⟨p⟩⟩
  rfl

end FundamentalGroup.LeftToRight

end
