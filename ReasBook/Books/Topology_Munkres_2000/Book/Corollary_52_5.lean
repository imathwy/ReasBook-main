module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention
public import Topology_Munkres_2000.Book.Definition_9_0_2

public section

universe u v

namespace FundamentalGroup

namespace LeftToRight

open Path.Homotopic.Quotient

/-- Corollary 52.5. A homeomorphism `h : X ≃ₜ Y` carrying `x₀` to `y₀`
induces an isomorphism from `π₁(X, x₀)` to `π₁(Y, y₀)`. -/
@[expose] noncomputable def mulEquivOfHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) (x₀ : X) (y₀ : Y)
    (hxy : h x₀ = y₀) :
    π₁(X, x₀) ≃* π₁(Y, y₀) :=
  (MulEquiv.op (h.fundamentalGroupMulEquiv x₀)).trans
    (MulEquiv.cast hxy : π₁(Y, h x₀) ≃* π₁(Y, y₀))

/-- The forward homomorphism of `mulEquivOfHomeomorph` is the map induced by the
pointed homeomorphism. -/
@[simp] theorem mulEquivOfHomeomorph_toMonoidHom {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) (x₀ : X) (y₀ : Y)
    (hxy : h x₀ = y₀) :
    (mulEquivOfHomeomorph h x₀ y₀ hxy).toMonoidHom =
      mapOfEq (h : C(X, Y)) hxy := by
  ext p
  cases hxy
  simp only [mulEquivOfHomeomorph]
  change MulOpposite.op (h.fundamentalGroupMulEquiv x₀ p.unop) = _
  rw [h.fundamentalGroupMulEquiv_apply]
  change MulOpposite.op (FundamentalGroup.map (h : C(X, Y)) x₀ p.unop) = _
  rw [mapOfEq_apply, FundamentalGroup.map_apply, cast_rfl_rfl]

/-- The homomorphism induced by a pointed homeomorphism is bijective. -/
theorem mapOfEq_bijective {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (x₀ : X) (y₀ : Y) (hxy : h x₀ = y₀) :
    Function.Bijective (mapOfEq (h : C(X, Y)) hxy) := by
  rw [← mulEquivOfHomeomorph_toMonoidHom]
  exact (mulEquivOfHomeomorph h x₀ y₀ hxy).bijective

end LeftToRight

end FundamentalGroup

end
