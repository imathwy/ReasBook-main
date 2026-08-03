module

public import Mathlib.Topology.Order

public section

/- Definition 22.1: A surjective map `p : X → Y` is a quotient map when a set
`U : Set Y` is open exactly when its preimage `p ⁻¹' U` is open. This is
mathlib's `Topology.IsQuotientMap`. -/
#check Topology.IsQuotientMap

namespace Topology

/-- The source-facing open-set characterization of a quotient map. -/
theorem isQuotientMap_iff_isOpen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) :
    IsQuotientMap p ↔
      Function.Surjective p ∧ ∀ U : Set Y, IsOpen U ↔ IsOpen (p ⁻¹' U) := by
  constructor
  · intro hp
    refine ⟨hp.surjective, fun U ↦ ?_⟩
    rw [hp.isCoinducing.eq_coinduced]
    rfl
  · rintro ⟨hp, hopen⟩
    refine ⟨⟨?_⟩, hp⟩
    apply TopologicalSpace.ext
    funext U
    exact propext (hopen U)

end Topology

end
