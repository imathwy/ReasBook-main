import Mathlib.Topology.Homotopy.HomotopyGroup

universe u

noncomputable section

namespace HomotopyGroup

/-- Multiplicative form of the canonical `π₁`/fundamental-group bridge. The underlying map is
`HomotopyGroup.pi1EquivFundamentalGroup`; only multiplicativity remains proof-shaped. -/
def pi1MulEquivFundamentalGroup {X : Type u} [TopologicalSpace X] (x : X) :
    HomotopyGroup.Pi 1 X x ≃* FundamentalGroup X x where
  toEquiv := HomotopyGroup.pi1EquivFundamentalGroup
  map_mul' := by
    sorry

end HomotopyGroup
