module

public import Topology_Munkres_2000.Book.Example_10_1.TwoCopiesPNat
public import Mathlib.Topology.Order.Basic

public section

namespace TwoCopiesPNat

/-- The order topology on the lexicographically ordered two copies of `ℕ+`. -/
noncomputable instance instTopologicalSpace : TopologicalSpace TwoCopiesPNat :=
  Preorder.topology TwoCopiesPNat

/-- The topology on `TwoCopiesPNat` is its order topology. -/
instance instOrderTopology : OrderTopology TwoCopiesPNat := ⟨rfl⟩

end TwoCopiesPNat
