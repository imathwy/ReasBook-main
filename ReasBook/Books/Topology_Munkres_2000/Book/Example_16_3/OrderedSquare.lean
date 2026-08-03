module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UnitInterval

public section

/-- The unit square equipped with the lexicographic order. Its intrinsic order topology is
`Preorder.topology LexUnitSquare`. -/
abbrev LexUnitSquare := Set.Icc (0 : ℝ) 1 ×ₗ Set.Icc (0 : ℝ) 1

/-- The ordered square: `unitInterval × unitInterval` with the lexicographic order topology. -/
@[expose]
def OrderedSquare := LexUnitSquare

/-- Standard notation for the ordered square. -/
notation "Iₒ²" => OrderedSquare

namespace OrderedSquare

/-- The carrier equivalence from the ordered square to its coordinate product. -/
def toProd : Iₒ² ≃ unitInterval × unitInterval := Equiv.refl _

/-- The lexicographic linear order on the ordered square. -/
noncomputable instance instLinearOrder : LinearOrder Iₒ² :=
  inferInstanceAs (LinearOrder (Lex (unitInterval × unitInterval)))

/-- The ordered square has more than one point. -/
instance instNontrivial : Nontrivial Iₒ² :=
  inferInstanceAs (Nontrivial (Lex (unitInterval × unitInterval)))

/-- The order topology on the ordered square. -/
noncomputable instance instTopologicalSpace : TopologicalSpace Iₒ² :=
  Preorder.topology Iₒ²

/-- The topology on `Iₒ²` is its order topology. -/
instance instOrderTopology : OrderTopology Iₒ² := ⟨rfl⟩

end OrderedSquare
